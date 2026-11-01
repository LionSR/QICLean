#!/usr/bin/env python3
"""Source-only blueprint resolution regressions; no network or Lean artifacts."""

from __future__ import annotations

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

import blueprint_lean_sync as sync


class MathlibSourceResolutionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.package = self.root / ".lake/packages/mathlib"
        self.write("QICLean/Example.lean", "theorem Owner.shared : True := by trivial\n")
        self.chapter = self.write("blueprint/src/chapter/example.tex", "")
        self.environment = mock.patch.dict(
            os.environ, {"BLUEPRINT_SYNC_FETCH_DEPS": "0", "GITHUB_ACTIONS": "false"}
        )
        self.environment.start()
        self.addCleanup(self.environment.stop)

    def write(self, relative: str, content: str) -> Path:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def git(self, *args: str, cwd: Path | None = None) -> str:
        return subprocess.check_output(
            ["git", *args], cwd=cwd or self.package,
            stderr=subprocess.PIPE, text=True,
        ).strip()

    def manifest(self, rev: str, **overrides: object) -> None:
        entry = {
            "name": "mathlib", "type": "git", "rev": rev,
            "url": "https://github.com/leanprover-community/mathlib4.git",
            "inputRev": "moving-tag", "subDir": None,
        }
        entry.update(overrides)
        self.write("lake-manifest.json", json.dumps({
            "packagesDir": ".lake/packages", "packages": [entry],
        }))

    def dependency(self) -> str:
        # Deliberately small parser fixtures with the real upstream names and
        # namespace forms used by QICLean; these are not Lean proof tests.
        self.write(".lake/packages/mathlib/Mathlib/Example.lean", "\n".join([
            "module",
            "public theorem Continuous.matrix_trace : True := by trivial",
            "theorem continuous_pow : True := by trivial",
            "namespace Matrix",
            "theorem submatrix_mulVec_equiv : True := by trivial",
            "end Matrix",
            "namespace groupCohomology",
            "def IsMulCocycle₂ : Prop := True",
            "end groupCohomology",
            "def Owner.shared : Prop := True",
            "namespace Nested",
            "theorem Owner.nested : True := by trivial",
            "private theorem hidden : True := by trivial",
            "end Nested",
            "",
        ]))
        self.git("init", "-q")
        self.git("add", "Mathlib")
        self.git("-c", "user.name=Blueprint test", "-c", "user.email=test@example.invalid",
                 "commit", "-qm", "source fixture")
        rev = self.git("rev-parse", "HEAD")
        self.manifest(rev)
        return rev

    def tags(self, *names: str) -> None:
        self.chapter.write_text("\n".join(
            "\\begin{theorem}\n\\lean{" + name + "}\\leanok\n\\end{theorem}"
            for name in names
        ) + "\n")

    def run_sync(self) -> sync.SyncReport:
        with contextlib.redirect_stdout(io.StringIO()):
            return sync.run_sync(self.root)

    def test_valid_external_names_at_manifest_revision(self) -> None:
        self.dependency()
        names = ("Continuous.matrix_trace", "continuous_pow", "Matrix.submatrix_mulVec_equiv",
                 "groupCohomology.IsMulCocycle₂")
        self.tags(*names)
        report = self.run_sync()
        self.assertTrue(report.ok)
        self.assertEqual(len(report.blueprint_entries), len(names))
        for name in names:
            self.assertEqual(report.lean_decls[name].file, "Mathlib/Example.lean")

    def test_typo_is_missing_even_in_known_namespace(self) -> None:
        self.dependency()
        self.tags("Continuous.matrix_traceTypo")
        report = self.run_sync()
        self.assertFalse(report.ok)
        self.assertEqual([e.lean_decl for e in report.missing_in_lean],
                         ["Continuous.matrix_traceTypo"])
        self.assertEqual(len(report.leanok_but_missing), 1)

    def test_external_lookup_does_not_accept_short_or_private_names(self) -> None:
        self.dependency()
        self.tags("Owner.nested", "Nested.hidden")
        report = self.run_sync()
        self.assertFalse(report.ok)
        self.assertEqual({e.lean_decl for e in report.missing_in_lean},
                         {"Owner.nested", "Nested.hidden"})

    def test_local_source_has_precedence(self) -> None:
        self.dependency()
        self.tags("Owner.shared", "continuous_pow")
        report = self.run_sync()
        self.assertTrue(report.ok)
        self.assertEqual(report.lean_decls["Owner.shared"].file, "QICLean/Example.lean")

    def test_local_only_blueprint_needs_no_dependency(self) -> None:
        self.tags("Owner.shared")
        with mock.patch.object(sync, "_resolve_mathlib_lean_root") as resolve:
            self.assertTrue(self.run_sync().ok)
            resolve.assert_not_called()

    def test_missing_sources_fail_without_implicit_ci_fetch(self) -> None:
        self.manifest("a" * 40)
        self.tags("continuous_pow")
        with mock.patch.dict(os.environ, {"GITHUB_ACTIONS": "true"}), \
                mock.patch.object(sync, "_fetch_mathlib_sources") as fetch:
            self.assertFalse(self.run_sync().ok)
            fetch.assert_not_called()

    def test_revision_mismatch_fails_without_mutating_checkout(self) -> None:
        actual = self.dependency()
        self.manifest("a" * 40)
        self.tags("continuous_pow")
        with mock.patch.object(sync, "_fetch_mathlib_sources") as fetch:
            self.assertFalse(self.run_sync().ok)
            fetch.assert_not_called()
        self.assertEqual(self.git("rev-parse", "HEAD"), actual)

    def test_dirty_source_is_not_evidence_for_the_pinned_commit(self) -> None:
        self.dependency()
        self.write(".lake/packages/mathlib/Mathlib/Example.lean",
                   "theorem manufactured : True := by trivial\n")
        self.tags("manufactured")
        self.assertFalse(self.run_sync().ok)

    def test_ignored_scratch_file_cannot_resolve_a_name(self) -> None:
        self.dependency()
        (self.package / ".git/info/exclude").write_text("Mathlib/Scratch.lean\n")
        self.write(".lake/packages/mathlib/Mathlib/Scratch.lean",
                   "theorem manufactured : True := by trivial\n")
        self.tags("manufactured")
        self.assertFalse(self.run_sync().ok)

    def test_missing_or_invalid_manifest_keeps_external_names_missing(self) -> None:
        self.tags("continuous_pow")
        for manifest in (None, "not json", '{"packages": []}'):
            with self.subTest(manifest=manifest):
                if manifest is not None:
                    self.write("lake-manifest.json", manifest)
                self.assertFalse(self.run_sync().ok)

    def test_source_only_fetch_checks_out_exact_commit_not_input_tag(self) -> None:
        rev = self.dependency()
        origin = self.root / "fixture-origin"
        self.package.rename(origin)
        self.git("tag", "moving-tag", cwd=origin)
        (origin / "Mathlib/Example.lean").write_text("theorem wrong : True := by trivial\n")
        self.git("add", "Mathlib", cwd=origin)
        self.git("-c", "user.name=Blueprint test", "-c", "user.email=test@example.invalid",
                 "commit", "-qm", "later source", cwd=origin)
        self.git("tag", "-f", "moving-tag", cwd=origin)
        self.manifest(rev, url=origin.as_uri())
        self.tags("continuous_pow")
        with mock.patch.dict(os.environ, {"BLUEPRINT_SYNC_FETCH_DEPS": "1"}):
            self.assertTrue(self.run_sync().ok)
        self.assertEqual(self.git("rev-parse", "HEAD"), rev)
        self.assertFalse((self.package / ".lake/build").exists())

    def test_failed_fetch_leaves_no_partial_package(self) -> None:
        self.manifest("a" * 40, url=(self.root / "missing-origin").as_uri())
        self.tags("continuous_pow")
        with mock.patch.dict(os.environ, {"BLUEPRINT_SYNC_FETCH_DEPS": "1"}):
            self.assertFalse(self.run_sync().ok)
        self.assertFalse(self.package.exists())
        self.assertEqual(list(self.package.parent.glob(".blueprint-mathlib-*")), [])

    def test_ci_cli_still_exits_nonzero_for_missing_external_name(self) -> None:
        self.dependency()
        self.tags("Continuous.matrix_traceTypo")
        result = subprocess.run(
            ["python3", str(Path(sync.__file__).resolve()), "--root", str(self.root), "--ci"],
            capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("Continuous.matrix_traceTypo", result.stdout)


if __name__ == "__main__":
    unittest.main()
