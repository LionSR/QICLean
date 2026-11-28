#!/usr/bin/env python3
"""Tests for the change-set selection in scripts/ci_lean_checks.py."""

from __future__ import annotations

import importlib.util
import subprocess
import tempfile
import unittest
from pathlib import Path

SPEC = importlib.util.spec_from_file_location(
    "ci_lean_checks", Path(__file__).with_name("ci_lean_checks.py"))
ci = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(ci)


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", *args], cwd=root, check=True,
                          capture_output=True, text=True).stdout.strip()


class SelectTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        files = {
            "QICLean/Core.lean": "import Mathlib\n",
            "QICLean/Uses.lean": "import QICLean.Core\n",
            "QICLean/Other.lean": "import Mathlib\n",
            "QICLean/Archive/Old.lean": "import QICLean.Core\n",
            "QICLean.lean": "import QICLean.Core\n",
            "scripts/LintStyle.lean": "import QICLean.Core\n",
        }
        for path, text in files.items():
            p = self.root / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        git(self.root, "init", "-q")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t",
            "commit", "-qm", "base")
        self.base = git(self.root, "rev-parse", "HEAD")

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def change(self, path: str, text: str) -> None:
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        git(self.root, "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t",
            "commit", "-qm", "change")

    def select(self, base: str | None):
        cwd = Path.cwd()
        try:
            import os
            os.chdir(self.root)
            return ci.select(Path("."), base)
        finally:
            os.chdir(cwd)

    def test_changed_module_is_selected_alone(self) -> None:
        self.change("QICLean/Core.lean", "import Mathlib\n-- edit\n")
        early, sources = self.select(self.base)
        self.assertEqual(early, ["QICLean.Core"])
        self.assertEqual(sources, ["QICLean/Core.lean"])

    def test_archive_is_not_built_early(self) -> None:
        self.change("QICLean/Archive/Old.lean", "import QICLean.Core\n-- edit\n")
        self.assertEqual(self.select(self.base), ([], []))

    def test_root_aggregator_and_scripts_are_not_selected(self) -> None:
        (self.root / "QICLean.lean").write_text("import QICLean.Core\n-- edit\n")
        self.change("scripts/LintStyle.lean", "import QICLean.Core\n-- edit\n")
        self.assertEqual(self.select(self.base), ([], []))

    def test_new_module(self) -> None:
        self.change("QICLean/New.lean", "import QICLean.Core\n")
        early, sources = self.select(self.base)
        self.assertEqual(early, ["QICLean.New"])
        self.assertEqual(sources, ["QICLean/New.lean"])

    def test_deleted_module_is_not_selected(self) -> None:
        (self.root / "QICLean/Uses.lean").unlink()
        git(self.root, "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "delete")
        self.assertEqual(self.select(self.base), ([], []))

    def test_renamed_module_selects_the_new_name(self) -> None:
        git(self.root, "mv", "QICLean/Uses.lean", "QICLean/Renamed.lean")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "rename")
        early, sources = self.select(self.base)
        self.assertEqual(early, ["QICLean.Renamed"])
        self.assertEqual(sources, ["QICLean/Renamed.lean"])

    def test_pin_change_keeps_changed_sources_strict(self) -> None:
        (self.root / "lake-manifest.json").write_text("{}\n")
        self.change("QICLean/Core.lean", "import Mathlib\n-- edit\n")
        self.assertEqual(self.select(self.base), (["QICLean.Core"], ["QICLean/Core.lean"]))

    def test_no_base_selects_nothing(self) -> None:
        self.assertEqual(self.select(None), ([], []))


class EarlyBuildTest(unittest.TestCase):
    """Run early_build against a stand-in `lake`."""

    def setUp(self) -> None:
        import os
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.dir = Path(tmp.name)
        self.old_path = os.environ["PATH"]
        self.addCleanup(os.environ.__setitem__, "PATH", self.old_path)
        os.environ["PATH"] = f"{self.dir}:{self.old_path}"
        self.log = self.dir / "lake-build.log"

    def lake(self, body: str) -> None:
        path = self.dir / "lake"
        path.write_text("#!/bin/bash\necho building \"$@\"\n" + body)
        path.chmod(0o755)

    def test_success_and_log(self) -> None:
        self.lake("exit 0\n")
        self.assertEqual(ci.early_build(["QICLean.Core"], self.log, 0), 0)
        self.assertIn("building --fail-fast build QICLean.Core", self.log.read_text())

    def test_build_failure_fails_the_step(self) -> None:
        self.lake("exit 3\n")
        self.assertEqual(ci.early_build(["QICLean.Core"], self.log, 0), 3)

    def test_budget_kills_descendants_that_ignore_sigterm(self) -> None:
        # lake exits on SIGTERM, but its compiler child ignores it and holds the
        # output pipe; the step must still end promptly.
        self.lake("bash -c 'trap \"\" TERM; sleep 60' &\n"
                  "trap 'exit 143' TERM\nsleep 60 & wait\n")
        import io, time
        from contextlib import redirect_stdout
        start = time.monotonic()
        with redirect_stdout(io.StringIO()):
            code = ci.early_build(["QICLean.Core"], self.log, 1)
        self.assertEqual(code, 0)
        self.assertLess(time.monotonic() - start, 20)

    def test_budget_exceeded_is_a_warning(self) -> None:
        self.lake("sleep 30\n")
        import io
        from contextlib import redirect_stdout
        out = io.StringIO()
        with redirect_stdout(out):
            code = ci.early_build(["QICLean.Core"], self.log, 1)
        self.assertEqual(code, 0)
        self.assertIn("::warning::Early build stopped after 1s", out.getvalue())


if __name__ == "__main__":
    unittest.main()
