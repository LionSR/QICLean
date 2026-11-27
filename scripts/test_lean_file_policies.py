#!/usr/bin/env python3
"""Unit tests for the Lean module naming, file-size and small-module policy checkers."""

from __future__ import annotations

import contextlib
import io
import subprocess
import tempfile
import unittest
from collections.abc import Callable
from pathlib import Path

import check_import_layers as layers
import check_numbered_lean_files as numbered
import check_oversized_lean_files as oversized
import check_small_lean_modules as small


class CapturedCheck(unittest.TestCase):
    def capture(self, function: Callable[..., int], *args: object) -> tuple[int, str]:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = function(*args)
        return status, output.getvalue()


class NumberedLeanFilePolicyTests(CapturedCheck):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def track(self, relative: str, source: str = "def x := 1\n") -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        subprocess.run(["git", "-C", str(self.root), "add", relative], check=True)

    def check(
        self,
        debt: frozenset[str] = frozenset(),
        exceptions: dict[str, str] | None = None,
        base_debt: frozenset[str] | None = None,
    ) -> tuple[int, str]:
        return self.capture(
            numbered.check_numbered_files,
            self.root,
            debt,
            {} if exceptions is None else exceptions,
            base_debt,
        )

    def test_new_numbered_production_file_fails_with_guidance(self) -> None:
        self.track("QICLean/Proof2.lean")
        status, output = self.check()
        self.assertEqual(status, 1)
        self.assertIn("new numbered-sequel filename", output)
        self.assertIn("Basic.lean", output)

    def test_existing_debt_is_allowed(self) -> None:
        path = "QICLean/Proof2.lean"
        self.track(path)
        status, output = self.check(frozenset({path}))
        self.assertEqual(status, 0)
        self.assertIn("1 numbered debt", output)

    def test_new_debt_allowlist_entry_fails_against_base(self) -> None:
        path = "QICLean/Proof2.lean"
        self.track(path)
        status, output = self.check(frozenset({path}), base_debt=frozenset())
        self.assertEqual(status, 1)
        self.assertIn("debt allowlist; this set may only shrink", output)

    def test_base_debt_ratchet_rejects_pr_and_multicommit_push_additions(self) -> None:
        old_path = "QICLean/Old2.lean"
        new_path = "QICLean/New3.lean"
        self.track(old_path)
        checker = self.root / "scripts" / "check_numbered_lean_files.py"
        checker.parent.mkdir(parents=True)
        checker.write_text(
            "NUMBERED_DEBT_ALLOWLIST: frozenset[str] = "
            f"frozenset({{{old_path!r}}})\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "-C", str(self.root), "add", checker.relative_to(self.root)],
            check=True,
        )
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "baseline",
            ],
            check=True,
        )
        base_ref = subprocess.run(
            ["git", "-C", str(self.root), "rev-parse", "HEAD"],
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()

        self.track(new_path)
        checker.write_text(
            "NUMBERED_DEBT_ALLOWLIST: frozenset[str] = "
            f"frozenset({{{old_path!r}, {new_path!r}}})\n",
            encoding="utf-8",
        )
        subprocess.run(
            ["git", "-C", str(self.root), "add", checker.relative_to(self.root)],
            check=True,
        )
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "proposed addition",
            ],
            check=True,
        )

        baseline = numbered._debt_allowlist_at_merge_base(self.root, base_ref)
        status, output = self.check(
            frozenset({old_path, new_path}),
            base_debt=baseline,
        )
        self.assertEqual(status, 1)
        self.assertIn(f"{new_path}: added to the numbered debt allowlist", output)

        self.track("QICLean/Unrelated.lean")
        subprocess.run(
            [
                "git", "-C", str(self.root),
                "-c", "user.name=Test",
                "-c", "user.email=test@example.com",
                "commit", "-qm", "later commit in the same push",
            ],
            check=True,
        )

        parent_baseline = numbered._debt_allowlist_at_merge_base(self.root, "HEAD^")
        parent_status, _ = self.check(
            frozenset({old_path, new_path}),
            base_debt=parent_baseline,
        )
        self.assertEqual(parent_status, 0)

        push_baseline = numbered._debt_allowlist_at_merge_base(self.root, base_ref)
        push_status, push_output = self.check(
            frozenset({old_path, new_path}),
            base_debt=push_baseline,
        )
        self.assertEqual(push_status, 1)
        self.assertIn(f"{new_path}: added to the numbered debt allowlist", push_output)

    def test_removing_debt_allowlist_entry_is_allowed(self) -> None:
        path = "QICLean/Proof2.lean"
        self.track(path)
        status, output = self.check(
            frozenset({path}),
            base_debt=frozenset({path, "QICLean/Removed3.lean"}),
        )
        self.assertEqual(status, 0)

    def test_stale_debt_entry_fails_so_allowlist_shrinks(self) -> None:
        status, output = self.check(frozenset({"QICLean/Gone2.lean"}))
        self.assertEqual(status, 1)
        self.assertIn("stale debt allowlist entry", output)

    def test_documented_semantic_exception_is_allowed(self) -> None:
        path = "QICLean/ZMod2.lean"
        self.track(path)
        status, output = self.check(
            exceptions={path: "The numeral is part of the mathematical type name."}
        )
        self.assertEqual(status, 0)
        self.assertIn("1 semantic exceptions", output)

    def test_empty_semantic_explanation_fails(self) -> None:
        path = "QICLean/ZMod2.lean"
        self.track(path)
        status, output = self.check(exceptions={path: "  "})
        self.assertEqual(status, 1)
        self.assertIn("has no explanation", output)

    def test_archive_and_untracked_files_are_out_of_scope(self) -> None:
        self.track("QICLean/Archive/Legacy2.lean")
        untracked = self.root / "QICLean" / "Scratch2.lean"
        untracked.write_text("def scratch := 2\n", encoding="utf-8")
        status, output = self.check()
        self.assertEqual(status, 0)
        self.assertIn("0 numbered debt", output)


class OversizedLeanFilePolicyTests(CapturedCheck):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write(self, relative: str, source: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")

    def test_oversized_module_fails_with_actionable_split_guidance(self) -> None:
        self.write("QICLean/Huge.lean", "def x := 1\n" * (oversized.THRESHOLD + 1))
        status, output = self.capture(oversized.check_files, self.root, set(), set())
        self.assertEqual(status, 1)
        self.assertIn("concept-named modules", output)
        self.assertIn("Foo2.lean", output)

    def test_exact_import_only_aggregator_is_exempt(self) -> None:
        source = "/- generated\n  /- nested comment -/\n-/\n" + (
            "import QICLean.Algebra.Basic -- public import\n" * (oversized.THRESHOLD + 1)
        )
        self.write("QICLean.lean", source)
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"QICLean.lean"}
        )
        self.assertEqual(status, 0)
        self.assertIn("validated 1 of 1 exact aggregator exemption", output)

    def test_import_only_file_is_not_exempt_without_exact_registration(self) -> None:
        self.write(
            "QICLean/All.lean",
            "import QICLean.Basic\n" * (oversized.THRESHOLD + 1),
        )
        status, output = self.capture(oversized.check_files, self.root, set(), set())
        self.assertEqual(status, 1)
        self.assertIn("Oversized Lean file", output)

    def test_aggregator_with_declaration_is_rejected_even_below_limit(self) -> None:
        self.write("QICLean.lean", "import QICLean.Basic\ndef notAnAggregator := 1\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"QICLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("contains non-import Lean code", output)

    def test_aggregator_with_invalid_module_segment_is_rejected(self) -> None:
        self.write("QICLean.lean", "import QICLean.0Invalid\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"QICLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("contains non-import Lean code", output)

    def test_missing_aggregator_exemption_is_rejected(self) -> None:
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"Missing.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("must name an existing, scanned .lean file", output)

    def test_unterminated_comment_rejects_aggregator(self) -> None:
        self.write("QICLean.lean", "import QICLean.Basic\n/- never closed\n")
        status, output = self.capture(
            oversized.check_files, self.root, set(), {"QICLean.lean"}
        )
        self.assertEqual(status, 1)
        self.assertIn("unterminated block comment", output)


class SmallModuleCeilingTests(unittest.TestCase):
    def test_public_top_level_declarations_are_counted(self) -> None:
        count = small.public_declarations
        source = (
            "import QICLean.Algebra.Matrix.Basic\n"
            "/-! A module docstring naming theorem fake. -/\n"
            "@[simp] theorem a : True := trivial\n"
            "private lemma b : True := trivial\n"
            "noncomputable def c := 0\n"
            "  theorem indented : True := trivial\n"
            'def d := "theorem inString"\n'
            "-- theorem commented : True := trivial\n"
        )
        self.assertEqual(count(source), 3)
        self.assertEqual(count("syntax \"foo\" : tactic\n"), 0)

    def test_aggregators_and_import_only_modules_are_not_counted(self) -> None:
        generated = f"-- {small.AGGREGATOR_MARKER}\nimport QICLean.A\n"
        self.assertIsNone(small.public_declarations(generated))
        self.assertIsNone(small.public_declarations("/- forward -/\nimport QICLean.A\n"))

    def test_modules_are_grouped_by_the_directories_of_the_layer_check(self) -> None:
        sources = {
            "QICLean.ManyBody.Replica.Sub.A": "theorem a : True := trivial\n",
            "QICLean.Algebra.Deep.B": "def b := 0\n",
            "QICLean.Root": "def r := 0\n",
            "QICLean.ManyBody.Replica.Big": "def x := 0\ndef y := 0\ndef z := 0\n",
        }
        self.assertEqual(
            small.small_modules(sources),
            {
                "ManyBody/Replica": {"QICLean.ManyBody.Replica.Sub.A": 1},
                "Algebra": {"QICLean.Algebra.Deep.B": 1},
                ".": {"QICLean.Root": 1},
            },
        )

    def test_a_count_above_its_ceiling_names_the_directory_and_modules(self) -> None:
        found = {"ManyBody/Replica": {"QICLean.ManyBody.Replica.A": 1, "QICLean.ManyBody.Replica.B": 2}}
        errors, _ = small.check(found, {"ManyBody/Replica": 1})
        self.assertEqual(len(errors), 1)
        self.assertIn("ManyBody/Replica has 2 modules", errors[0])
        self.assertIn("QICLean.ManyBody.Replica.A (1), QICLean.ManyBody.Replica.B (2)", errors[0])
        # A changed module is named in preference to the others.
        errors, _ = small.check(found, {"ManyBody/Replica": 1}, {"ManyBody/Replica": 1}, {},
                                {"QICLean.ManyBody.Replica.B"})
        self.assertIn("added or changed modules: QICLean.ManyBody.Replica.B (2)", errors[0])
        # A directory without a ceiling has ceiling 0.
        errors, _ = small.check({"Entropy": {"QICLean.Entropy.New": 0}}, {})
        self.assertIn("above its ceiling of 0", errors[0])
        # A count below its ceiling only warns.
        errors, warnings = small.check({}, {"Entropy": 2})
        self.assertEqual(errors, [])
        self.assertIn("below its ceiling of 2", warnings[0])

    def test_write_lowers_ceilings_and_never_raises_one(self) -> None:
        self.assertEqual(
            small.lowered({"A": 3, "B": 2, "C": 1}, {"A": 1, "B": 5, "D": 4}), {"A": 1, "B": 2}
        )
        text = small.format_ceilings({"ManyBody/Replica": 2, "Entropy": 1, "Gone": 0})
        self.assertEqual(small.parse_ceilings(text), {"ManyBody/Replica": 2, "Entropy": 1})
        for bad in ("A\n", "A x\n", "A 1\nA 2\n"):
            with self.assertRaises(ValueError):
                small.parse_ceilings(bad)

    def test_ceilings_may_only_fall_against_the_base(self) -> None:
        found = {"A": {"QICLean.A.X": 1, "QICLean.A.Y": 1}}
        errors, _ = small.check(found, {"A": 2}, {"A": 1}, {})
        self.assertEqual(
            errors,
            [
                "Ceiling of A rose from 1 to 2; a ceiling may only fall",
                "Sum of the ceilings rose from 1 to 2; when a small module moves, lower the "
                "ceiling of the directory it left",
            ],
        )
        # A moved module carries its ceiling, provided the directory it left falls.
        moved = {"B": {"QICLean.B.X": 1}, "A": {"QICLean.A.Y": 1}}
        self.assertEqual(small.check(moved, {"A": 1, "B": 1}, {"A": 2}, {"B": 1})[0], [])
        errors, _ = small.check(moved, {"A": 2, "B": 1}, {"A": 2}, {"B": 1})
        self.assertEqual(len(errors), 1)
        self.assertIn("Sum of the ceilings rose from 2 to 3", errors[0])
        # Without a base the recorded ceilings are the baseline.
        self.assertEqual(small.check(found, {"A": 2}, None)[0], [])

    def test_moves_and_changes_are_read_from_git(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def git(*args: str) -> None:
                subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True)

            def write(relative: str, text: str) -> None:
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")

            git("init", "-q")
            git("config", "user.email", "test@example.com")
            git("config", "user.name", "test")
            write("QICLean/Entropy/Moved.lean", "theorem moved_statement : True := trivial\n")
            write(small.CEILINGS_PATH, "Entropy 1\n")
            git("add", ".")
            git("commit", "-q", "-m", "base")
            git("branch", "base")
            write("QICLean/Algebra/New.lean", "def fresh := 0\n")
            git("mv", "QICLean/Entropy/Moved.lean", "QICLean/Algebra/Moved.lean")
            git("add", ".")
            git("commit", "-q", "-m", "head")
            found = small.small_modules(layers.tracked_sources(root))
            base, moved_in, changed = small.base_state(root, "base", found)
        self.assertEqual(base, {"Entropy": 1})
        self.assertEqual(moved_in, {"Algebra": 1})
        self.assertEqual(changed, {"QICLean.Algebra.Moved", "QICLean.Algebra.New"})

    def test_a_module_deleted_in_the_working_tree_is_absent(self) -> None:
        # Git still lists a module that is removed but not yet committed; the checks read
        # the tree on disk instead of failing on the missing file.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)

            def git(*args: str) -> None:
                subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True)

            git("init", "-q")
            git("config", "user.email", "test@example.com")
            git("config", "user.name", "test")
            for name in ("Kept", "Deleted"):
                path = root / "QICLean" / "Entropy" / f"{name}.lean"
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(f"def {name.lower()} := 0\n", encoding="utf-8")
            (root / small.CEILINGS_PATH).parent.mkdir(parents=True, exist_ok=True)
            (root / small.CEILINGS_PATH).write_text("Entropy 2\n", encoding="utf-8")
            git("add", ".")
            git("commit", "-q", "-m", "base")
            git("branch", "base")
            (root / "QICLean" / "Entropy" / "Deleted.lean").unlink()
            sources = layers.tracked_sources(root)
            found = small.small_modules(sources)
            base, _, changed = small.base_state(root, "base", found)
        self.assertEqual(set(sources), {"QICLean.Entropy.Kept"})
        self.assertEqual(found, {"Entropy": {"QICLean.Entropy.Kept": 1}})
        self.assertEqual(base, {"Entropy": 2})
        self.assertEqual(changed, set())

    def test_recorded_ceilings_hold_for_the_tree(self) -> None:
        root = Path(__file__).resolve().parent.parent
        found = small.small_modules(layers.tracked_sources(root))
        ceilings = small.parse_ceilings((root / small.CEILINGS_PATH).read_text(encoding="utf-8"))
        self.assertEqual(small.check(found, ceilings)[0], [])


if __name__ == "__main__":
    unittest.main()
