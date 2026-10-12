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


class ParseImportsTest(unittest.TestCase):
    def test_header_only(self) -> None:
        text = ("/-\nCopyright\n-/\nimport A.B -- see D\nimport C\n\n/-! doc -/\n"
                "import NotHeader\n")
        self.assertEqual(ci.parse_imports(text), ["A.B", "C"])

    def test_module_system_keywords(self) -> None:
        text = "module\n\npublic import A\nmeta import B\nimport C D\n"
        self.assertEqual(ci.parse_imports(text), ["A", "B", "C", "D"])


class SelectTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        files = {
            "QICLean/Core.lean": "import Mathlib\n",
            "QICLean/Uses.lean": "import QICLean.Core\n",
            "QICLean/Other.lean": "import Mathlib\n",
            "QICLean/Archive/Old.lean": "import QICLean.Core\n",
            "QICLeanTest/Support/Fixture.lean": "import QICLean.Other\n",
            "QICLeanTest/UsesTest.lean": "import QICLean.Uses\n",
            "QICLeanTest/FixtureTest.lean": "import QICLeanTest.Support.Fixture\n",
            "QICLeanTest/Unrelated.lean": "import Mathlib\n",
            "scripts/Tests/CoreRegression.lean": "import QICLean.Uses\n",
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
            return ci.select(Path("."), base)[:3]
        finally:
            os.chdir(cwd)

    def test_transitive_dependents_are_selected(self) -> None:
        self.change("QICLean/Core.lean", "import Mathlib\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["QICLean.Core"])
        self.assertEqual(sources, ["QICLean/Core.lean"])
        self.assertEqual(tests, ["QICLeanTest/UsesTest.lean",
                                 "scripts/Tests/CoreRegression.lean"])

    def test_imported_test_fixture_runs_first(self) -> None:
        self.change("QICLean/Other.lean", "import Mathlib\n-- edit\n")
        _, _, tests = self.select(self.base)
        self.assertEqual(tests, ["QICLeanTest/Support/Fixture.lean",
                                 "QICLeanTest/FixtureTest.lean"])

    def test_changed_test_brings_its_fixture(self) -> None:
        self.change("QICLeanTest/FixtureTest.lean",
                    "import QICLeanTest.Support.Fixture\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), ([], []))
        self.assertEqual(tests, ["QICLeanTest/Support/Fixture.lean",
                                 "QICLeanTest/FixtureTest.lean"])

    def test_archive_is_not_built_early(self) -> None:
        self.change("QICLean/Archive/Old.lean", "import QICLean.Core\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources, tests), ([], [], []))

    def test_new_module_and_test(self) -> None:
        (self.root / "QICLean/New.lean").write_text("import QICLean.Core\n")
        self.change("QICLeanTest/NewTest.lean", "import QICLean.New\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["QICLean.New"])
        self.assertEqual(tests, ["QICLeanTest/NewTest.lean"])

    def test_changed_regression_script_is_selected(self) -> None:
        self.change("scripts/Tests/CoreRegression.lean", "import QICLean.Uses\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources, tests), ([], [], ["scripts/Tests/CoreRegression.lean"]))

    def test_deleted_module_marks_its_importers(self) -> None:
        (self.root / "QICLean/Uses.lean").unlink()
        git(self.root, "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "delete")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), ([], []))
        self.assertEqual(tests, ["QICLeanTest/UsesTest.lean", "scripts/Tests/CoreRegression.lean"])

    def test_renamed_module_marks_importers_of_the_old_name(self) -> None:
        git(self.root, "mv", "QICLean/Uses.lean", "QICLean/Renamed.lean")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "rename")
        early, sources, tests = self.select(self.base)
        self.assertEqual(early, ["QICLean.Renamed"])
        self.assertEqual(tests, ["QICLeanTest/UsesTest.lean", "scripts/Tests/CoreRegression.lean"])

    def test_deleted_test_fixture_marks_its_importers(self) -> None:
        (self.root / "QICLeanTest/Support/Fixture.lean").unlink()
        git(self.root, "add", "-A")
        git(self.root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "delete")
        _, _, tests = self.select(self.base)
        self.assertEqual(tests, ["QICLeanTest/FixtureTest.lean"])

    def test_dependency_pin_runs_every_test(self) -> None:
        self.change("lake-manifest.json", "{}\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), ([], []))
        self.assertEqual(len(tests), 5)
        self.assertNotIn("scripts/LintStyle.lean", tests)
        self.assertLess(tests.index("QICLeanTest/Support/Fixture.lean"),
                        tests.index("QICLeanTest/FixtureTest.lean"))

    def test_pin_change_keeps_changed_sources_strict(self) -> None:
        (self.root / "lake-manifest.json").write_text("{}\n")
        self.change("QICLean/Core.lean", "import Mathlib\n-- edit\n")
        early, sources, tests = self.select(self.base)
        self.assertEqual((early, sources), (["QICLean.Core"], ["QICLean/Core.lean"]))
        self.assertEqual(len(tests), 5)

    def test_lakefile_lean_runs_every_test(self) -> None:
        self.change("lakefile.lean", "import Lake\n")
        _, _, tests = self.select(self.base)
        self.assertEqual(len(tests), 5)

    def test_no_base_runs_every_test(self) -> None:
        _, _, tests = self.select(None)
        self.assertEqual(len(tests), 5)

    def test_levels_respect_imports(self) -> None:
        _, _, tests = self.select(None)
        files = ci.lean_files(self.root)
        cwd = Path.cwd()
        try:
            import os
            os.chdir(self.root)
            graph = ci.import_graph(Path("."), files)
        finally:
            os.chdir(cwd)
        batches = ci.levels(tests, graph)
        self.assertIn("QICLeanTest/Support/Fixture.lean", batches[0])
        self.assertIn("QICLeanTest/FixtureTest.lean", batches[1])


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
