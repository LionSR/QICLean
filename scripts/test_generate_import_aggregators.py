#!/usr/bin/env python3
"""Regression tests for the deterministic QICLean import-aggregator generator."""

from __future__ import annotations

import contextlib
import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest import mock

SCRIPT = Path(__file__).with_name("generate_import_aggregators.py")
SPEC = importlib.util.spec_from_file_location("generate_import_aggregators", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


class ImportAggregatorGeneratorTests(unittest.TestCase):
    def write(self, root: Path, relative: str, content: str) -> Path:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def generated_snapshot(self, root: Path) -> dict[str, bytes]:
        paths = [root / "QICLean.lean", *(root / "QICLean").rglob("*.lean")]
        return {
            path.relative_to(root).as_posix(): path.read_bytes()
            for path in paths
            if GENERATOR.is_generated(path, root / "QICLean")
        }

    def test_idempotent_and_preserves_shadowing_content(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "QICLean/Foo/Basic.lean", "def foo : Nat := 1\n")
            shadow = self.write(root, "QICLean/Shadow.lean", "def shadow : Nat := 2\n")
            self.write(root, "QICLean/Shadow/Leaf.lean", "def leaf : Nat := 3\n")
            self.write(root, "QICLean/Archive/Old.lean", "def old : Nat := 4\n")
            shadow_before = shadow.read_bytes()

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)
            first_snapshot = self.generated_snapshot(root)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)
            second_snapshot = self.generated_snapshot(root)

            self.assertEqual(first_snapshot, second_snapshot)
            self.assertEqual(shadow.read_bytes(), shadow_before)
            self.assertNotIn("QICLean/Shadow.lean", first_snapshot)
            self.assertEqual(set(first_snapshot), {"QICLean.lean", "QICLean/Foo.lean"})
            root_text = (root / "QICLean.lean").read_text(encoding="utf-8")
            self.assertIn("import QICLean.Foo\n", root_text)
            self.assertIn("import QICLean.Shadow\n", root_text)
            self.assertIn("import QICLean.Shadow.Leaf\n", root_text)
            self.assertNotIn("Archive", root_text)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=True), 0)

    def test_generated_detection_is_independent_of_copyright_year(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "QICLean/Foo/Basic.lean", "def foo := 1\n")
            generated = self.write(
                root,
                "QICLean/Foo.lean",
                GENERATOR.generated_notice("QICLean.Foo").replace("2026", "2037")
                + "\nimport QICLean.Foo.Basic\n",
            )
            self.assertTrue(GENERATOR.is_generated(generated, root / "QICLean"))

    def test_handwritten_marker_files_are_preserved_and_counted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "QICLean/Draft/Leaf.lean", "def leaf := 1\n")
            draft = self.write(
                root,
                "QICLean/Draft.lean",
                GENERATOR.GENERATED_NOTICE + "\ndef handwrittenDraft := 2\n",
            )
            copied = self.write(
                root,
                "QICLean/Copied.lean",
                GENERATOR.GENERATED_NOTICE + "\nimport QICLean.Draft\n",
            )
            self.write(root, "QICLean/Barrel/Leaf.lean", "def barrelLeaf := 3\n")
            barrel = self.write(
                root,
                "QICLean/Barrel.lean",
                GENERATOR.GENERATED_NOTICE + "\nimport QICLean.Barrel.Leaf\n",
            )
            draft_before = draft.read_bytes()
            copied_before = copied.read_bytes()
            barrel_before = barrel.read_bytes()

            self.assertFalse(GENERATOR.is_generated(draft, root / "QICLean"))
            self.assertFalse(GENERATOR.is_generated(copied, root / "QICLean"))
            self.assertFalse(GENERATOR.is_generated(barrel, root / "QICLean"))
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)

            self.assertEqual(draft.read_bytes(), draft_before)
            self.assertEqual(copied.read_bytes(), copied_before)
            self.assertEqual(barrel.read_bytes(), barrel_before)
            _, sources = GENERATOR.build_expected_files(root)
            self.assertIn(draft, sources)
            self.assertIn(copied, sources)
            self.assertIn(barrel, sources)
            root_text = (root / "QICLean.lean").read_text(encoding="utf-8")
            self.assertIn("import QICLean.Draft\n", root_text)
            self.assertIn("import QICLean.Copied\n", root_text)
            self.assertIn("import QICLean.Barrel\n", root_text)

    def test_stale_generated_aggregator_is_removed_after_directory_deletion(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            leaf = self.write(root, "QICLean/Foo/Leaf.lean", "def leaf := 1\n")
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)
            aggregator = root / "QICLean/Foo.lean"
            self.assertTrue(GENERATOR.is_generated(aggregator, root / "QICLean"))

            leaf.unlink()
            leaf.parent.rmdir()
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)

            self.assertFalse(aggregator.exists())
            self.assertNotIn(
                "import QICLean.Foo\n",
                (root / "QICLean.lean").read_text(encoding="utf-8"),
            )

    def test_archive_marker_file_is_never_deleted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            archived = self.write(
                root,
                "QICLean/Archive/All.lean",
                GENERATOR.generated_notice("QICLean.Archive.All")
                + "\nimport QICLean.Archive.Old\n",
            )
            before = archived.read_bytes()
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)
            self.assertEqual(archived.read_bytes(), before)
            self.assertFalse(GENERATOR.is_generated(archived, root / "QICLean"))

    def test_manifest_coverage_ignores_incidental_handwritten_imports(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "QICLean/Foo/A.lean", "import QICLean.Foo.B\ndef a := 1\n")
            self.write(root, "QICLean/Foo/B.lean", "def b := 2\n")
            expected, sources = GENERATOR.build_expected_files(root)
            foo_aggregator = root / "QICLean/Foo.lean"
            expected[foo_aggregator] = expected[foo_aggregator].replace(
                "import QICLean.Foo.B\n", ""
            )

            self.assertEqual(
                GENERATOR.check_manifest_coverage(root, expected, sources),
                ["QICLean.Foo.B"],
            )

            output = io.StringIO()
            with mock.patch.object(
                GENERATOR, "build_expected_files", return_value=(expected, sources)
            ), contextlib.redirect_stdout(output):
                self.assertEqual(GENERATOR.update(root, check=False), 1)
            self.assertIn("absent from the generated import frontier", output.getvalue())
            self.assertFalse((root / "QICLean.lean").exists())

    def test_check_rejects_omitted_import_despite_incidental_reachability(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "QICLean/Foo/A.lean", "import QICLean.Foo.B\ndef a := 1\n")
            self.write(root, "QICLean/Foo/B.lean", "def b := 2\n")
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(GENERATOR.update(root, check=False), 0)
            aggregator = root / "QICLean/Foo.lean"
            aggregator.write_text(
                aggregator.read_text(encoding="utf-8").replace(
                    "import QICLean.Foo.B\n", ""
                ),
                encoding="utf-8",
            )

            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertEqual(GENERATOR.update(root, check=True), 1)
            self.assertIn("out-of-date generated aggregator: QICLean/Foo.lean", output.getvalue())

    def test_import_parser_rejects_digit_initial_name_segment(self) -> None:
        self.assertEqual(GENERATOR.imported_modules("import QICLean.0Invalid\n"), set())
        self.assertEqual(
            GENERATOR.imported_modules("import QICLean.Valid_Name2\n"),
            {"QICLean.Valid_Name2"},
        )

    def test_check_rejects_out_of_date_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary_directory:
            root = Path(temporary_directory)
            self.write(root, "QICLean/Foo/Basic.lean", "def foo : Nat := 1\n")
            with contextlib.redirect_stdout(io.StringIO()):
                GENERATOR.update(root, check=False)
            aggregator = root / "QICLean/Foo.lean"
            aggregator.write_text(
                aggregator.read_text(encoding="utf-8") + "import QICLean.Extra\n",
                encoding="utf-8",
            )

            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertEqual(GENERATOR.update(root, check=True), 1)
            self.assertIn("out-of-date generated aggregator: QICLean/Foo.lean", output.getvalue())


if __name__ == "__main__":
    unittest.main()
