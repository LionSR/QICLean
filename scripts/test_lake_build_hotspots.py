#!/usr/bin/env python3
"""Unit tests for the Lake build hotspot parser."""

from __future__ import annotations

import contextlib
import io
import tempfile
import unittest
from pathlib import Path

import lake_build_hotspots as hotspots


class LakeBuildHotspotTests(unittest.TestCase):
    def test_parses_units_ansi_and_optional_progress_prefix(self) -> None:
        jobs = hotspots.parse_timed_jobs(
            "\n".join(
                [
                    "✔ [9622/9713] Built QICLean.Slow (831s)",
                    "\x1b[32m⚠ [2/3] Built QICLean.Fast:c.o (250ms)\x1b[0m",
                    "Replayed QICLean.Middle (1.5m)",
                    "✖ [3/3] Built QICLean.Failed (98s)",
                    "info: unrelated output",
                ]
            )
        )
        self.assertEqual(
            jobs,
            [
                hotspots.TimedJob("QICLean.Slow", 831.0),
                hotspots.TimedJob("QICLean.Failed", 98.0),
                hotspots.TimedJob("QICLean.Middle", 90.0),
                hotspots.TimedJob("QICLean.Fast:c.o", 0.25),
            ],
        )

    def test_report_is_ranked_filtered_and_limited(self) -> None:
        jobs = [
            hotspots.TimedJob("QICLean.A", 10.0),
            hotspots.TimedJob("QICLean.B", 5.0),
            hotspots.TimedJob("QICLean.C", 1.0),
        ]
        self.assertEqual(
            hotspots.render_tsv(jobs, threshold=5.0, limit=1),
            "seconds\tjob\n10.000\tQICLean.A\n",
        )

    def test_equal_timings_are_deterministic(self) -> None:
        jobs = hotspots.parse_timed_jobs(
            "[1/2] Built QICLean.Z (12s)\n[2/2] Built QICLean.A (12s)\n"
        )
        self.assertEqual([job.job for job in jobs], ["QICLean.A", "QICLean.Z"])

    def test_changed_file_gate_warns_at_twenty_five_and_fails_at_fifty(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "lake.log"
            changed = Path(directory) / "changed.txt"
            log.write_text(
                "\n".join(
                    [
                        "Built QICLean.Unchanged (80s)",
                        "Built QICLean.Warning (25s)",
                        "Built QICLean.TooSlow (50s)",
                        "Built LintStyle (30s)",
                        "Built QICLean.Σlow (26s)",
                    ]
                ),
                encoding="utf-8",
            )
            changed.write_text(
                "QICLean/Warning.lean\nQICLean/TooSlow.lean\nscripts/LintStyle.lean\n"
                "QICLean/Σlow.lean\nREADME.md\n",
                encoding="utf-8",
            )
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                status = hotspots.main([str(log), "--changed-files-from", str(changed)])
        self.assertEqual(status, hotspots.TIMING_LIMIT_EXIT)
        self.assertEqual(
            output.getvalue(),
            "\n".join(
                [
                    "seconds\tjob",
                    "50.000\tQICLean.TooSlow",
                    "30.000\tLintStyle",
                    "26.000\tQICLean.Σlow",
                    "25.000\tQICLean.Warning",
                    "::error file=QICLean/TooSlow.lean::QICLean.TooSlow compiled in 50.000s "
                    "(warning at 25s, error at 50s)",
                    "::warning file=scripts/LintStyle.lean::LintStyle compiled in 30.000s "
                    "(warning at 25s, error at 50s)",
                    "::warning file=QICLean/Σlow.lean::QICLean.Σlow compiled in 26.000s "
                    "(warning at 25s, error at 50s)",
                    "::warning file=QICLean/Warning.lean::QICLean.Warning compiled in 25.000s "
                    "(warning at 25s, error at 50s)",
                    "",
                ]
            ),
        )

    def test_changed_file_gate_ignores_unmodified_slow_modules(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / "lake.log"
            changed = Path(directory) / "changed.txt"
            log.write_text("Built QICLean.Unchanged (80s)\n", encoding="utf-8")
            changed.write_text("QICLean/Changed.lean\n", encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()):
                status = hotspots.main([str(log), "--changed-files-from", str(changed)])
        self.assertEqual(status, 0)

    def test_annotations_ignore_jobs_without_a_matching_path(self) -> None:
        self.assertEqual(
            hotspots.render_github_annotations(
                [hotspots.TimedJob("QICLean.Unchanged", 80.0)],
                ["QICLean/Changed.lean"],
                warn_threshold=25.0,
                error_threshold=50.0,
            ),
            "",
        )

    def test_changed_file_gate_includes_native_facets(self) -> None:
        jobs = [hotspots.TimedJob("LintStyle:c.o", 51.0)]
        paths = ["scripts/LintStyle.lean"]
        self.assertEqual(hotspots.changed_jobs(jobs, paths), jobs)
        self.assertIn(
            "::error file=scripts/LintStyle.lean::LintStyle:c.o compiled in 51.000s",
            hotspots.render_github_annotations(jobs, paths, 25.0, 50.0),
        )


if __name__ == "__main__":
    unittest.main()
