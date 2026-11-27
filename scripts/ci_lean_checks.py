#!/usr/bin/env python3
"""Generic early builds and strict Lean checks for pull-request CI.

`pr-ci.yml` used to carry one hand-written step per new module ("Build X
early", "Test X strictly and audit axioms").  Every topic pull request edited
the same lines of the workflow, so unrelated pull requests conflicted there.
This script derives the same checks from the change set instead.

Commands
--------
``early``   Build the changed production modules with ``lake --fail-fast build``
            before the full library build, so a failure surfaces quickly.
``strict``  After the full build, elaborate every changed production source
            file with warnings as errors.
``list``    Print the selection of both commands.

Pushes use the previous head as the base. Without a base revision (manual
dispatch, an unfetchable base) both commands select nothing; the full build
covers every module. The repository keeps no Lean test fixtures, so there is
nothing else to select (see ``docs/project_conventions.md``).
"""

from __future__ import annotations

import argparse
import concurrent.futures
import os
import signal
import subprocess
import sys
import threading
from pathlib import Path

LEAN_FLAGS = [
    "-DautoImplicit=false",
    "-DrelaxedAutoImplicit=false",
    "-Dpp.unicode.fun=true",
    "-DmaxSynthPendingDepth=3",
    "-Dlinter.mathlibStandardSet=true",
    "-DwarningAsError=true",
]

# Keep aligned with EXCLUDED_TOP_LEVEL_DIRECTORIES in
# scripts/generate_import_aggregators.py.
EXCLUDED_PREFIXES = ("QICLean/Archive/",)


def module_of(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def is_production(path: str) -> bool:
    return (
        path.startswith("QICLean/")
        and path.endswith(".lean")
        and not path.startswith(EXCLUDED_PREFIXES)
    )


def changed_paths(base: str | None) -> list[str] | None:
    """Changed paths against `base`, or None without a base revision."""
    if not base:
        return None
    return [p for p in subprocess.run(
        ["git", "diff", "-z", "--name-only", "--no-renames", "--diff-filter=ACDM", base, "HEAD"],
        check=True, capture_output=True, text=True,
    ).stdout.split("\0") if p]


def select(root: Path, base: str | None) -> tuple[list[str], list[str]]:
    """Return (early modules, strict source files): the changed production
    files that still exist, and their modules."""
    sources = sorted(p for p in changed_paths(base) or []
                     if is_production(p) and (root / p).is_file())
    return [module_of(p) for p in sources], sources


def run_lean(path: str, timeout: int) -> tuple[str, int, str]:
    cmd = ["lake", "env", "timeout", "--signal=INT", "--kill-after=5s", f"{timeout}s",
           "lean", "-j1", *LEAN_FLAGS, path]
    env = dict(os.environ, LEAN_NUM_THREADS="1")
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True)
    return path, proc.returncode, proc.stdout + proc.stderr


def run_batch(paths: list[str], jobs: int, timeout: int) -> list[str]:
    failed: list[str] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        for path, code, output in pool.map(lambda p: run_lean(p, timeout), paths):
            status = "ok" if code == 0 else ("timeout" if code == 124 else f"exit {code}")
            print(f"::group::{path}: {status}", flush=True)
            if output.strip():
                print(output.rstrip(), flush=True)
            print("::endgroup::", flush=True)
            if code != 0:
                print(f"::error file={path}::strict Lean check failed ({status})", flush=True)
                failed.append(path)
    return failed


def _signal_group(pid: int, sig: int) -> None:
    try:
        os.killpg(pid, sig)
    except ProcessLookupError:
        pass  # the whole group has already exited


def _stop_group(proc: subprocess.Popen, grace: int = 30) -> None:
    """Terminate the build's process group: SIGTERM, a grace period for `lake`,
    then SIGKILL for any descendant that ignored it or outlived `lake`."""
    _signal_group(proc.pid, signal.SIGTERM)
    try:
        proc.wait(timeout=grace)
    except subprocess.TimeoutExpired:
        pass
    _signal_group(proc.pid, signal.SIGKILL)
    proc.wait()


def early_build(modules: list[str], log_path: Path | None, budget: int) -> int:
    """Fail-fast `lake build` of `modules`. The early build is only a shortcut,
    since the root build compiles the same modules, so when it exceeds `budget`
    seconds (for example behind a cold dependency cache) it is stopped with a
    warning instead of failing the job."""
    proc = subprocess.Popen(["lake", "--fail-fast", "build", *modules],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                            start_new_session=True)
    assert proc.stdout is not None

    def pump(stream, log) -> None:
        for line in stream:
            sys.stdout.write(line)
            log.write(line)

    with open(log_path or os.devnull, "a") as log:
        reader = threading.Thread(target=pump, args=(proc.stdout, log), daemon=True)
        reader.start()
        try:
            code: int | None = proc.wait(timeout=budget or None)
        except subprocess.TimeoutExpired:
            _stop_group(proc)
            code = None
        except BaseException:
            # The build runs in its own session, so an interrupt such as Ctrl-C
            # does not reach it; stop it before re-raising.
            _stop_group(proc, grace=5)
            raise
        finally:
            # A descendant that outlived `lake` would keep the pipe open.
            _signal_group(proc.pid, signal.SIGKILL)
            reader.join(timeout=60)
    if code is None:
        print(f"::warning::Early build stopped after {budget}s; "
              "the root build compiles the remaining modules.", flush=True)
        return 0
    return code


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("command", choices=["early", "strict", "list"])
    parser.add_argument("--base", default=os.environ.get("BASE_SHA") or None,
                        help="base revision; omit to select nothing")
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=240,
                        help="seconds allowed for each file")
    parser.add_argument("--log", type=Path, help="append early-build output here")
    parser.add_argument("--budget", type=int, default=0,
                        help="early: stop after this many seconds and leave the rest "
                             "to the root build (0 means no limit)")
    args = parser.parse_args(argv)

    os.chdir(args.root)
    early, sources = select(Path("."), args.base)

    if args.command == "list":
        for m in early:
            print("early", m)
        for s in sources:
            print("source", s)
        return 0

    if args.command == "early":
        if not early:
            print("No changed production modules to build early.")
            return 0
        print("Building changed modules early:", *early, sep="\n  ", flush=True)
        return early_build(early, args.log, args.budget)

    print(f"Strict checks: {len(sources)} changed source file(s).", flush=True)
    failed = run_batch(sources, args.jobs, args.timeout)
    if failed:
        print(f"{len(failed)} strict Lean check(s) failed:", *failed, sep="\n  ")
        return 1
    print("All strict Lean checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
