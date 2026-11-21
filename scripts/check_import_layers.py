#!/usr/bin/env python3
"""Enforce the QICLean library layers and shrinking import debt.

Ported from TNLean; see docs/library_layers.md for the single-system layers and
docs/import_structure.md for ownership, allowed imports, source revision, scope
and commands. Comments are removed before parsing imports;
import-only aggregators are expanded recursively. New and stale recorded entries
fail; --base-ref compares with the merge base, --base-revision with an exact commit.
"""

# Adapted from LionSR/TNLean scripts/check_import_layers.py at
# 7e8438a32f1f0435e3acec579a89656de1b3f07b (Apache-2.0).
# Changes: QICLean layer ownership and debt baselines; see docs/import_structure.md.

from __future__ import annotations

import argparse
import ast
import functools
import re
import subprocess
from collections.abc import Callable, Iterable, Mapping
from pathlib import Path

from lean_import_syntax import strip_lean_comments

PRODUCTION_ROOT = "QICLean/"
ARCHIVE_ROOT = "QICLean/Archive/"
CHECKER_PATH = "scripts/check_import_layers.py"
# An import command with the modifiers Lean accepts: ``import M``,
# ``public import M``, ``meta import M``, ``public meta import M``, ``import all M``.
# Lean identifiers also permit Unicode and guillemet-escaped components.
MODULE_SEGMENT = r"(?:[^\W\d][\w']*|«[^»\n]+»)"
MODULE_NAME = rf"{MODULE_SEGMENT}(?:\.{MODULE_SEGMENT})*"
IMPORT_COMMAND_RE = re.compile(
    rf"(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?({MODULE_NAME})(?![\w'.«])"
)


# First matching prefix owns a module; specific circuit layers precede Circuit.
# docs/library_layers.md describes the layers below ManyBody and Circuit;
# docs/import_structure.md describes ManyBody and Circuit.
LAYERS: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("sites", ("QICLean.ManyBody.Sites",)),
    ("dynamics", ("QICLean.ManyBody.Dynamics",)),
    ("hamiltonian", ("QICLean.ManyBody.Hamiltonian",)),
    ("manybody_entropy", ("QICLean.ManyBody.Entropy",)),
    ("subspace", ("QICLean.ManyBody.Subspace",)),
    ("replica", ("QICLean.ManyBody.Replica",)),
    ("gate", ("QICLean.Circuit.Gate",)),
    ("party", ("QICLean.Circuit.Party",)),
    ("algorithm", ("QICLean.Circuit.Algorithm",)),
    ("model", ("QICLean.Circuit.Model",)),
    ("compile", ("QICLean.Circuit.Compile",)),
    ("protocol", ("QICLean.Circuit.Protocol",)),
    ("simulation", ("QICLean.Circuit.Simulation",)),
    ("circuit", ("QICLean.Circuit",)),
    ("algebra", ("QICLean.Algebra",)),
    ("analysis", ("QICLean.Analysis",)),
    ("spectral", ("QICLean.Spectral",)),
    ("channel", ("QICLean.Channel",)),
    ("kraus", ("QICLean.Kraus",)),
    ("entropy", ("QICLean.Entropy",)),
    ("probability", ("QICLean.Probability",)),
    ("representation", ("QICLean.Representation",)),
)

# The layers designed for the many-body and circuit libraries, where no
# forwarding declaration is admitted (see check_pass_through_declarations.py).
# The many-body layers of regional entropy, subspaces and replicas hold modules
# moved from the single-system directories and keep their recorded forwarders.
NEW_LAYERS = frozenset({
    "sites", "dynamics", "hamiltonian", "gate", "circuit", "party", "algorithm", "model",
    "compile", "protocol", "simulation"
})
# Matrices of one system, maps between matrix algebras, and the systems of one or two
# parties that the many-body layers build on.
MATRIX = frozenset({"algebra", "analysis", "spectral"})
CHANNEL = frozenset({"channel", "kraus"})
SINGLE_SYSTEM = MATRIX | CHANNEL | {"entropy"}
ALLOWED: dict[str, frozenset[str]] = {
    # The single-system layers form a chain.
    "algebra": frozenset(),
    "analysis": frozenset({"algebra"}),
    "spectral": frozenset({"algebra", "analysis"}),
    "channel": MATRIX,
    "kraus": MATRIX | {"channel"},
    "entropy": MATRIX | CHANNEL,
    "probability": SINGLE_SYSTEM,
    "representation": SINGLE_SYSTEM | {"probability"},
    "sites": SINGLE_SYSTEM,
    "dynamics": SINGLE_SYSTEM | {"sites"},
    "hamiltonian": SINGLE_SYSTEM | {"sites", "dynamics"},
    "manybody_entropy": SINGLE_SYSTEM | {"sites", "dynamics", "hamiltonian"},
    # Subspaces and replicas of a many-body system are siblings.
    "subspace": SINGLE_SYSTEM | {
        "probability", "sites", "dynamics", "hamiltonian", "manybody_entropy"
    },
    "replica": SINGLE_SYSTEM | {
        "probability", "representation", "sites", "dynamics", "hamiltonian", "manybody_entropy"
    },
    "gate": MATRIX,
    "circuit": MATRIX | CHANNEL | {"sites", "gate"},
    "party": MATRIX | CHANNEL | {"sites", "gate", "circuit"},
    "algorithm": MATRIX | CHANNEL | {"sites", "gate", "circuit"},
    "model": MATRIX | CHANNEL | {"sites", "gate", "circuit"},
    "compile": MATRIX | CHANNEL | {"sites", "gate", "circuit", "model"},
    "protocol": MATRIX | CHANNEL | {"sites", "gate", "circuit", "model", "compile"},
    # QICLean #1062: simulation consumes both circuits and many-body evolution.
    "simulation": MATRIX | CHANNEL | {"sites", "gate", "circuit", "dynamics", "hamiltonian"},
}
DEBT: frozenset[str] = frozenset({})
DEEP_ROOTS: frozenset[str] = frozenset({"ManyBody", "Circuit"})
MUTUAL_DIRECTORIES: frozenset[str] = frozenset({})
EXAMPLES_IMPORTS: frozenset[str] = frozenset({})


def layer_of(module: str) -> str | None:
    """Return the layer that owns ``module``, or ``None`` if it is unconstrained."""
    for name, prefixes in LAYERS:
        for prefix in prefixes:
            if module == prefix or module.startswith(prefix + "."):
                return name
    return None


@functools.cache
def parse_module(source: str) -> tuple[tuple[str, ...], bool]:
    """Return the imported modules of a source and whether it is import-only.

    Comments and literal contents are removed first. Lexical errors fail closed
    rather than silently turning off enforcement for the affected module.
    The result is cached, since each check of this script reads every module.
    """
    uncommented, error = strip_lean_comments(source, mask_strings=True)
    if error is not None:
        raise ValueError(error)
    # Imports are header commands, not lines. Lean permits line breaks inside
    # an import and multiple import commands on one line. Never scan commands
    # or string contents after the header for apparent imports.
    remaining = uncommented.lstrip()
    for keyword in ("module", "prelude"):
        match = re.match(rf"{keyword}\b", remaining)
        if match:
            remaining = remaining[match.end():].lstrip()
    imports: list[str] = []
    while match := IMPORT_COMMAND_RE.match(remaining):
        imports.append(match.group(1).replace("«", "").replace("»", ""))
        remaining = remaining[match.end():].lstrip()
    return tuple(imports), bool(imports) and not remaining


def resolved_imports(sources: Mapping[str, str]) -> dict[str, set[str]]:
    """Return the ``QICLean`` modules each module with declarations depends on.

    An import-only module (an aggregator) has no entry, and an imported
    aggregator is replaced by the modules it re-exports, through nested
    aggregators.
    """
    parsed = {}
    for module, source in sources.items():
        try:
            parsed[module] = parse_module(source)
        except ValueError as error:
            raise ValueError(f"{module}: {error}") from error

    def reexports(module: str, seen: frozenset[str]) -> set[str]:
        imports, import_only = parsed.get(module, ((), False))
        if not import_only or module in seen:
            return {module}
        result: set[str] = set()
        for imported in imports:
            result |= reexports(imported, seen | {module})
        return result

    resolved: dict[str, set[str]] = {}
    for module, (imports, import_only) in parsed.items():
        if import_only:
            continue
        targets: set[str] = set()
        for imported in imports:
            if (imported == "QICLean" or imported.startswith("QICLean.")):
                targets |= reexports(imported, frozenset())
        resolved[module] = {target for target in targets if target.startswith("QICLean.")}
    return resolved


def violations(sources: Mapping[str, str]) -> set[str]:
    """Return every ``"A -> B"`` whose import points outside the allowed layers.

    ``A`` is any module that a layer owns. ``B`` is a module with declarations:
    an imported aggregator is replaced by the modules it re-exports, through
    nested aggregators.
    """
    found: set[str] = set()
    for module, targets in resolved_imports(sources).items():
        layer = layer_of(module)
        if layer is None:
            continue
        for target_module in targets:
            target = layer_of(target_module)
            if target is None or (target != layer and target not in ALLOWED[layer]):
                found.add(f"{module} -> {target_module}")
    return found


def directory_of(module: str) -> str | None:
    """Return the directory of a module, or ``None`` for one directly below ``QICLean/``.

    Directories are taken at depth two below the roots in ``DEEP_ROOTS`` and at
    depth one elsewhere.
    """
    parts = module.split(".")[1:-1]
    if not parts:
        return None
    depth = 2 if parts[0] in DEEP_ROOTS else 1
    return "/".join(parts[:depth])


def mutual_directories(sources: Mapping[str, str]) -> dict[str, tuple[str, str]]:
    """Return the pairs of directories that import each other.

    A key is ``"A <-> B"`` with ``A`` before ``B`` in sorted order.  Its value
    is one import from ``A`` into ``B`` and one from ``B`` into ``A``, each
    the first in sorted order, for the error message.
    """
    witness: dict[tuple[str, str], str] = {}
    for module, targets in sorted(resolved_imports(sources).items()):
        source_directory = directory_of(module)
        if source_directory is None:
            continue
        for target_module in sorted(targets):
            target_directory = directory_of(target_module)
            if target_directory is None or target_directory == source_directory:
                continue
            witness.setdefault(
                (source_directory, target_directory), f"{module} -> {target_module}"
            )
    return {
        f"{first} <-> {second}": (forward, witness[second, first])
        for (first, second), forward in witness.items()
        if first < second and (second, first) in witness
    }


def in_examples(module: str) -> bool:
    """Whether a module lies in a directory named ``Examples``."""
    return "Examples" in module.split(".")[1:-1]


def examples_imports(sources: Mapping[str, str]) -> set[str]:
    """Return every ``"A -> B"`` with ``B`` inside an ``Examples`` directory and ``A`` outside."""
    return {
        f"{module} -> {target}"
        for module, targets in resolved_imports(sources).items()
        if not in_examples(module)
        for target in targets
        if in_examples(target)
    }


def tracked_sources(root: Path) -> dict[str, str]:
    """Read the Git-tracked, non-archive Lean modules below ``QICLean/``."""
    result = subprocess.run(
        ["git", "-C", str(root), "ls-files", "-z", "--", "QICLean", "QICLean.lean"],
        check=True,
        stdout=subprocess.PIPE,
    )
    sources: dict[str, str] = {}
    for path in result.stdout.decode("utf-8").split("\0"):
        if (path != "QICLean.lean" and not path.startswith(PRODUCTION_ROOT)) or path.startswith(ARCHIVE_ROOT):
            continue
        if not path.endswith(".lean"):
            continue
        module = path[: -len(".lean")].replace("/", ".")
        if (root / path).is_file():
            sources[module] = (root / path).read_text(encoding="utf-8")
    return sources


def record_from_source(source: str, name: str) -> frozenset[str] | None:
    """Read the recorded set ``name`` from one revision of a checker.

    ``None`` means that the revision does not define ``name``.
    """
    tree = ast.parse(source)
    for statement in tree.body:
        if not isinstance(statement, (ast.Assign, ast.AnnAssign)):
            continue
        targets = statement.targets if isinstance(statement, ast.Assign) else [statement.target]
        if not any(isinstance(target, ast.Name) and target.id == name for target in targets):
            continue
        value = statement.value
        if (
            not isinstance(value, ast.Call)
            or not isinstance(value.func, ast.Name)
            or value.func.id != "frozenset"
            or len(value.args) != 1
            or value.keywords
        ):
            raise ValueError(f"{name} must be a literal frozenset")
        parsed = ast.literal_eval(value.args[0])
        if not isinstance(parsed, (set, dict)) or not all(isinstance(e, str) for e in parsed):
            raise ValueError(f"{name} must contain only literal strings")
        return frozenset(parsed)
    return None


def debt_from_source(source: str) -> frozenset[str]:
    """Read ``DEBT`` from one revision of this checker."""
    debt = record_from_source(source, "DEBT")
    if debt is None:
        raise ValueError("DEBT assignment not found")
    return debt


def records_at_merge_base(
    root: Path, base_ref: str, checker_path: str, names: Iterable[str]
) -> dict[str, frozenset[str] | None]:
    """Return the recorded sets ``names`` of a checker at the merge base with ``base_ref``.

    A value is ``None`` only while the set is first introduced: the checker, or
    the set in it, is absent from the base revision.
    """
    names = tuple(names)
    merge_base = subprocess.run(
        ["git", "-C", str(root), "merge-base", "HEAD", base_ref],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if merge_base.returncode != 0:
        raise ValueError(f"cannot find merge base with {base_ref}: {merge_base.stderr.strip()}")
    base_commit = merge_base.stdout.strip()
    return records_at_revision(root, base_commit, checker_path, names)


def records_at_revision(
    root: Path, revision: str, checker_path: str, names: Iterable[str]
) -> dict[str, frozenset[str] | None]:
    """Read the exact CI base, including the previous tip of a force-pushed branch."""
    names = tuple(names)
    commit = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "--verify", f"{revision}^{{commit}}"],
        capture_output=True, text=True,
    )
    if commit.returncode:
        raise ValueError(f"cannot resolve base revision {revision}: {commit.stderr.strip()}")
    base_commit = commit.stdout.strip()
    result = subprocess.run(
        ["git", "-C", str(root), "show", f"{base_commit}:{checker_path}"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    if result.returncode != 0:
        if "does not exist in" in result.stderr or "exists on disk, but not in" in result.stderr:
            return dict.fromkeys(names)
        raise ValueError(
            f"cannot read checker at base revision {base_commit}: {result.stderr.strip()}"
        )
    return {name: record_from_source(result.stdout, name) for name in names}


def ratchet_errors(
    current: frozenset[str],
    recorded: frozenset[str],
    base: frozenset[str] | None,
    *,
    new: str,
    stale: str,
    added: str,
    describe: Callable[[str], str] = str,
) -> list[str]:
    """Compare what the tree has with a recorded set that may only shrink.

    An entry of ``current`` that is not recorded gives the message ``new``, a
    recorded entry that is not current gives ``stale``, and, when the set at
    the base revision is known, a recorded entry absent from it gives ``added``.
    """
    errors = [f"{new}: {describe(entry)}" for entry in sorted(current - recorded)]
    errors += [f"{stale}: {entry}" for entry in sorted(recorded - current)]
    if base is not None:
        errors += [f"{added}: {entry}" for entry in sorted(recorded - base)]
    return errors


def check_layers(
    sources: Mapping[str, str],
    debt: frozenset[str] = DEBT,
    base_debt: frozenset[str] | None = None,
) -> list[str]:
    """Return the error messages of the layer check; an empty list means it passes."""
    return ratchet_errors(
        frozenset(violations(sources)),
        debt,
        base_debt,
        new="Import points outside the allowed layers",
        stale="Repaired import still listed in DEBT; remove it",
        added="Entry added to DEBT; this set may only shrink",
    )


def check_mutual_directories(
    sources: Mapping[str, str],
    recorded: frozenset[str] = MUTUAL_DIRECTORIES,
    base: frozenset[str] | None = None,
) -> list[str]:
    """Return the error messages of the check on directories that import each other."""
    current = mutual_directories(sources)

    def describe(pair: str) -> str:
        forward, backward = current[pair]
        return f"{pair} (by {forward} and {backward})"

    return ratchet_errors(
        frozenset(current),
        recorded,
        base,
        new="Directories import each other",
        stale=(
            "Directories no longer import each other but are listed in "
            "MUTUAL_DIRECTORIES; remove the pair"
        ),
        added="Pair added to MUTUAL_DIRECTORIES; this set may only shrink",
        describe=describe,
    )


def check_examples_imports(
    sources: Mapping[str, str],
    recorded: frozenset[str] = EXAMPLES_IMPORTS,
    base: frozenset[str] | None = None,
) -> list[str]:
    """Return the error messages of the check on imports of ``Examples`` modules."""
    return ratchet_errors(
        frozenset(examples_imports(sources)),
        recorded,
        base,
        new="Module outside Examples imports a worked example",
        stale="Removed import still listed in EXAMPLES_IMPORTS; remove it",
        added="Entry added to EXAMPLES_IMPORTS; this set may only shrink",
    )


RECORDS: tuple[str, ...] = ("DEBT", "MUTUAL_DIRECTORIES", "EXAMPLES_IMPORTS")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Reject upward imports, new mutually importing directories, "
        "and new imports of worked examples by library modules."
    )
    parser.add_argument("--root", type=Path, default=Path("."))
    base_options = parser.add_mutually_exclusive_group()
    base_options.add_argument("--base-revision", help="exact revision fixing the recorded entries (CI)")
    base_options.add_argument(
        "--base-ref",
        help="ref whose merge base with HEAD fixes the recorded entries that may remain",
    )
    parser.add_argument(
        "--print-debt", action="store_true", help="print the current layer violations and exit"
    )
    parser.add_argument(
        "--print-mutual-directories",
        action="store_true",
        help="print the current pairs of directories that import each other and exit",
    )
    parser.add_argument(
        "--print-examples-imports",
        action="store_true",
        help="print the current imports of worked examples by library modules and exit",
    )
    args = parser.parse_args()
    root = args.root.resolve()

    sources = tracked_sources(root)
    printed: Iterable[str] | None = None
    if args.print_debt:
        printed = violations(sources)
    elif args.print_mutual_directories:
        printed = mutual_directories(sources)
    elif args.print_examples_imports:
        printed = examples_imports(sources)
    if printed is not None:
        for entry in sorted(printed):
            print(f'        "{entry}",')
        return 0

    base: dict[str, frozenset[str] | None] = dict.fromkeys(RECORDS)
    if args.base_ref is not None or args.base_revision is not None:
        try:
            read_base = records_at_revision if args.base_revision else records_at_merge_base
            revision = args.base_revision or args.base_ref
            base = read_base(root, revision, CHECKER_PATH, RECORDS)
        except (SyntaxError, ValueError) as error:
            print(f"::error title=Import layer check failed::{error}")
            return 1

    errors = check_layers(sources, DEBT, base["DEBT"])
    errors += check_mutual_directories(sources, MUTUAL_DIRECTORIES, base["MUTUAL_DIRECTORIES"])
    errors += check_examples_imports(sources, EXAMPLES_IMPORTS, base["EXAMPLES_IMPORTS"])
    for message in errors:
        print(f"::error title=Import layer policy::{message}")
    if errors:
        print(
            "A lower layer must not import a higher one, two directories must not "
            "import each other, a module outside Examples must not import a worked "
            "example, and the recorded sets may only shrink. Move the shared "
            "declaration to a module both sides may import; see "
            "docs/import_structure.md."
        )
        return 1
    print(
        f"Import layers respected ({len(DEBT)} recorded violations, "
        f"{len(MUTUAL_DIRECTORIES)} recorded pairs of directories that import each "
        f"other and {len(EXAMPLES_IMPORTS)} recorded imports of worked examples remain)."
    )
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except ValueError as error:
        print(f"::error title=Import layer check failed::{error}")
        raise SystemExit(1)
