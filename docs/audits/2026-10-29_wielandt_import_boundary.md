# Quantum-Wielandt import boundary (issue #525)

Base: `87cb104a853153751bc4932cf3c55427a1d99724`.
Issue: https://github.com/LionSR/QICLean/issues/525.

`StronglyIrreducibleToFullWordSpan.lean` uses the fixed-density theorem from
`Channel.Irreducible.Ergodicity` and the complementary eigenvalue bound from
`Channel.Peripheral.IrreducibleChannel`. Import those owners in place of
`Channel.Semigroup.Primitivity.IrreducibleAnalysis`.

Every declaration, statement, and docstring is preserved. At this revision,
compilation of the two-import substitution alone fails on
`ne_zero_of_mem_densityMatrices'`, which is actually owned by
`Channel.Semigroup.Primitivity.Helpers`. Replace that single proof argument
with `fun hρ_zero => htr_ne (by simp [hρ_zero])`, deriving the same nonzero
fact from the already established nonzero trace. All other non-import bytes
are unchanged. No hypothesis or mathematical bound changes.
No dependency source, pin, toolchain, or file changed by PR #974 is modified.
The added test guards the actual public theorem's transitive logical axioms.

## Current import-cone measurement

Count recursive **QICLean prerequisite modules**, excluding the target itself
and external packages: **122 before, 100 after; 22 removed (18.0%)**, none added.
The issue's older 115-to-77 measurement is not a measurement of this revision.
Other direct imports are retained: each either supplies a used declaration or
removing it leaves the complete explicit transitive import cone unchanged.

This change does not eliminate all semigroup/Lindblad prerequisites at this
revision. For example, the required owning module still imports
`Channel.FixedPoint.MeanErgodicProjection`, which imports `Channel.Semigroup.CPClosure`.
Narrowing those dependencies is outside this change's scope.

Reproduce the QICLean counts from the repository root:

```python
import re
import subprocess
import sys
from pathlib import Path
sys.path.insert(0, "scripts")
from lean_import_syntax import strip_lean_comments

base = "87cb104a853153751bc4932cf3c55427a1d99724"
path = Path("QICLean/Kraus/Wielandt/Primitivity/StronglyIrreducibleToFullWordSpan.lean")
def imports(text):
    text, error = strip_lean_comments(text)
    assert error is None
    return re.findall(r"^import\s+(\S+)", text, re.M)
graph = {".".join(p.with_suffix("").parts): imports(p.read_text())
         for p in Path("QICLean").rglob("*.lean")}
def cone(roots):
    seen, todo = set(), list(roots)
    while todo:
        module = todo.pop()
        if module.startswith("QICLean.") and module not in seen:
            seen.add(module)
            todo.extend(graph[module])
    return seen
old = subprocess.check_output(["git", "show", f"{base}:{path}"], text=True)
before, after = cone(imports(old)), cone(imports(path.read_text()))
print(len(before), len(after), len(before - after), len(after - before))
print("\n".join(sorted(before - after)))
```

## Validation

- Pinned Lean `v4.35.0-rc3`; Mathlib
  `c55e6e786f49471c72fbddbec5415808896aec1e`. All dependency checkouts match
  the unchanged manifest. Setup fetched Mathlib artifacts successfully;
  `lake --no-build build` of the target cone's 113 direct Mathlib import roots
  passed (3176 jobs). Build logs contain no rebuilt Mathlib source modules.
- Separate worktree with private copied package/build artifacts; the original
  checkout and all shared dependency sources remain unchanged.
- Baseline target build passed (9085 jobs); revised target build passed
  (9063 jobs). Each command used `lake --fail-fast build` of the target,
  guarded by a 600-second timeout with interrupt and forced-kill grace period.
  Existing Brouwer dependency deprecation warnings were replayed; the changed
  production source and new fixture pass strict checks without warnings.
- Strict target elaboration and the new axiom fixture passed with `-j1`,
  `autoImplicit=false`, `relaxedAutoImplicit=false`, `pp.unicode.fun=true`,
  `maxSynthPendingDepth=3`, `linter.mathlibStandardSet=true`, and
  `warningAsError=true`. The actual theorem reports exactly
  `[propext, Classical.choice, Quot.sound]` before and after.
- Source preservation (all bytes except the imports and the explicitly
  identified nonzero proof argument), forbidden-proof-token scan, Lean line
  widths, generated-import check, and `git diff --check` passed.

## Current target timings and limits

Sequential strict target elaborations in the same isolated worktree with
warmed prerequisite artifacts, `LEAN_NUM_THREADS=1` and `-j1`; no concurrent
Lean/build/source-check workload. Each sample invokes `lake env lean` with
all strict flags above, so wall time includes Lake startup and import loading.
Three baseline samples were followed by three candidate samples. Both source
variants were elaborated directly; target artifacts were not used to skip work.

| Source | Wall seconds, three samples | Median seconds |
| --- | --- | --- |
| baseline | 9.050, 8.934, 8.744 | 8.934 |
| candidate | 8.793, 9.822, 9.438 | 9.438 |

These fixed-order samples establish no wall-time speedup; the candidate median
is higher. They are not a cold-cache benchmark or a statistical performance
claim. The proven saving here is the 22-module prerequisite reduction. Initial
baseline dependency compilation and the incremental candidate build have
unequal cache states and are not used as a before/after timing comparison.
No historical issue timings are claimed as current measurements.

A full root `lake build` was not run under the delegated scope's prohibition
on costly broad evaluations. Full-library/downstream compatibility is therefore
not claimed. The import-only trial's missing-helper failure was corrected by
the documented one-argument proof change before the successful final checks.
Raw command logs and per-run JSON remain in `/tmp/qic525/` in this environment.
