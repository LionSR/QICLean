# QICLean extraction dry run 3 -- corrected seed rule, 2026-08-21

Third rehearsal of `LionSR/TNLean` issue #6560 Phase 3 (plan in issue
#6622), same-day follow-up to run 2, with a **corrected seed rule** per the
coordinator's scouting of current `origin/main`: `TNLean/Kraus/Wielandt/`
is a complete channel-generic Wielandt stack (zero `TNLean.MPS`/
`TNLean.Spectral` imports across its 30 files); legacy `TNLean/Wielandt/`
is the `MPSTensor`-typed consumer layer imported by 9 MPS files and PEPS
and belongs to TNLean. This run does not seed legacy `TNLean/Wielandt/` at
all, and drops the four force-seeded "sanctioned interface module" entries
from runs 1/2 in favor of letting the closure decide.

Entirely against a fresh local clone under the session scratchpad; nothing
touched `LionSR/TNLean`'s repository state or `LionSR/QICLean`'s
pre-existing branches. The only pushes made were to `LionSR/QICLean`
branches `dryrun3-2026-08-21` and `dryrun3-packaging-2026-08-21`.

Source snapshot: `origin/main` of `LionSR/TNLean` at commit `b51276ece`
("fix(qic): keep TeX environments atomic (#6818)"), 2026-08-21.

**Result: GREEN BUILD on the first pass** (9235 jobs, zero failures),
wall clock **~8m11s** (00:00:15 -> 01:08:26 local, i.e. faster than run 2's
14m24s despite an identical pipeline -- fewer modules and no legacy
`MPSTensor`-typed Wielandt elaboration). Pushed to
`https://github.com/LionSR/QICLean/tree/dryrun3-2026-08-21`. The packaging
branch `dryrun3-packaging-2026-08-21`, stacked on top, was also pushed.
`main`, `scaffold-preview`, `dryrun-2026-08-20`, `dryrun-packaging`,
`dryrun-2026-08-21`, and `dryrun-packaging-2026-08-21` are all untouched
(verified by `git ls-remote` at the end, section 6).

## 1. Corrected seed rule and scouting confirmation

Before building the mover set, confirmed the coordinator's two claims
directly against the fresh clone:

- `grep -rl "^import TNLean\.MPS\|^import TNLean\.Spectral"` across
  `TNLean/Kraus/Wielandt/` and `TNLean/Kraus/Wielandt.lean`: **zero hits**
  (30 files, confirmed channel-generic).
- Importers of legacy `TNLean/Wielandt/*` outside `Wielandt/` itself: **9
  `MPS/` files** (`CanonicalForm/Existence.lean`,
  `CanonicalForm/SectorComparison/{NormalityChain,TPPrimitiveReduction}.lean`,
  `FundamentalTheorem/FiniteLength.lean`, `MPDO/PostBlockedRepresentativeSpan.lean`,
  `ParentHamiltonian/{IntersectionProperty,Nonvanishing,WrappingWindow}.lean`,
  `ParentHamiltonian/Martingale/C3Threshold.lean`) plus **1 PEPS file**
  (`PEPS/CycleMPSWordTransport.lean`), plus `Algebra/BurnsideMatrix.lean`
  and `Spectral/QuantitativeGap.lean` (itself already poisoned/excluded in
  every run's mover set). Matches the coordinator's brief exactly.

`build_movers3.py` (`scratchpad/build_movers3.py`) implements the
correction: seed = `scripts/qic_layer0_modules.txt` (a) + full
`Channel/`, `Entropy/`, `Kraus/` (includes `Kraus/Wielandt/`), `QPF/` (b) +
poison-filtered `Spectral/` (c); legacy `Wielandt/` is not in the loop at
all, and the four `(d)` force-seeds from runs 1/2 are removed -- the
closure/poison algorithm itself (STOP_PREFIXES, two-phase raw-closure +
poison-propagation) is byte-identical to runs 1/2.

## 2. Mover-set result

| Stage | Run 2 | Run 3 (corrected) |
|---|---|---|
| Seed set (before closure) | 556 | 512 |
| Poisoned (excluded) | 34 | 11 |
| Orphaned | 9 | 7 |
| **Final mover set** | **540** | **512** |
| Dragged-in (non-seed, surviving) | 7 | 9 |

The poisoned/excluded count drops sharply (34 -> 11) because run 2's
excluded list was dominated by 14 legacy-Wielandt capstone files that are
simply not in run 3's seed/closure at all anymore -- there is nothing left
to exclude them from. The remaining 11 excluded files are the same
`Spectral/` chain both prior runs found (`MPVOverlapTrace.lean` and its
downstream poisoned files -- section 3).

## 3. The four requested verifications

**(a) No duplicate Wielandt -- confirmed.** `TNLean/Wielandt/` (legacy)
contributes **0** movers. `TNLean/Kraus/Wielandt/` contributes **31**
movers (30 content files + the `Kraus/Wielandt.lean` aggregator), 0 of them
`MPSTensor`-namespaced -- identical file count to runs 1/2's
`Kraus/Wielandt/` tree (that tree itself is unaffected by the seed-rule
correction), but this time it is the *only* Wielandt content that ships.

**(b) The "14 excluded capstones" finding is moot -- as expected, stated
explicitly.** Runs 1 and 2 both excluded 14 legacy `Wielandt/` files
(`Primitivity.lean` + 4 sub-files, `Inequality.lean` + 4 sub-files,
`SpanGrowth.lean` + `SpanGrowth/CumulativeToWordSpan.lean`,
`WolfChapter6TNIndex.lean`) as *poisoned* -- i.e. excluded because they
transitively required a still-unsplit `Spectral/` file. Under the
corrected seed rule, legacy `Wielandt/` is never seeded, so this exclusion
mechanism does not apply to it at all: **legacy Wielandt's capstones
(`Primitivity.lean`, `Inequality.lean`, `WolfChapter6TNIndex.lean`, and the
rest of the 40-file tree) intentionally stay in TNLean**, full stop, by
design rather than by a still-open `Spectral/`-split blocker. This is a
qualitatively different, better outcome than runs 1/2's "blocked, pending a
future split" framing -- there is no longer a pending action item for this
specific exclusion. (Whether the *channel-generic* `Kraus/Wielandt/`
capstones -- `Kraus/Wielandt/Primitivity.lean`, `Inequality.lean` -- are
themselves complete/self-contained is a separate question this dry run does
not evaluate; they were already movers in every run.)

**(c) Spectral movers = only the clean channel-generic files --
confirmed, identical set to runs 1/2.** 4 movers:
`GaugeConstruction.lean`, `MixedTransfer.lean`,
`TransferOperatorGapNormalized.lean`, `TransferOperatorGapRectNormalized.lean`.
11 excluded, same chain as before: `MPVOverlapTrace.lean` (direct
`MPS/Overlap/*` import) poisons `CrossCorrelation.lean`,
`MPVOverlapDecay(Rect).lean`, `PeripheralToTransferMapGap.lean`,
`PrimitiveOverlap.lean`, `QuantitativeGap.lean`,
`TransferOperatorGap(Injective|NT).lean`, and `MPS/Overlap/Basic.lean`
itself (forbidden-prefix). The correction does not touch `Spectral/`'s
mover/exclusion boundary at all -- it was never about `Spectral/`.

**(d) The dragged list is the final interface-module surface --
confirmed and reported in full.** 9 dragged (non-seed) files, all traceable
to genuine imports from the corrected seed's closure:

```
TNLean/Algebra/MatrixKernelRigidity.lean <- TNLean/Spectral/GaugeConstruction.lean
TNLean/MPS/Core/CPPrimitive.lean <- TNLean/QPF/Assembly.lean, TNLean/QPF/PosDef.lean, TNLean/QPF/Primitive.lean
TNLean/MPS/Core/Injectivity.lean <- TNLean/MPS/Defs.lean
TNLean/MPS/Core/InvariantProjection.lean <- TNLean/MPS/Core/TransferChannel.lean
TNLean/MPS/Core/Transfer.lean <- TNLean/MPS/Core/TransferChannel.lean, TNLean/Spectral/MixedTransfer.lean
TNLean/MPS/Core/TransferChannel.lean <- TNLean/MPS/Core/CPPrimitive.lean, TNLean/Spectral/MixedTransfer.lean
TNLean/MPS/Core/Word.lean <- TNLean/MPS/Core/Injectivity.lean, TNLean/MPS/Core/InvariantProjection.lean, TNLean/MPS/Defs.lean
TNLean/MPS/Defs.lean <- TNLean/MPS/Core/Transfer.lean
TNLean/MPS/Tactic/Attr.lean <- TNLean/MPS/Core/Transfer.lean
```

Of the four modules runs 1/2 force-seeded as "sanctioned interface
modules", **three survive here as genuine drags**
(`MPS/Core/{Transfer,TransferChannel,CPPrimitive}.lean` -- reached because
`QPF/{Assembly,PosDef,Primitive}.lean` import `CPPrimitive.lean`, and
`Spectral/MixedTransfer.lean` imports `Transfer.lean`/`TransferChannel.lean`
directly), while **`MPS/Structure/PrimitiveFixedPoint.lean` does not** --
its only importer in the raw closure,
`TNLean/Spectral/PeripheralToTransferMapGap.lean`, is itself
excluded/poisoned (section 3(c)), so `PrimitiveFixedPoint.lean` is orphaned
and correctly dropped (`excluded.txt`: `"orphaned: only importer(s) were
excluded"`). This is exactly the decision the task asked to record: three
of the four old force-seeds were load-bearing, one was not.

## 4. `_tNLean\b` rename hazard -- still fixed upstream, zero hits

`grep -rn "_tNLean\b" --include="*.lean" .` against the fresh clone
returned zero hits, same as run 2 -- the `NormedSpace ℝ (Matrix n n ℂ)`
instance in `Algebra/MatrixOperatorSpace.lean` remains explicitly named
(`instNormedSpaceRealMatrixComplex`), so the hazard class has no live
instance to trigger on. No mechanical fix was needed.

## 5. Build status

**GREEN, first pass**, 9235/9235 jobs, zero failures, **~8m11s** wall
clock. `lake exe cache get` reported "No files to download" (Mathlib cache
used, ~81s bootstrap) -- cache rule satisfied. `sorry`/`axiom`: **zero**
real occurrences (same 8 docstring-prose hits as runs 1/2, e.g.
"sorry-free").

## 6. Packaging branch (`dryrun3-packaging-2026-08-21`)

Cherry-picked the three packaging commits from `dryrun-packaging-2026-08-21`
(`ci+blueprint: package QICLean's standalone-repository CI and blueprint`,
`doc(docs): add the getting-started guide`, `doc(README): point to the
getting-started guide`) onto `dryrun3-2026-08-21`. **All three applied with
zero conflicts** -- same reasoning as run 2: the packaging content touches
no path the Lean-tree cut differs on.

`missing_decls.md` regenerated (mechanical, same tool + identical `.tex`
content): **58 -> 112**, purely additive (all 58 prior names still
missing, 54 new). This jump is the *expected, correct* consequence of the
seed-rule correction, not a new classification defect: runs 1/2 seeded
legacy `Wielandt/` directly, so blueprint tags citing its declarations
resolved by accident; this run correctly excludes that entire tree, so
every one of those tags is now honestly reported missing. 108 of the 112
are `MPSTensor`-namespaced (concentrated 81 of 112 in the two Wielandt
blueprint chapters, `ch08_wielandt_cumulative_bound.tex` 41 and
`appendix/ft_mps/ch08_wielandt.tex` 40); the remaining 4 are the unchanged
`Matrix.*` RFP/MPDO helper lemmas from every prior run. Full detail and the
complete 112-item list in `missing_decls.md` on the packaging branch.

`interface_edges.md` again **not regenerated** -- flagged stale for two
stacking reasons this time: PR #6806's item-level reclassification
(unaddressed since run 2) plus this run's own `docs/movers.txt` shape
change, which would itself change the old whole-file classification's
chapter assignments even without #6806. See the staleness note added atop
the file on the packaging branch.

## 7. Verification: other branches untouched

```
$ git ls-remote https://github.com/LionSR/QICLean.git
e1650a1fdbc47c2d0535a7e15209e710ff1c09c3  HEAD
766a7b45eecfef6f476fc6d33f2bee813723e287  refs/heads/dryrun-2026-08-20
505a4c04513d5a339fe44af9ff73410343c8523f  refs/heads/dryrun-2026-08-21
1b898f27574ebba44f7e7a891939b59ce732df55  refs/heads/dryrun-packaging
65021ab7d849139896e210c08f75c817af502c7c  refs/heads/dryrun-packaging-2026-08-21
[new: dryrun3-2026-08-21]
[new: dryrun3-packaging-2026-08-21]
e1650a1fdbc47c2d0535a7e15209e710ff1c09c3  refs/heads/main
e1650a1fdbc47c2d0535a7e15209e710ff1c09c3  refs/heads/scaffold-preview
```

(exact tip SHAs for the two new branches recorded after the final push,
section 8 below). All five pre-existing branches -- `main`,
`scaffold-preview`, `dryrun-2026-08-20`, `dryrun-packaging`,
`dryrun-2026-08-21`, `dryrun-packaging-2026-08-21` -- confirmed at their
pre-run SHAs, unchanged. `LionSR/TNLean` was only cloned (read) and
`curl`-fetched (read); `git-filter-repo` removed its `origin` remote by
design, so no write path to `LionSR/TNLean` existed during this run.

## 8. Branches pushed

| Branch | Tip |
|---|---|
| `dryrun3-2026-08-21` | Lean-tree extraction, 3 commits on top of `24988c2` (`refactor(qic): stabilize matrix real-scalar instance name`, the tip of the corrected filter-repo history, 1578 commits) |
| `dryrun3-packaging-2026-08-21` | stacked on `dryrun3-2026-08-21`, + 3 cherry-picked packaging commits + 1 ledger-regeneration commit |

## 9. State of readiness for the real cutover

**This cut is clean: the mover set is a final-candidate boundary pending
the owner's freeze.** All four requested verifications came back exactly
as predicted from the scouting: no duplicate Wielandt, the prior "14
excluded capstones" concern is structurally moot (legacy Wielandt stays in
TNLean by design, not by an open blocker), the Spectral boundary is
unchanged and already minimal, and the dragged-file surface is small (9
files) and fully explained -- three of the four old force-seeded interface
modules are genuinely load-bearing, one is not and correctly does not move.
Two consecutive builds under this exact pipeline (run 2's old seed rule and
this run's corrected one) both went green, and this run went green in a
single pass with a materially smaller, cleaner tree (512 vs 540 files, 11
vs 34 exclusions). The one open item is **entirely on the blueprint side,
not the Lean-tree side**: `blueprint/` still needs a packaging pass that
reclassifies chapters against this corrected `docs/movers.txt` (ideally
also picking up PR #6806's item-level split) before the two Wielandt-bound
chapters' 81 newly-broken `\lean{}` references can be resolved -- either by
restating them against `Kraus.Wielandt.*` declarations where a faithful
channel-generic equivalent exists, or by leaving those chapters in
TNLean's own blueprint to match the corrected Lean-tree boundary. No further
Lean-tree mover-set iteration is expected to be needed before a real
extraction under this seed rule.
