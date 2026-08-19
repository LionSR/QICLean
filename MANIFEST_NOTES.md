# QICLean extraction manifest — current best-known state

Source: issue [#6560](https://github.com/LionSR/TNLean/issues/6560)
("Tracking: quantum-channel layer extraction") and its migration-plan
comments, cross-checked against the current TNLean tree at `de295511d`
(2026-08-19). This note is a summary of a moving target — the issue is an
open tracking issue under active scouting, and several boundary decisions
below were revised more than once across the comment thread. Treat the file
lists here as the current best estimate, not a frozen manifest; regenerate
against the live comment thread and tree before executing any extraction
step.

## 1. Directories moving wholesale

- **`Channel/`** — the finite-dimensional quantum-channel theory itself
  (Wolf Ch. 2–7): Kraus/Choi/Stinespring representations, Schwarz
  inequalities, fixed points, irreducibility, peripheral spectrum,
  semigroups, KoashiImoto. **Exception**: `Channel/PositiveSkolemNoether.lean`
  physically lives in this directory but is consumed only by
  `MPS/FundamentalTheorem`; it is reassigned OUT of the channel tree and
  stays in TNLean despite the directory-wide move. Do not treat "lives under
  `Channel/`" as sufficient evidence a file moves.
- **`Entropy/`** — classical/quantum entropy and recovery theory. Confirmed
  100% TN-free by the boundary survey; moves without qualification.
- **`Wielandt/`** — quantum Wielandt theory (span-growth, rank-one
  extraction, rectangular span, primitivity equivalences). Added to the
  QICLean boundary by a later maintainer comment (`Boundary update`), after
  the issue's original nine-bullet plan, which covered only `Channel/` and
  `Entropy/`. All 45 files (39 substantive + 6 generated import
  aggregators) classify as clean movers; zero files cite genuinely
  TN-state-flavored vocabulary (`SameMPV`, `GaugeEquiv`, `mpv`) in their
  proofs, even though several sit under directory names that suggest
  otherwise (`Primitivity/*` imports resolve to `IsIrreducibleTensor`/
  `IsPrimitiveMPS`-style Kraus-flavored declarations, not tensor-state ones).
  `Wielandt/` is proof-complete (zero `sorry`/`axiom`, zero
  Unfaithful/Scope-restriction markers) — the migration is a pure refactor.
- **The word-evaluation layer, as a new `Kraus/` directory** — not an
  existing directory today. Per the phase-1b scout's final decision, the
  WORD half of `MPS/Defs.lean` (`evalWord` and its variant lemmas,
  `IsInjective`, `IsNBlkInjective`, `IsNormal`, `reindexPhysical`) plus five
  whole files (`MPS/Core/{Transfer,BlockingTransfer,CPPrimitive,
  TransferChannel,OrthogonalProjectionInvariance}.lean`) plus split
  fragments of `MPS/Core/{RepeatedWord,Blocking,MultiBlock,TPGauge}.lean`
  plus `IsIrreducibleTensor`/`HasInvariantProj` (currently in
  `MPS/CanonicalForm/Reduction.lean`) land in a new top-level
  `TNLean/Kraus/` directory first (an in-repo move, decided but not yet
  executed as of the last read comment), which becomes `QICLean/Kraus/` at
  extraction. **Naming caveat**: the declarations physically move into
  `Kraus/` while *keeping* `namespace MPSTensor` — a full rename to
  `namespace Kraus` was originally planned but was revised after a dry-run
  measured ~429 consumer files touched by the rename (vs. 28 direct
  importers of `MPS.Defs`), so the physical move and the namespace rename
  are now decoupled; the rename is deferred to a single mechanical sweep
  scheduled with the extraction-time module-prefix rename. `IsIrreducibleTensor`
  keeps its name outright (72 call-site files).
- **`Analysis/`** — moves wholesale (66 files). Verified: no file imports
  any tensor-network module or mentions state-level identifiers; the three
  files with non-foundation imports (`Entropy`, `EntropyMarkovForward`,
  `OperatorConvexity`) import from `Channel/`, which moves with them.
- **`Topology/`** — moves wholesale (the Brouwer fixed-point chain, with the
  `Gametheory` (`LionSR/Brouwer`) Lake dependency moving alongside it —
  QICLean's quantum Perron-Frobenius existence argument is its only
  consumer, so TNLean drops the `Gametheory` require entirely once this
  lands).
- **Most of `Algebra/`** — the rest of the directory "follows the import
  closure" once the four staying files below are pulled out; namespace
  cleanup (`namespace MPSTensor` blocks inside otherwise-generic Algebra
  files) was already applied by an earlier sweep PR. See §2 for the
  confirmed stay-list.
- **`QPF/`** — all four files move cleanly (`PosDef.lean`, `Uniqueness.lean`,
  `Assembly.lean`, `Primitive.lean`) — no split, no stay list.
- **`~8 Spectral/` files** — matches the task's estimate for the files that
  move *cleanly*: `MixedTransfer.lean`, `TraceExpansion.lean`,
  `FrobeniusNorm.lean`, `Radius.lean`, `TransferOperatorGapCommon.lean`,
  `TransferOperatorGapNormalized.lean`, `TransferOperatorGapRectNormalized.lean`,
  `QuantitativeGap.lean` — exactly 8 of the directory's 18 files. **This
  figure is a floor, not the whole `Spectral/` disposition** — see §3.

## 2. Stay-list exceptions (confirmed)

The fundamental-theorem algebra cluster stays in TNLean even though its
statements are generic algebra, because its *consumers* are exclusively
tensor-network proof machinery:

- `Algebra/SkolemNoether.lean`, `Algebra/CornerSkolemNoether.lean`,
  `Algebra/IrreducibleTensorAction.lean`, `Algebra/GramMatrixLI.lean`,
  `Algebra/MatrixAlgEquiv.lean` — tensor-network-side consumers only, stay.
  (`CornerSkolemNoether` was on an earlier "+10 blueprint-driven movers"
  list in an intermediate draft; the final correction removes it from that
  list and keeps it on the stay side — the blueprint entry follows the
  declaration.)
- `Algebra/TracePairing.lean`, `Algebra/BurnsideMatrix.lean`,
  `Algebra/ProjectionTriangularTrace.lean`, `Algebra/BlockTriangularTrace.lean`
  — the four files whose import of MPS modules keeps them out of the move
  set. (Do not confuse `BurnsideMatrix.lean`, which imports
  `MPS.CanonicalForm.Reduction` and stays, with `Algebra/BurnsideTheorem.lean`,
  a distinct, Mathlib-only file with no TNLean imports that `BurnsideMatrix.lean`
  itself imports — `BurnsideTheorem.lean` moves cleanly.)
- `Spectral/MPVOverlapTrace.lean` — stays whole in TNLean as a structural
  bridge: every theorem's conclusion is stated as `= mpvOverlap ...`, the
  TNLean-owned quantity, so keeping it TN-side means `Channel.TransferMatrix`
  becomes a state→channel import (the expected direction) rather than
  requiring a split.
- The **state halves of the split `Spectral/` files** — see §3 for the
  six files that split rather than move or stay outright; their
  `mpvOverlap`/`GaugePhaseEquiv`-concluding halves stay in TNLean and cite
  the moved channel halves.

**Not on the task's stay-list but confirmed shared/split, worth flagging as
a refinement**: `Algebra/SkolemNoetherUnitary.lean` and
`Algebra/BlockPermutation.lean` are "genuinely shared" per the final
comment — `Channel/FixedPoint` consumes them for the Wolf 6.14
fixed-point-algebra structure theorem, and since QICLean cannot import back
from TNLean, the textbook *cores* (the Skolem–Noether theorem for matrix
algebras, the block-ideal machinery) move to QICLean while the
fundamental-theorem *application* layers stay in TNLean, importing the
moved cores across the package boundary. This is a third disposition
(split by role, not by file) that the task's flat stay-list does not
distinguish from the five outright-stay files above — treat
`SkolemNoetherUnitary`/`BlockPermutation` as "core moves, application
layer stays," not as either fully in or fully out.

## 3. `Spectral/` — the fuller picture behind "~8 files"

The task's "~8 Spectral files" stay-list framing describes only the clean
movers (§1). The full 18-file directory disposition, per the boundary
survey's Part 4 table, is:

| Disposition | Files |
|---|---|
| **Move cleanly** (8, counted above) | `MixedTransfer`, `TraceExpansion`, `FrobeniusNorm`, `Radius`, `TransferOperatorGapCommon`, `TransferOperatorGapNormalized`, `TransferOperatorGapRectNormalized`, `QuantitativeGap` |
| **Delete** (empty shims / dead code) | `TransferOperatorGap.lean`, `TransferOperatorGapRect.lean` (shims — downstream importers repoint to the concrete file they actually need), `MPVOverlapDecay.lean` (dead compatibility shim, no declarations) |
| **Split** (6) | `TransferOperatorGapInjective.lean`, `TransferOperatorGapNT.lean`, `GaugeConstruction.lean`, `CrossCorrelation.lean`, `MPVOverlapDecayRect.lean`, `PrimitiveOverlap.lean` — each has a channel-generic half that moves and a `mpvOverlap`/`GaugePhaseEquiv`-concluding half that stays, with the stay half importing the move half |
| **Stay whole (bridge)** | `MPVOverlapTrace.lean` (§2) |

`QPF/`'s four files are simpler: all move cleanly, no split, no stay
entries (unlike `Spectral/`).

An open question flagged but not resolved in the comment thread: whether
`IsInjective` and `IsIrreducibleTensor` (defined in `MPS/Defs.lean` and
`MPS/CanonicalForm/Reduction.lean` respectively, both channel-vocabulary by
content but currently TNLean-hosted) move to QICLean. The 6-file split
list above and every "moves cleanly" verdict in `QPF/`/`Spectral/QuantitativeGap.lean`
take these as hypothesis types, so their eventual home determines whether
those files are truly free of a TNLean dependency or pick up a
channel→state import for their hypotheses. Per §1, the phase-1b decision
already answers this for the two named predicates by moving them into the
new `Kraus/` directory — but that decision post-dates the Spectral/QPF
survey and was not re-propagated into it as of the last read comment.

## 4. `Axioms/` — "dissolving," with a caveat

The task brief frames `Axioms/` as being dissolved. The clearest statement
in the comment thread is narrower: "`Topology/` ... and `Axioms/` move
likewise" (i.e., the directory's four files —
`BrouwerFixedPoint.lean`, `Entropy.lean`, `LiebSubBoundary.lean`,
`OperatorConvexity.lean` — move to QICLean as a unit, the same as any other
foundation directory). Nothing in the read comments describes files being
redistributed out of the directory or the directory disappearing as a
physical location.

What *is* independently true of the current tree, and is likely the source
of "dissolving": **zero of the four files contain a live `axiom`
declaration** — `grep -rn "^axiom " TNLean/Axioms/*.lean` returns nothing.
`Entropy.lean`'s own docstring records that strong subadditivity is "no
longer axiomatized." `docs/import_structure.md`'s description of `Axioms/`
as "axiomatized inputs" is stale prose, not current fact, and is called out
as needing a fix during the split. So "dissolving" is accurate as a
statement about the directory's *conceptual* status (it no longer holds
axioms, only proven theorems under historical names) but not as a
statement about the directory being broken up file-by-file — as read, the
four files travel together to QICLean, keeping their historical names,
with an open decision on whether to rename them at extraction.

One layering caveat carried with the move: `Axioms/BrouwerFixedPoint.lean`
imports `Channel/DensityRetract.lean`, so inside QICLean, `Axioms/` is not
strictly below `Channel/` in the layer ordering the way TNLean's
`docs/import_structure.md` table currently implies — never move `Axioms/`
without `Channel/` in the same step.

## 5. Inconsistencies found relative to the task brief

1. **"Channel/ moves wholesale" has one confirmed exception**:
   `Channel/PositiveSkolemNoether.lean` reassigns out of the channel tree
   (§1). A directory-level move list must special-case this file.
2. **`SkolemNoetherUnitary`/`BlockPermutation` are neither move nor stay**:
   they split by role (core moves, FT-application layer stays), a third
   category the task's flat stay-list collapses into the same bucket as
   the five outright-stay Algebra files (§2).
3. **"~8 Spectral files" undercounts the directory's true disposition**:
   the fuller picture is 8 clean movers + 2 dead-shim deletions + 6 files
   that split + 1 file that stays whole as the sanctioned bridge (§3).
4. **`Axioms/` "dissolving" is stronger than what the comment thread
   states**: the thread says the directory moves likewise to the other
   foundation directories; the more defensible reading of "dissolving" is
   that the directory's *axiomatized-inputs* framing is obsolete (all four
   files hold proven theorems), not that the directory is being broken up
   (§4).
5. **The boundary itself grew mid-thread**: the issue's original nine-bullet
   plan covers only `Channel/` and `Entropy/`; `Wielandt/` (and by
   extension the Analysis/Topology/most-of-Algebra/QPF/Spectral foundation
   closure this note describes) was added by a later maintainer comment
   reassigning it to QICLean, "together with the analysis results already
   in the moving closure." A reader of the issue body alone, without the
   comment thread, would reconstruct a materially smaller boundary than the
   one this manifest describes.
6. **The `Kraus/` namespace plan reversed once already**: the original
   phase-1b write-up planned an immediate rename to `namespace Kraus` for
   the moved word-evaluation declarations; a later comment in the same
   thread revised this after measuring the true consumer-file cost
   (~429 files, not the 28-file figure the original plan used), decoupling
   the physical move (keeps `namespace MPSTensor`) from the rename (deferred
   to extraction time). A manifest snapshot taken before that revision
   would describe a `namespace Kraus` layout that is no longer the plan.
