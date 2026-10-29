# Wolf Theorem 6.7: positive-map equivalences

Source contract: [issue 479](https://github.com/LionSR/QICLean/issues/479),
[Wolf Chapter 6, lines 835–890](https://github.com/LionSR/QICLean/blob/87cb104a853153751bc4932cf3c55427a1d99724/Notes/WolfNoteTexSource/ch06_spectral_properties.tex#L835-L890).
Ownership was checked before editing: the issue was open, unassigned, and had
no comments; no open pull request claimed this theorem. Work is isolated on
`codex/wolf-theorem67`, based on `87cb104a853153751bc4932cf3c55427a1d99724`.

## Result

`QICLean/Channel/WolfTheorem67.lean` proves
`WolfTheorem67.wolf_theorem_6_7_tfae` for an arbitrary complex-linear positive
trace-preserving map on `M_D(ℂ)`, with `D ≥ 1`. It assumes neither complete
positivity nor a Schwarz inequality. All four source conditions occur in its
statement; the spectral clause explicitly includes
`T.charpoly.rootMultiplicity 1 = 1`.

The algebraic-multiplicity equivalence uses maximal generalized eigenspaces,
not only ordinary eigenvectors. Positive iterate indices in the irreducibility
clause satisfy `k > 0`; the positivity-power witness can be zero. A separate
result proves uniform eventual positivity, with one threshold for every
later exponent and every density matrix. The convergence-to-uniformity step
first extends convergence to all matrices, then uses finite-dimensional
operator-norm convergence and compactness of the density matrices. For the
recurrent projection, compactness is used on the image of the whole density
set; strict positivity itself is not treated as closed.

The theorem and four predicates are documented in the Blueprint. The
numbering coverage is updated. The resolved source-convention note is
`docs/paper-gaps/wolf_theorem67_positive_iterates.tex`. Theorem 6.8 and all
existing production modules remain mathematically unchanged; the generated
channel aggregator only adds the new import. No files implementing issue 477
were edited.

## Validation

Lean is pinned to `v4.35.0-rc3`; Mathlib is pinned to
`c55e6e786f49471c72fbddbec5415808896aec1e`. The isolated worktree reuses the
exact pinned package checkout and its cache. `lake exe cache get` succeeded
with no files to download, and `lake --no-build build @mathlib` confirmed all
Mathlib targets up to date before the mathematical builds. No Mathlib Lean
source module was rebuilt. The text-linter executable did compile native
object files from cached generated C artifacts.

Passed:

- `lake build QICLean.Channel.WolfTheorem67`.
- The standard `scripts/ci_lean_checks.py` `run_batch` runner, explicitly
  targeting the new production module and its two test files: three files,
  zero failures. This uses `-j1`, disabled automatic implicits, the standard
  Mathlib linters, and warnings as errors. It is a focused check, not the
  full changed-module/aggregator or repository-wide strict suite.
- Seven guarded foundation checks, covering every new public theorem. Each
  theorem uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
- Boundary applications to transposition, the identity on `M_2(ℂ)` with
  multiplicity four at `1`, failure of zeroth-iterate irreducibility on
  `M_2(ℂ)`, and a zeroth positivity witness on `M_1(ℂ)`.
- Blueprint/source synchronization and compilation of all eleven new
  Blueprint declaration references through an import of the actual module.
- `lake exe lint_style`; generated imports; numbered-module and module-size
  policies; changed reader-facing prose; whitespace checks.
- Twenty-five tests for the module policy and import-generator scripts.
- The existing TNLean tactic-pattern scanner run read-only against the
  channel source tree; the normalization/convergence pattern was recorded
  in QICLean's existing ledger. No new tactic is needed.

Full library compilation, the repository-wide strict suite, and full
`leanblueprint checkdecls` were not run. Targeted checks above establish the
new theorem's elaboration and foundation audit; they are not a full CI claim.

The exact new paper-gap note was sent to `latexmk -pdf`. Rendering remains
blocked by the environment's missing `dsfont.sty`, required by the existing
shared `docs/paper-gaps/command.tex`; no PDF was produced. This is a pending
document-rendering dependency, not a denied operation or an unresolved
mathematical implication. No replacement package or altered rendering macros
were used to hide the missing dependency.
