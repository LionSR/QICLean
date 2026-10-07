# Doubled full-system gap: source and verification

This packet records the original five-entry blueprint leaf at the frozen
documentation revision identified in [`frozen-blueprint.json`](frozen-blueprint.json).
The current leaf is
[`ch12_entropy_doubled_system_gap.tex`](../../../../blueprint/src/chapter/ch12_entropy_doubled_system_gap.tex).
The frozen leaf contains five mathematical entries and all 13 public declarations in
[`DoubledSystemGap.lean`](../../../../QICLean/Analysis/DoubledSystemGap.lean).
The matching 13-entry provenance ledger is
[`doubled8766.json`](../../openai-math.d/doubled8766.json).
The current ledger names public checkpoint
`5a846a09030085ad1546d50163caad111f7748f4`; the exact source-byte and tree
correspondence to the recorded local checks is in
[`public-checkpoint-attestation.json`](public-checkpoint-attestation.json).
The former local-revision ledger is retained unchanged in
[`historical-ledger-57bf.json`](historical-ledger-57bf.json).
This correspondence does not relabel any command as having run at the public
checkpoint; all historical run records retain their original revisions and
outcomes.
The later strictly positive-gap uniqueness extension and its 16-link combined
render are recorded separately in
[`8766-doubled-gap-uniqueness-render`](../8766-doubled-gap-uniqueness-render/README.md).
The checker reads the historical leaf from the recorded Git revision; it does
not assert that the current extended leaf has the old render hash.

## Source correspondence

The source is the unnumbered paragraph immediately after `eq:info-reset-overlap`
in [the pinned September 24, 2026 paper](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L415-L425),
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This paragraph calls the tensor sum `mathbb H`, its partial-swap conjugate
`mathbb H'`, their ground vectors `Psi` and `Phi`, and their common ground
energy `mathcal E = 2 E0`. It asserts that their gaps are at least `Delta`.
The new leaf proves this lower-gap and eigenvector part by the following exact
correspondence:

- The physical vector is `Psi = Omega tensor Omega`; its coefficients are
  `Omega(i) Omega(j)`, including their complex phases. Its rank-one projector
  is `P tensor P`, where `P = |Omega><Omega|`.
- Normalization `sum_i |Omega(i)|^2 = 1` makes `Q = I - P` positive
  semidefinite. The assumption `R = H - E0 I - Delta Q >= 0` states the
  full-system lower gap. It makes no assertion about subsystem Hamiltonians.
- The exact residual is
  `mathbb H - 2 E0 I - Delta(I - |Psi><Psi|)`
  `= R tensor I + I tensor R + Delta(Q tensor Q)`.
  This is an algebraic identity without normalization or an eigenvector
  hypothesis. Positivity of its three terms uses normalization, `R >= 0`,
  and `Delta >= 0`.
- The separate assumption `H Omega = E0 Omega` proves
  `mathbb H Psi = 2 E0 Psi`. Together with normalization and the nonnegative
  lower-gap bound, this identifies `2 E0` as the ground energy.
- For every unitary `U`, the entire gap residual is conjugated by `U`.
  The norm and eigenvector equation are also preserved. This transport
  allows any real `Delta`; nonnegativity is needed in the preceding doubling
  argument.
- The final theorem uses the actual `Matrix.partialSwap A B`. Its coordinate
  action exchanges the two `A` factors of `((A x B) x (A x B))`. Both
  Hamiltonians and vectors stay on this original doubled physical space.
  Taking `Phi = F Psi` and `mathbb H' = F mathbb H F dagger` yields the three
  conclusions together: normalization, eigenvalue `2 E0`, and the inherited
  lower-gap bound.

This is not an equality assertion for the exact spectral gap. The formal
theorems admit `Delta = 0`; they make no uniqueness claim there, and the
regression suite includes a zero-gap Hamiltonian for which every vector is a
ground vector. The source also discusses uniqueness under its positive-gap
setting, interaction range, degree, strength, and support of the Hamiltonian
difference. Those assertions are outside these 13 declarations. No claim of
formalizing that entire paragraph, a subsystem gap, or the later Gaussian
filter is made. The proof text is original; no upstream Lean proof was copied.

## Frozen and integrated Lean evidence

[`verification.json`](verification.json) indexes the preserved runs and exact
source hashes. The frozen production and final regression bytes are from
`b4acf6c00a3d0f6e150462bfd7d5cde4dddb584b`.

- `runs/doubled-gap-strict-first.json` records passing strict production
  elaboration and a passing raw 13-declaration axiom audit. It also records
  an earlier regression failure against different test bytes. That failure
  and its complete diagnostic log are retained as history.
- `runs/doubled-gap-tests-b4ac.json` records the final strict regression pass,
  including all 13 guarded axiom checks, against the committed b4 test hash.
- `runs/doubled-integrated-57bf.json` separately records the parent's native
  target build, strict production, strict regression/all 13 guards, and raw
  13-declaration audit at
  `57bfd1d9842875d41d1e8d1b56f0ec66d6dbc2b0`. All four succeeded and the
  production/test/driver hashes are unchanged. The integration commit also
  registers the root Analysis import and existing regression loop; those
  changes belong to the parent's integration work, not this documentation
  commit.

Every raw audit reports exactly `propext`, `Classical.choice`, and `Quot.sound`
for each of the 13 declarations. The Mathlib `#print` linter messages are
preserved; they are informational, and the test guards expect them rather
than disabling the linter. The raw driver is retained byte-for-byte in
[`drivers/DoubledSystemGapRawAxioms.lean`](drivers/DoubledSystemGapRawAxioms.lean).

The compiler worktree is deliberately switched between frozen revisions.
File presence in its current checkout is not evidence that the recorded
revision passed or failed; the attestation is the recorded revision, exact
source bytes, command result, and log. The documentation worker ran no Lean,
Lake, dependency build, or cache command.

## Rendering and limits

The focused render contains the unchanged physical-buffer leaf followed by
the doubled-gap leaf, so the partial-swap definition and unitarity references
resolve. No new tensor diagram is introduced: the doubled-gap proof is an
aligned-equation exposition. The unchanged compression picture uses the
existing pinned Tenkz support, and its contraction records and pixels are
checked again in this combined render. The focused preamble borrows the
support from the local buffer-publication checkout; this commit does not
duplicate or change that infrastructure.

The render reports and artifact hashes are in [`render/`](render/). PDF and
static HTML checks cover all 13 new declaration links and the new labels;
the reused leaf's 43 declaration links are checked separately. The local
PDF, rendered pages, generated HTML, and SVG are untracked artifacts. Live
browser, MathJax execution, responsive layout, complete-book rendering,
full-root build, hosted CI, publication, merge, and issue completion are not
claimed here.

Private workspace prefixes in copied run records and logs are replaced with
role tokens. Render-log trailing whitespace and terminal blank lines are
trimmed; no diagnostic lines are discarded. Each original and normalized
SHA256 is recorded, while the raw driver is copied unchanged. Recorded
tokenized commands describe past runs, not ready-to-execute shell scripts.
The render history retains the initial environment-only TeX lookup failures;
the final render uses the already prepared TeX environment and formats.

Run `python3 docs/provenance/evidence/8766-doubled-gap/check.py` from the
repository root with the frozen documentation revision available in Git to
verify this packet's hashes, provenance IDs,
declaration/guard/raw coverage, recorded source bytes, and standard-axiom
sets. This checker does not execute Lean.
