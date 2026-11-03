# ALVV companion sources on current main

The review series begins at QIC main af417dc8d480017e8c72c5d81191a76fcedb68a3.
Its mathematical sources reconcile the fully checked Lean 4.35 continuation
32b5f3e04e232bb9ee2ee34a7bf5078b263b85b3 and the independently checked
least-spectral-value lemma 6554bbb45c3806d3dad4b8cb2e8ac01303b74c15.
The series preserves main's Lean/Mathlib 4.36.0-rc1 configuration, dependency
pins, automation and unrelated mathematics. These draft trees have not been
elaborated or built on Lean 4.36. Historical Lean 4.35 checks do not establish
that these reconciled trees compile on the newer toolchain.

## Mathematical overlaps

The three-way comparison found 22 overlapping handwritten Lean files.
Nineteen retain current main unchanged. These include the coordinate-index
abstraction used by sampling, the current soft-truncation imports, and the
region-rank import used by internal cuts. Fourteen of those overlaps differ
only in prose or theorem/lemma classification. The remaining import and
coordinate-index differences are retained from current main as well.

Three files adopt explicit extensions from the checked continuation, while
retaining current main's theorem/lemma classification for existing names:

- `Analysis/ChebyshevWordPower.lean`: the extended theorem returns the
  actual filter, its complementary tensor factors, low-space invariance,
  minimum gain and high-space contraction before every input space. The
  previous ordered-word conclusion remains an active corollary with its
  original mathematical hypotheses and conclusion.
- `Analysis/ViableSubspaceErrorReduction.lean`: for nested targets
  T contained in Tplus, the sufficient hypothesis is that the filter sends
  Tplus's orthogonal complement into T's orthogonal complement. Main's
  stronger invariance of Tplus's complement implies this condition, since
  T is contained in Tplus. The continuation proof uses precisely the
  resulting orthogonality to T. The error conclusion is unchanged. This
  is a generalization of the sufficient hypothesis, not an assumed spectral
  gap or a stronger invariant-subspace assertion. The nonnested theorem's
  public mathematical signature remains unchanged.
- `Analysis/ViableSubspaceSpectralProjector.lean`: the corresponding nested
  tensor consequence uses that weaker sufficient orthogonality condition.
  Tensor containment is taken from its shared owner `TensorFamilyImage`.
  The elementary tensor-product declarations retain their original names
  there, and the spectral-cutoff application explicitly derives the
  orthogonality required by the generalized theorem.

No new proof was attempted during publication preparation. Every source
choice requires the forthcoming Lean 4.36 verification, including unchanged
importers above the generalized matrix-analysis APIs.

## Previously submitted nested-cutoff results

The older draft 8af1f77d468fed30b84644f923b8ae319a2bc432 contains helpers absent
from the historical 32b5f3e0 provider. They are already present on current main
and remain in this series. In particular `Analysis/SpectralWindowCount.lean`
is retained unchanged from main. The older draft's mathematical declaration
names are retained, allowing the two elementary tensor helpers to move to
the shared tensor-family owner. There is no replacement of current main by
an old-toolchain snapshot, and no duplicate submission of QIC PR 1020.

## Review order and scope

The five dependency layers concern spectral/soft estimates; low-density and
refinement bounds; Borel sampling and trimming; stopped repeated sampling;
and compressed energies with Ritz extraction. Each branch is based on the
preceding one. The current import generator is run at every layer, and every
source import and blueprint declaration reference is checked against that
layer's sources. Historical audit notes accompany the modules they mention,
or the final layer when their dependencies cannot be identified reliably.

These are companion-library results with the hypotheses stated in their
signatures. They do not assert the complete physical algorithm, its printed
running time, or unresolved regional-energy attachments. The coordination
tracker is https://github.com/LionSR/TNLean/issues/10533; current-toolchain
verification is tracked at https://github.com/LionSR/TNLean/issues/10534.
The remaining physical energy composition is tracked separately at
https://github.com/LionSR/TNLean/issues/10535.

New review commits are authored by Sirui Lu using the established GitHub
noreply address. Their commit messages explicitly credit OpenAI Codex GPT-6.
Original proof commits and preservation references are not rewritten.
