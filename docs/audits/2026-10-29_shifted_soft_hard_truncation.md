# Soft truncation with an approximate energy origin

Let A be a Hermitian complex matrix, let r and r′ be real, and suppose
A − r′I is positive semidefinite and r − 10 ≤ r′. For t > 0 and an integer
m ≥ 1, put ε = (t/2)2^(−m). The actual affine soft truncation satisfies

\[
\operatorname{min}(A,(r+t/2-10)I)-\varepsilon I
\le r'I+h_{m,t}(A-r'I)\le A.
\]

The proof applies the positive-matrix soft-versus-hard comparison to
A − r′I. The hard cutoff obeys the exact translation identity

\[
\operatorname{min}(A-r'I,(t/2)I)
 = \operatorname{min}(A,(r'+t/2)I)-r'I.
\]

Finally, r + t/2 − 10 ≤ r′ + t/2, so monotonicity in the scalar cutoff gives
the stated lower comparator. The translation identity reuses Mathlib's
functional-calculus composition theorem and `min_sub_sub_right`; no new
matrix spectral expansion or noncommutative power estimate is introduced.

## Source and scope

ALVV, arXiv:1602.08828v2, Definition `def:soft-trunc`, lines 1178–1185 of
`local_alg_arxiv_v2.tex`, chooses an approximate regional ground energy r′
with r − 10 ≤ r′ ≤ r. If r is the true regional ground energy, this also
gives A − r′I ≥ 0. The theorem therefore applies to those source data.
The separate upper restriction r′ ≤ r is not needed once positivity of
A − r′I is an explicit assumption; the proved auxiliary theorem is valid
on this slightly larger domain.

The source's hard truncation is Definition `def:hard-trunc`, lines
873–886. The local source SHA256 is
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.
At t = m the actual uniform hard threshold above the true regional minimum
is m/2 − 10. The comparison remains an order statement even if that
threshold is negative. A physical hard-truncation theorem may impose its
own positive threshold requirement.

The complementary Hamiltonian, including interactions crossing the
regional boundary, is unchanged. Adding it preserves both inequalities.
This contribution does not prove the physical low-energy spectral theorem,
spectral-subspace closeness, or cluster and matrix product operator bounds.
It does not identify the result with the printed uniform energy estimate
in equation `eq:exp-approx-0`.

## Declarations and verification

The new module `Analysis/ShiftedSoftHardTruncation.lean` provides three
public declarations, each used by the final comparison or its proof:

- `Matrix.monotone_energyTruncation`;
- `Matrix.IsHermitian.energyTruncation_sub_smul_one`;
- `Matrix.IsHermitian.softTruncation_shifted_hard_bounds`.

Cutoff monotonicity needs no Hermitian hypothesis in its Lean statement:
Mathlib's functional-calculus order theorem already applies to the
library's totalized calculus. The translation and affine comparison state
their Hermitian hypothesis explicitly. Empty matrix index types are
included, and no normalized vector or ground-state uniqueness is assumed.

The separate prerequisite patch is
`qiclean-soft-hard-truncation-20261029.patch`, SHA256
`05513948ac3daa039a8d44abb735cb4032ea25a28af12b30f9411e5cf6719472`.
Its source files and private compiled objects remained byte-identical
throughout the affine contribution. This contribution contains no edits to
its scalar or positive-matrix theorem modules.

Private elaboration used the clean TNLean provider
`1604ed2ffc831a4f6afba70150024edd3ca19d6c` and checked QICLean package
`afcf986970504f1d370e475f0617256ca83b160d`. Its strict actual-module check
passed in 3.64 seconds after proof simplification. A separate importing
module audited all three new public declarations: their only foundations
were `propext`, `Classical.choice`, and `Quot.sound`. Source, provider-object,
and prerequisite source/object hashes were checked before and after these
runs. Every new object was written under `/tmp`; no provider or dependency
was changed and no Mathlib source was rebuilt.

The reader-facing prose check and repeated-tactic scan passed. The new
chapter compiled together with its prerequisite chapter, with resolved
references and no overfull boxes, and the comparison statements were
visually inspected. Ordinary common-library compilation and the compiled
blueprint declaration check remain integration checks. No persistent
per-theorem audit fixture is included in the patch.

## Ordinary verification

At mathematical revision `d41577c2965094ee0f1067fce107aa59088d653e`, the full 10,353-job library build,
strict checks of all five changed production files, and the imported audit
of all eleven public declarations in the four changed mathematical modules
passed. The only foundations used are propext, Classical.choice and
Quot.sound. Source synchronization, compiled blueprint declaration checks,
added-prose and compilation-time checks also passed. No job reached the
25-second warning threshold, and no Mathlib source was compiled. Existing
prebuilt artifacts and the repository lock were used; no permanent Lean
fixture was added.

The complete local record is `/tmp/qiclean-soft-hard-kernel-gates.json`,
with the additional prose log `/tmp/qiclean-soft-hard-kernel-prose.log`.
This completion record changes documentation only. The physical soft
spectral/subspace comparison remains separate.
