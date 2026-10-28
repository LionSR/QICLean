# AKLV fixed-frequency operator Schmidt rank

The contribution proves the algebraic estimate at one distinguished cut in the
proof of AKLV, arXiv:1301.1162v1, Lemma 4.2 (source label `l:agsp`, lines
626–662). It does not prove the optimized rank bound for an arbitrary polynomial.

## Mathematical statement

Let the ordinary interactions satisfy
\(H_a=A_a\otimes 1+1\otimes B_a\), and let the distinguished interaction
\(T\) have operator Schmidt rank at most \(r\). For ordinary degree \(m\),
marker frequency \(k\), and \(E_m=\{\alpha:\sum_a\alpha(a)=m\}\), define
\(C_\alpha\) by summing the actual ordered words of length \(m+k\) having
these letter counts. For arbitrary complex weights, the new theorem proves

\[
\operatorname{OSR}\left(\sum_{\alpha\in E_m}\lambda_\alpha C_\alpha\right)
\le |E_m|\binom{m+2k+1}{2k+1}r^k.
\]

The proof identifies the actual generating polynomial, applies the commuting-gap
rank bound to each evaluation, and recovers the weighted coefficient sum from one
common set of evaluation points. No independence or nonvanishing of coefficient
operators is assumed. Empty alphabets, zero-dimensional factors, zero frequencies,
and zero rank bounds are included with the usual convention \(0^0=1\).

The additional `+1` in the binomial coefficient is the correction already recorded
in [the interpolation and word-count note](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf).
With total degree \(\ell=m+k\), the count is
\(\binom{\ell+k+1}{2k+1}\), rather than the printed count lacking that `+1`.

## Source ownership

`OneMarkerWeightedSchmidtRank.lean` defines the actual coefficient family and its
compatibility with semiring homomorphisms, then proves the weighted rank bound.
The previously private weighted interpolation argument is moved, without changing
its proof, to `MonomialEvaluationSchmidtRank.lean`; both one-marker and two-marker
consumers reuse it. The existing public two-marker statement is unchanged.

The physical chain supports, exact count of ordinary frequencies, and actual window
alphabet belong to TNLean. The remaining AKLV steps include the partition by a
low-frequency interaction, transport to the central cut, summation of the selected
pieces, and the optimized polynomial rank estimate. No independent chain area-law
result is used as a replacement.

## Verification

The source-only worktree is based on QICLean main
`b294d968eeed2a7618dab1ca67deb00224171448`. No Lake environment was initialized
there. Separate strict module checks used the already seeded TNLean dependency
artifacts at QICLean `c97ffd63d9b52bdec7191d25aca66b9af7a2f872`, with all new
objects written into a private temporary namespace. These are preliminary checks,
not an ordinary current-main QICLean build.

Every existing QICLean source in the transitive import closure of the three changed
modules (18 sources), and the toolchain, Lake configuration, and dependency manifest,
was compared between those commits: there were no differences. No deleted
`finrank_iSup_map_le_card_mul` helper was restored or referenced.

| Module | Strict check | SHA-256 |
| --- | --- | --- |
| `MonomialEvaluationSchmidtRank` | passed, 10.66 s | `d0ca2fa0a8349fcec9fe77e053cd6363bd60157688d879c0c1f9254a50c2fc8f` |
| `WeightedFrequencySchmidtRank` | passed, 3.83 s | `078dbf826aa445f90d025ede787257bfe34726b57a99cae3d35066c82a57f96c` |
| `OneMarkerWeightedSchmidtRank` | passed, 11.10 s | `64ab78f3ec76d80c0fef5adeb74e727ea29dc3a6db610ec0d5dbed64f7468b2f` |

All checks use `autoImplicit=false`, `relaxedAutoImplicit=false`,
`maxSynthPendingDepth=3`, Mathlib standard linters, and warnings as errors.
An imported manual foundation inspection includes every new public declaration
and the unchanged two-marker consumer. Their only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The inspection is temporary; no permanent
per-theorem fixture is added.

An ordinary build against current-main QICLean and compiled blueprint declaration
validation remain pending. No Mathlib source was compiled and no shared build cache
was changed by these checks.
