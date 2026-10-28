# Actual low-frequency coefficients in the AKLV construction

This contribution provides the algebraic connection between the actual ordered-word
partition and the fixed-frequency rank estimate in AKLV, arXiv:1301.1162v1,
Lemma 4.2 (`l:agsp`, source lines 604–644). It follows the weighted one-marker
contribution in local commit `f7e523320bb4721617b598ebe2084f9836e78d5e`, based on
current QICLean main `164c79df0e105bd6acef741709a14d95da3cd24a`.

## Mathematical content

`WordCoefficient.lean` defines the actual full-frequency coefficient as a sum of
ordered words and proves that bijective renaming of the alphabet preserves occurrence
counts. Distinct labels remain distinct when their operators coincide.

`OneMarkerFullCounts.lean` inserts a prescribed distinguished count into a residual
frequency vector. If \(O=I\setminus\{u\}\), \(\alpha:O\to\mathbb N\), and
\(\iota_{u,k}(\alpha)\) has value \(k\) at \(u\) and restriction \(\alpha\) to \(O\),
then its total is \(k+\sum_a\alpha(a)\). Rewriting words by the bijection
\(O\sqcup\{*\}\simeq I\) proves exact equality of the actual full-frequency and
residual one-marker coefficients. Consequently, for arbitrary complex weights,

\[
\sum_{\substack{\beta:I\to\mathbb N\\\sum_a\beta(a)=m+k,\ \beta(u)=k}}
\lambda_\beta C_{m+k,\beta}
=
\sum_{\substack{\alpha:O\to\mathbb N\\\sum_a\alpha(a)=m}}
\lambda_{\iota_{u,k}(\alpha)}D_{m,k,\alpha}.
\]

The frequency insertion is a bijection on these two finite sets. The finite
enumerations of the original and residual alphabets are arbitrary; no prescribed
ordering or independence assumption is imposed.

`OneWindowWordPartition.lean` chooses a selector from the occurrence counts in a
nonempty window \(S\). It is chosen before the operator family, degree, and cutoff.
For every \(d\le\ell\), the actual full-frequency coefficients of
\((\sum_aH_a)^d\) partition by the selected interaction \(u\in S\) and its count
\(0\le k\le\lfloor\ell/|S|\rfloor\). The proof reuses the existing local
minimum-frequency selector and groups the actual ordered words twice. No suitable
marker or coefficient-rank estimate is supplied.

Zero degrees, empty residual alphabets, vanishing operators and linear dependence
among coefficients are included. This contribution introduces no new source correction.
The corrected commuting-gap count remains documented in
[the existing word-count note](https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf).

The physical chain supports, transport to the central cut, and resulting power-rank
bound are separate TNLean results. The binomial estimates, choice of a shorter window,
arbitrary-polynomial assembly and optimized AKLV rank estimate remain separate.

## Verification

The source worktree was advanced to exact current main `164c79df` before seeding.
The canonical source was the clean, fully warmed QICLean `hot-main` at that same commit.
Its prebuilt cache fetch and full build passed 10,330 jobs. Canonical same-commit seeding
then succeeded under the shared TNLean lock; no patched-branch cache was copied.

The frozen first contribution passed an ordinary three-target build against this
current-main environment (1,834 jobs). The three new algebra modules then passed a
separate ordinary target build (1,830 jobs):

| Module | Ordinary time | SHA-256 |
| --- | --- | --- |
| `WordCoefficient` | 5.7 s | `b7ea4b219742ce766ce1e3e1129d4eb659768910979567e50c9bac989a3de223` |
| `OneWindowWordPartition` | 2.2 s | `61d64f91b02346f98098affb961ac51d6261e3f7a2a29d9e8b27bb3ca95768ea` |
| `OneMarkerFullCounts` | 3.7 s | `10ae7aee01708c6e09e5b33fa6e5549d3f868cdc14fb8296ea3821d57676ac71` |

Separate strict checks of the actual modules also passed with `autoImplicit=false`,
`relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`, Mathlib standard linters and
warnings as errors. An imported manual inspection of all twelve new public QICLean
and TNLean declarations passed in 3.06 seconds. Their only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. No permanent per-theorem fixture is added.

A full ordinary QICLean library build passed 10,334 jobs in 39.86 seconds, followed
by compiled blueprint declaration validation in 11.09 seconds. All six changed
mathematical source hashes remained unchanged throughout both checks. The generated
algebra import file contains the four new production modules. Blueprint source
synchronization, reader-facing prose checks and the tactic-pattern scan also passed.

The earlier audit `2026-10-28_aklv_one_marker_rank.md` records the preliminary status
of the frozen first contribution. The current-main ordinary verification above
supersedes that pending-build status without changing any of its source hashes.

No Mathlib source was compiled. Shared cache operations and ordinary builds used the
repository lock, and no other worktree or live build was interrupted.
