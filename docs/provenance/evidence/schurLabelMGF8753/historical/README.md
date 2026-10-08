# Quantitative centered Schur-label moment transfer

The two public declarations concern an actual copy-permutation-invariant
density matrix on k copies and an arbitrary real center s. The sole growth
hypothesis bounds the logarithm of the actual centered surprisal moment by
C0 k B t² for |t| ≤ c0/√B. It is not a label-moment hypothesis.

The first declaration gives the sharper positive bound C0 k B u² and the
negative bound 2 C0 k B u² + (q²/2) log(k+1) on the explicit smaller range.
It does not need positivity assumptions on C0 or c0 beyond the given moment
and range hypotheses. The uniform declaration assumes C0≥0, c0>0 and B≥1,
constructs c=min(c0,1)/2>0, and proves the larger bound for every real t with
|t|≤c/√B. Here q is the dimension of the one-copy coordinate space.

The trace of each relevant exponential weighted by the actual state is
proved strictly positive. This uses the state's nonvanishing, the positive
definiteness of a Hermitian exponential, and the existing strict trace-pairing
theorem. No convention at log(0) replaces this step.

The source is the conditional transfer at Section 7, lines 227–238 of the
September 24, 2026 area-law manuscript. The one-copy marginal estimate at
lines 75–85 and its independent-copy application must be connected separately;
this contribution assumes the centered k-copy surprisal bound explicitly.
It does not claim the full comparator concentration theorem.

## Verification

The exact notice-bearing source passed direct Lean verification with all
package options and warningAsError in 4.271 seconds. Its separate imported
axiom audit passed in 3.586 seconds. Both public declarations depend only on
propext, Classical.choice and Quot.sound.

All 4,651 actual imported artifacts are hashed. Every preexisting dependency
hash agrees before and after the final compilation and audit. The frozen
signed-moment comparison source matches canonical commit
6c8a3e8cfaf896ebf6eeac3d8782193847755905 byte for byte; its underlying weighted
trace and joint-resolution dependencies remain the frozen f24f6b07 sources.
Only this new module was compiled. No shared cache was changed.

The mathematical fragment has exactly two public declaration tags. The
focused repeated-tactic scan found no repeated pattern at its thresholds.
This evidence records raw Lean checks, not a Lake build, full checkdecls,
or full-book rendering. The latter integration checks belong to the area-law
coordinator.
