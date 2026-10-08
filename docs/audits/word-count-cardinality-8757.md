# Word count cardinality

This separately named combinatorial intermediate supports the fixed-time
Poisson count/order calculation in the pinned amplification source,
`area-law09-amplification.tex`, lines 49–54 and 237–253. It does not identify
the existing word measure with a chronological independent-clock process.

## Mathematical argument

`WordMultiplicity.countsFinsupp` is the sum of one-coordinate unit count
vectors over the positions of a word. Its coordinate sum is the word length.
For a finite alphabet, the polynomial `(∑ i, X i)^m` expands by distributivity
as the sum of `X^(countsFinsupp w)` over all functions `w : Fin m → ι`.
Taking the coefficient at the finitely supported version of `n : ι → ℕ`
therefore counts the fixed-length words with precisely those counts.
Mathlib's independently proved coefficient formula gives the multinomial
coefficient when `∑ i, n i = m`, and zero otherwise.

The probability module defines `countVector` on the existing `PoissonWord.Word`
and its actual preimage event `countEvent`. Any member has length `∑ i, n i`.
A proved bijection to the fixed-length subtype supplies a finite enumeration,
the exact cardinality `(∑ i, n i)! / ∏ i, (n i)!`, and nonemptiness from strict
positivity of the multinomial coefficient. There are no assumed cardinality,
count-law, or normalization fields. The empty alphabet and zero vector are
included without extra hypotheses.

## Public declaration audit

All 16 public declarations are covered by guarded `#print axioms` checks in
`QICLeanTest/PoissonWordCountsAxioms.lean`:

- `WordMultiplicity.countsFinsupp`
- `WordMultiplicity.sum_counts`
- `WordMultiplicity.card_counts_eq`
- `PoissonWord.countVector`
- `PoissonWord.countEvent`
- `PoissonWord.countFiber`
- `PoissonWord.countVector_nil`
- `PoissonWord.sum_countVector`
- `PoissonWord.length_eq_sum_of_countVector_eq`
- `PoissonWord.countFiberEquiv`
- `PoissonWord.instFintypeCountFiber`
- `PoissonWord.finite_countEvent`
- `PoissonWord.card_countFiber`
- `PoissonWord.card_countFiber_eq_factorial`
- `PoissonWord.countFiber_nonempty`
- `PoissonWord.countEvent_nonempty`

Every guard reports only `propext`, `Classical.choice`, and `Quot.sound`.
The polynomial expansion is private and is transitively audited by
`WordMultiplicity.card_counts_eq`. The two new source files and the consumer
examples contain no `sorry`, `admit`, `axiom`, `native_decide`, or `unsafeCast`.
The existing base `PoissonWord` module was not changed and does not acquire
any polynomial imports.

## Validation

The exact Lean 4.35.0-rc3 compiler and prebuilt Mathlib cache in the shared
compiler worktree checked committed authoring trees under the exclusive Lake
cache lock. No uncommitted leaf copies were used. Every check enabled:

```
-DautoImplicit=false
-DrelaxedAutoImplicit=false
-Dpp.unicode.fun=true
-DmaxSynthPendingDepth=3
-Dlinter.mathlibStandardSet=true
-DwarningAsError=true
```

- `QICLean/Algebra/WordMultiplicity.lean`: pass at `4461092`; its unchanged
  source was checked again and emitted at `033adfa`.
- `QICLean/Probability/PoissonWordCounts.lean`: pass and emitted at `d7b78ac`.
- `QICLeanTest/PoissonWordCounts.lean`: pass at `f5cadb4`.
- `QICLeanTest/PoissonWordCountsAxioms.lean`: pass at `f5cadb4`.

The eight consumer examples check actual positional counts for the word
`[0, 1, 0]`, multiplicities `(2, 1)` and `(2, 2)`, a mismatched fixed length,
zero counts, the empty alphabet, absence of positive-length empty-alphabet
words, and finite/nonempty count events under only `Finite ι`.

The blueprint leaf `ch11_poisson_word_counts.tex` directly mirrors the
coefficient proof and count-fiber bijection. Router integration and the final
combined declaration/blueprint checks belong to the parent integration pass.

The convention's `scripts/tactic_pattern_scan.py` is absent from this checkout.
Manual review found no new proof pattern repeated across mathematical source
files that warrants a new lemma, simp set, or tactic.
