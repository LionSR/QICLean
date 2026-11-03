# Failure sections of a finite independent product

For a measurable event in a finite product of probability spaces, a uniform upper bound epsilon on every section in one coordinate bounds the probability of the event by epsilon. The remaining coordinates can include both earlier and later choices; the event is not required to be independent of them.

The proof uses Mathlib's measure-preserving separation of one finite coordinate, followed by the existing uniform-section theorem with the full remaining history space. It introduces no second product measure and repeats no integration proof.

This auxiliary supports the local-failure sum in Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Figure fig:algo1 and lines 1777–1817. A physical application must still construct the actual measurable outputs, prove that a child's output is independent of its parent's fresh coordinate, and supply the fixed-input section estimate. This lemma alone is not a probability theorem for the complete recursive construction.

Strict checking passes at the default options in 4.114 seconds. Imported foundation inspection uses only propext, Classical.choice and Quot.sound; the temporary source is deleted. Combined ordinary-build and compiled blueprint declaration checks remain pending.
