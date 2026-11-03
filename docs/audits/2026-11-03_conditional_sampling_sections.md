# Integrating a conditional sampling error

For a measurable set A of earlier successful histories and a measurable failure relation E, a uniform section bound nu(E_x)<=epsilon for x in A gives (mu product nu)(E intersect fst-preimage(A))<=epsilon mu(A). The first statement requires only that nu is s-finite. When nu is a probability measure, the union of earlier failure and new failure has measure at most mu(A-complement)+epsilon mu(A). When mu is also a probability measure this is at most mu(A-complement)+epsilon.

The proof applies Mathlib's product-measure formula and integrates the bound epsilon times the indicator of A. It then decomposes the failure union and uses its subadditivity. No jointly measurable choice of pointwise success hulls is required. The actual failure relation must itself be measurable; applying this inequality to the complete interval-tree construction is subsequent work.

This is a measure-theoretic auxiliary for ALVV, arXiv:1602.08828v2, Lemma l:rs, lines 530–558, and the merge analysis at lines 1777–1817. It asserts neither an adaptive-tree theorem nor a running time.

Strict actual-name checking passes at default options in 3.694 seconds. All three public statements pass imported foundation inspection in 3.563 seconds using only propext, Classical.choice and Quot.sound. The temporary inspection source is deleted. Source blueprint synchronization, generated imports, prose and whitespace checks pass. Combined ordinary-build and declaration checks remain pending.
