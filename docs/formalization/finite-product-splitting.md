# Splitting finite regions by an isometry on their complement

Let ψ be a unit pure state on a finite tensor product, let T and E be disjoint
regions, and put U = Λ \ (T ∪ E). The formalization constructs an isometry W on the
entire Hilbert space of U and separate unit purifications s, s′ such that

\[
\|(1_{TE}\otimes W)\psi-s\otimes s'\|
\le \sqrt{2(1-e^{-I_\psi(T:E)/2})}\le\sqrt{I_\psi(T:E)}.
\]

This is Lemma 6.4, `lem:splitting`, in OpenAI's *Polynomial PEPS approximation of
gapped square-grid ground states* (September 24, 2026),
[`05-frames.tex`, lines 352–391](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/05-frames.tex#L352).
The source is fixed at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The declarations are in `QICLean/Entropy/FiniteProductSplitting.lean`. They reuse
the existing physical reduced density, regional entropy and mutual information
from `FiniteProduct`, together with the proved matrix purification splitting
from `PurificationSplitting`. The coordinate equivalence enumerates only T and E;
it does not discard any directions of U. Its rank-one right marginal is exactly
`FiniteProduct.jointMatrix`, and trace one proves coordinate normalization.

The output factors can be chosen as B_T = ℂ^(dim H_T) and
B_E = ℂ^(dim H_E) ⊕ H_U. Their dimensions are finite but unrestricted, as in the
source. Empty regions and unequal local dimensions are allowed. For L > 0, the
corollary proves that I(T:E) ≤ L⁻⁶⁰ gives vector error ≤ L⁻³⁰.

A stated partition Λ = T ⊔ U ⊔ E has U = Λ \ (T ∪ E); the complement formulation
therefore has the same mathematical hypotheses. The state need not be a ground
state, and the theorem makes no spectral-gap assumption. The full area law and
polynomial PEPS approximation theorem require additional analytic and geometric
results and are not established by this splitting result.

All new proofs are original, using the existing QICLean and Mathlib results.
No upstream OpenAI Lean proof text was copied or adapted. OpenAI Codex assisted
with the proof, source comparison, documentation and verification. Human
mathematical review remains a separate responsibility.
