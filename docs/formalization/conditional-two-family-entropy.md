# Conditional two-family entropy estimate

`FiniteProduct.conditionalMutualInformation_le_two_family_sum` proves the generic
entropy step used inside the proof of OpenAI's PEPS cell-information lemma
([September 24, 2026, Lemma 3.2, lines 180–222](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex#L180-L222)).

For an actual normalized finite-product pure state, let G, B and C be disjoint,
and partition G into an exceptional remainder D and two disjoint finite ordered
families X and Y. Set F = (G ∪ B ∪ C)ᶜ. Bounds

- I(Xᵢ : C ∪ B ∪ pastᵢ) ≤ εᵢ
- I(Yⱼ : C ∪ F ∪ pastⱼ) ≤ δⱼ

imply I(G:C|B) ≤ Σ εᵢ + 2S(D) + Σ δⱼ. The main theorem also has a direct form
using the actual sums of mutual information. Local dimensions may vary, empty
families/regions are allowed, and no error-sign or smallness hypothesis is added.

The proof applies the conditional chain rule to the whole first family, D and
the whole second family. It dualizes that last whole-family term before using
its forward chain. This implements the paper's opposite-order argument without
a second enumeration. It never infers that an ordinary information estimate
survives arbitrary conditioning. The exceptional cost 2S(D) follows from purity
and subadditivity. The exterior identity C ∪ F = (G ∪ B)ᶜ connects the formula
to the forbidden-color-one exterior used in the manuscript.

## Scope and ownership

This is a generic QICLean entropy theorem. It does not construct the geometric
cell partition, prove coarse collars, count tiles, or prove the polylogarithmic
cell bound. The source's cell-lemma completion label is not assigned to this
supporting theorem. Canonical tripartite API identification and dimension/site-
count transport remain with their existing owner; no competing API is introduced.

All new code is independently written from the mathematical paper and existing
Mathlib/QICLean results. No OpenAI Lean proof code is copied or adapted.
