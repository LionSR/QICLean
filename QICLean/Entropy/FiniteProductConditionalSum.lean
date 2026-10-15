/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.FiniteProductConditional

/-!
# Adding finitely many conditional information costs

A finite family of regional systems can be added in any order. If the
conditional information contributed by each region is bounded whenever
all preceding regions are included in the conditioning system, the total
increase of mutual information is bounded by the sum of these costs.

This is the entropy summation in the proof of Proposition 3.4 of
*Polynomial PEPS approximation of gapped square-grid ground states*,
`02-information.tex`, lines 717–725, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The identity itself does not
require normalization, disjointness, or a Hamiltonian.
-/

open scoped BigOperators

namespace FiniteProduct

/-- Adding a finite family of regions increases mutual information by at most
the sum of its conditional information costs. Every preceding region remains
in the conditioning system.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 717–725. -/
theorem mutualInformation_union_biUnion_le_of_conditional
    {V ι : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (B C : Finset V)
    (G : ι → Finset V) (s : Finset ι) (cost : ι → ℝ)
    (hcost : ∀ i ∈ s, ∀ t : Finset ι, t ⊆ s → i ∉ t →
      FiniteProduct.conditionalMutualInformation β ψ (G i) C (B ∪ t.biUnion G) ≤
        cost i) :
    FiniteProduct.mutualInformation β ψ (B ∪ s.biUnion G) C ≤
      FiniteProduct.mutualInformation β ψ B C + ∑ i ∈ s, cost i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hprev := ih (fun j hj t hts hjt ↦
      hcost j (Finset.mem_insert_of_mem hj) t (hts.trans (Finset.subset_insert i s)) hjt)
    have hnext := hcost i (Finset.mem_insert_self i s) s (Finset.subset_insert i s) hi
    have hchain : mutualInformation β ψ (B ∪ (insert i s).biUnion G) C =
        mutualInformation β ψ (B ∪ s.biUnion G) C +
          conditionalMutualInformation β ψ (G i) C (B ∪ s.biUnion G) := by
      simp only [Finset.biUnion_insert, mutualInformation, conditionalMutualInformation,
        Finset.union_left_comm, Finset.union_comm]
      ring
    rw [hchain, Finset.sum_insert hi]
    linarith only [hprev, hnext]

end FiniteProduct
