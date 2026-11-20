/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Support
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Two systems on the same sites, paired at every site

Two systems `X` and `Y` on the same sites `V` give the system with basis `X v × Y v` at the site
`v`. Its configurations are pairs of configurations of the two systems, along
`Equiv.arrowProdEquivProdArrow`, so an operator `A` on the first system and `B` on the second give
the operator `A ⊗ B` on the paired system. If `A` is supported on `S` and `B` on `T`, then
`A ⊗ B` is supported on `S ∪ T`. No basis type need be nonempty.

Generalizes TNLean's `QuantumCircuit.reindex_kronecker_mem_supportedOperators`
(`TNLean/Circuit/SitewiseTensorSupport.lean` at commit `414a18fb88`), which pairs the
alphabets `Fin d` and `Fin e` into `Fin (d * e)`; there the pairing of the alphabets is a
relabelling of the basis at every site.

## Main results

* `ManyBody.reindex_kronecker_mem_supportedOperators` — the support of `A ⊗ B`.
-/

open Matrix
open scoped Kronecker

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X Y : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] [∀ v, Fintype (Y v)] [∀ v, DecidableEq (Y v)]

/-- **The support of a paired product.** If `A` is supported on `S` and `B` on `T`, then
`A ⊗ B`, an operator on the system with basis `X v × Y v` at every site `v`, is supported on
`S ∪ T`. -/
theorem reindex_kronecker_mem_supportedOperators {S T : Finset V}
    {A : Matrix (Config X) (Config X) ℂ} {B : Matrix (Config Y) (Config Y) ℂ}
    (hA : A ∈ supportedOperators X S) (hB : B ∈ supportedOperators Y T) :
    reindex (Equiv.arrowProdEquivProdArrow V X Y).symm (Equiv.arrowProdEquivProdArrow V X Y).symm
        (A ⊗ₖ B) ∈ supportedOperators (fun v ↦ X v × Y v) (S ∪ T) := by
  have hentry (σ τ : (v : V) → X v × Y v) :
      reindex (Equiv.arrowProdEquivProdArrow V X Y).symm
          (Equiv.arrowProdEquivProdArrow V X Y).symm (A ⊗ₖ B) σ τ =
        A (fun v ↦ (σ v).1) (fun v ↦ (τ v).1) * B (fun v ↦ (σ v).2) (fun v ↦ (τ v).2) := by
    simp
  refine ⟨fun σ τ ⟨v, hv, hne⟩ ↦ ?_, fun σ τ σ' τ' h1 h2 h3 h4 ↦ ?_⟩
  · rw [Finset.mem_union, not_or] at hv
    rw [hentry]
    by_cases h : (σ v).1 = (τ v).1
    · rw [apply_eq_zero_of_mem_supportedOperators hB hv.2 fun h' ↦ hne (Prod.ext h h'), mul_zero]
    · rw [apply_eq_zero_of_mem_supportedOperators hA hv.1 h, zero_mul]
  · have hcases (v : V) : (σ v = σ' v ∧ τ v = τ' v) ∨ (σ v = τ v ∧ σ' v = τ' v) := by
      by_cases hST : v ∈ S ∪ T
      · exact Or.inl ⟨h1 v hST, h2 v hST⟩
      · exact Or.inr ⟨h3 v hST, h4 v hST⟩
    rw [hentry, hentry,
      hA.apply_eq (fun v hv ↦ by rw [h1 v (Finset.mem_union_left T hv)])
        (fun v hv ↦ by rw [h2 v (Finset.mem_union_left T hv)])
        (fun v _ ↦ by rcases hcases v with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [h, h']),
      hB.apply_eq (fun v hv ↦ by rw [h1 v (Finset.mem_union_right S hv)])
        (fun v hv ↦ by rw [h2 v (Finset.mem_union_right S hv)])
        (fun v _ ↦ by rcases hcases v with ⟨h, h'⟩ | ⟨h, h'⟩ <;> simp [h, h'])]

end ManyBody
