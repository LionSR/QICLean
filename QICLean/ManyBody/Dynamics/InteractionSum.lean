/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DoubledSystemGap
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Sites.SumSites

/-!
# The interaction of two systems side by side

Two interactions, `Φ` on the sites `A` and `Ψ` on the sites `B`, give an interaction on the
sites `A ⊕ B`: its terms are the terms `h ⊗ 1` of `Φ`, supported on `T i ⊔ ∅`, and the terms
`1 ⊗ k` of `Ψ`, supported on `∅ ⊔ U j`. Its Hamiltonian is `H_Φ ⊗ 1 + 1 ⊗ H_Ψ`. Applied to an
interaction and itself on identical sites, this is the interaction of two replicas, whose
Hamiltonian is the doubled Hamiltonian `H ⊗ 1 + 1 ⊗ H`.

## Main definitions

* `ManyBody.Interaction.sum` — the interaction of two systems side by side.

## Main results

* `ManyBody.Interaction.hamiltonian_sum` — its Hamiltonian is `H_Φ ⊗ 1 + 1 ⊗ H_Ψ`.
* `ManyBody.Interaction.hamiltonian_sum_self` — for two replicas, it is the doubled
  Hamiltonian, transported along `Equiv.sumArrowEquivProdArrow`.
-/

open Matrix
open scoped Kronecker

namespace ManyBody.Interaction

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  {Z : A ⊕ B → Type*} [∀ v, Fintype (Z v)] [∀ v, DecidableEq (Z v)]
  {ι κ : Type*} {T : ι → Finset A} {U : κ → Finset B}

/-- **The interaction of two systems side by side.** The terms of `Φ` act on the first
system, with supports `T i ⊔ ∅`, and the terms of `Ψ` on the second, with supports
`∅ ⊔ U j`. -/
noncomputable def sum (Φ : Interaction (fun a ↦ Z (.inl a)) T)
    (Ψ : Interaction (fun b ↦ Z (.inr b)) U) :
    Interaction Z (Sum.elim (fun i ↦ (T i).disjSum ∅) fun j ↦ (∅ : Finset A).disjSum (U j)) where
  term := Sum.elim (fun i ↦ inlOp (Φ.term i)) fun j ↦ inrOp (Ψ.term j)
  mem
    | .inl i => inlOp_mem_supportedOperators (Φ.mem i)
    | .inr j => inrOp_mem_supportedOperators (Ψ.mem j)

/-- The Hamiltonian of two systems side by side is `H_Φ ⊗ 1 + 1 ⊗ H_Ψ`. -/
theorem hamiltonian_sum [Fintype ι] [Fintype κ] (Φ : Interaction (fun a ↦ Z (.inl a)) T)
    (Ψ : Interaction (fun b ↦ Z (.inr b)) U) :
    (Φ.sum Ψ).hamiltonian = inlOp Φ.hamiltonian + inrOp Ψ.hamiltonian := by
  simp [hamiltonian, sum, Fintype.sum_sum_type, inlOp_sum, inrOp_sum]

/-- **The Hamiltonian of two replicas.** For an interaction `Φ` on identical sites, the
Hamiltonian of `Φ` beside itself is the doubled Hamiltonian `H ⊗ 1 + 1 ⊗ H`, transported to
the sites `V ⊕ V` along `Equiv.sumArrowEquivProdArrow`. -/
theorem hamiltonian_sum_self {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α]
    [DecidableEq α] {ι : Type*} [Fintype ι] {T : ι → Finset V}
    (Φ : Interaction (fun _ : V ↦ α) T) :
    (Φ.sum (Z := fun _ ↦ α) Φ).hamiltonian =
      reindex (Equiv.sumArrowEquivProdArrow V V α).symm (Equiv.sumArrowEquivProdArrow V V α).symm
        (doubledHamiltonian Φ.hamiltonian) := by
  rw [hamiltonian_sum, inlOp_add_inrOp]
  rfl

end ManyBody.Interaction
