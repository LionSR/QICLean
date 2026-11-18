/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Map

/-!
# Substituting circuits for layers

An unbranched circuit is its sequence of layers. When every layer can be realised, through an
encoding of the matrices of each system, by an unbranched circuit on other sites and gates of
depth at most `K` times its own, the whole circuit can, with depth at most `K` times its own
(`Circuit.exists_substitute`). The statement is existential: there is no substitution operation
on circuits.

## Main results

* `QuantumCircuit.Circuit.exists_substitute` — unbranched substitution with its depth bound.
-/

open ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {ev : Interpretation G}

namespace Circuit

/-- **Unbranched substitution.** Let every layer `L` on nonempty bases with trace-preserving gates
and onsite families be realised, through the encodings `ι X` of the matrices of each system, by an
unbranched circuit on the sites `S'` with trace-preserving local families and depth at most
`K * L.depth`. Then so is every unbranched circuit with trace-preserving local families on
nonempty bases, with depth at most `K` times its depth.

The input bases must be nonempty: on an empty configuration space the empty Kraus family is
trace-preserving, so a layer may then have no branch to continue along, and the realisations of
the single layers give no circuit for the zero map.

The bound `K * L.depth` asks a layer of depth `0`, one using only cells of cost `0` and onsite
families, to be realised by a circuit of depth `0`. -/
theorem exists_substitute {S' : Type} [Fintype S'] [DecidableEq S'] {Γ' : Geometry S'}
    {G' : Finset S' → (S' → Type) → (S' → Type) → Type 1} [GateFamily G']
    {ev' : Interpretation G'} (Ψ : SystemMap S S')
    (ι : ∀ (X : S → Type) [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)],
      Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config (Ψ.system X)) (Config (Ψ.system X)) ℂ)
    (K : ℕ)
    (hL : ∀ ⦃X Y : S → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
      [∀ s, Nonempty (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y),
      L.Forall ev KrausFamily.IsTP →
        ∃ c' : Circuit Γ' G' (Ψ.system X) (Ψ.system Y), c'.IsUnbranched ∧
          c'.Forall ev' KrausFamily.IsTP ∧ c'.depth ≤ K * L.depth ∧
          c'.map ev' ∘ₗ ι X = ι Y ∘ₗ (ofLayer L).map ev) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    [∀ s, Nonempty (X s)] → [∀ s, Fintype (Z s)] → [∀ s, DecidableEq (Z s)] →
    (c : Circuit Γ G X Z) → c.IsUnbranched → c.Forall ev KrausFamily.IsTP →
    ∃ c' : Circuit Γ' G' (Ψ.system X) (Ψ.system Z), c'.IsUnbranched ∧
      c'.Forall ev' KrausFamily.IsTP ∧ c'.depth ≤ K * c.depth ∧
      c'.map ev' ∘ₗ ι X = ι Z ∘ₗ c.map ev
  | _, _, i₁, i₂, _, i₃, i₄, Circuit.done _, _, _ => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    refine ⟨.done _, trivial, trivial, Nat.zero_le _, ?_⟩
    rw [map_done, map_done]
    rfl
  | _, _, _, _, _, _, _, Circuit.step L next, hc, hTP => by
    obtain ⟨i₀⟩ := L.nonempty_index_of_forall_isTP ev hTP.1
    have := L.nonempty_output_of_forall_isTP ev hTP.1
    obtain ⟨cL, hcL, hTPL, hdL, hmL⟩ := hL L hTP.1
    obtain ⟨cR, hcR, hTPR, hdR, hmR⟩ :=
      exists_substitute Ψ ι K hL (next i₀) (hc.2 i₀) (hTP.2 i₀)
    refine ⟨cL.comp cR, hcL.comp hcR, hTPL.comp ev' hTPR, ?_, ?_⟩
    · refine (depth_comp _ _).trans ?_
      rw [depth_step, Nat.mul_add]
      exact Nat.add_le_add hdL (hdR.trans (Nat.mul_le_mul_left K
        (Finset.le_sup (f := fun i ↦ (next i).depth) (Finset.mem_univ i₀))))
    · rw [map_comp, LinearMap.comp_assoc, hmL, ← LinearMap.comp_assoc, hmR,
        step_eq_ofLayer_comp L hc.1 i₀, map_comp, LinearMap.comp_assoc]

end Circuit

end QuantumCircuit
