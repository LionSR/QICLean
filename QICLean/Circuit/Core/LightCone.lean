/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Channel
import QICLean.Circuit.Core.Cost

/-!
# The backward light cone of a circuit

The backward light cone of a region `R` through a circuit is obtained layer by layer, from the
last layer to the first: each layer adds the cells it uses that meet the current region. For
an unbranched circuit whose gates and onsite families are trace-preserving, the Heisenberg
picture maps an operator supported on `R` to an operator supported on the backward light cone
of `R`.

Both hypotheses are needed. If a continuation depends on the outcome of a measurement far from
`R`, the Heisenberg picture depends on the measured site. If a family outside the light cone is
not trace-preserving, its effect `∑ Kᵢᴴ Kᵢ` is not the identity and remains in the Heisenberg
picture.

When every cell has positive cost, the light cone lies in the `T`-fold neighbourhood of `R` in
the geometry, where `T` is the depth.

## Main definitions

* `QuantumCircuit.Circuit.lightCone` — the backward light cone of a region.

## Main results

* `QuantumCircuit.Circuit.dual_mem_supportedOperators_lightCone` — the light cone bound.
* `QuantumCircuit.Circuit.lightCone_subset_neighbourhood` — the light cone in terms of depth.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

namespace Layer

omit [Fintype S] [GateFamily G] in
/-- The backward light cone through a layer lies in the neighbourhood of the region. -/
theorem lightCone_subset_neighbourhood [Fintype Γ.Cell] {X Y : S → Type}
    (L : Layer Γ G X Y) (R : Finset S) : L.lightCone R ⊆ Γ.neighbourhood R := by
  refine Finset.union_subset_union le_rfl (Finset.biUnion_subset_biUnion_of_subset_left _ ?_)
  intro b hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩

end Layer

namespace Circuit

/-- The backward light cone of the region `R` through a circuit, layer by layer from the last
layer, over all branches. -/
def lightCone : {X Z : S → Type} → Circuit Γ G X Z → Finset S → Finset S
  | _, _, done _, R => R
  | _, _, step L next, R => L.lightCone (Finset.univ.sup fun i ↦ (next i).lightCone R)

/-- The backward light cone: the Heisenberg picture of an unbranched circuit whose gates and
onsite families are trace-preserving maps an operator supported on `R` to an operator supported
on the backward light cone of `R`. -/
theorem dual_mem_supportedOperators_lightCone (ev : Interpretation G) : {X Z : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : Circuit Γ G X Z) → c.IsUnbranched →
    c.Forall ev KrausFamily.IsTP → ∀ {R : Finset S} {A : Matrix (Config Z) (Config Z) ℂ},
      A ∈ supportedOperators Z R → c.dual ev A ∈ supportedOperators X (c.lightCone R)
  | _, _, i₁, i₂, i₃, i₄, done _, _, _, R, A, hA => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    have : (done _ : Circuit Γ G _ _).dual ev A = A := by
      change ∑ _ : Unit, ((1 : Matrix _ _ ℂ))ᴴ * A * 1 = A
      simp
    rw [this]
    exact hA
  | _, _, _, _, _, _, step L next, hb, h, R, A, hA => by
    rw [dual_step]
    cases isEmpty_or_nonempty L.Index with
    | inl hL =>
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact zero_mem _
    | inr hL =>
      obtain ⟨i₀⟩ := hL
      have hnext : ∀ i, next i = next i₀ := fun i ↦ hb.1 i i₀
      have hU : (next i₀).dual ev A ∈ supportedOperators _
          (Finset.univ.sup fun i ↦ (next i).lightCone R) :=
        supportedOperators_mono (Finset.le_sup (f := fun i ↦ (next i).lightCone R)
          (Finset.mem_univ i₀))
          (dual_mem_supportedOperators_lightCone ev (next i₀) (hb.2 i₀) (h.2 i₀) hA)
      have hsum : ∑ i, (L.kraus ev i)ᴴ * (next i).dual ev A * L.kraus ev i =
          L.dual ev ((next i₀).dual ev A) :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hnext i]
      rw [hsum]
      exact L.dual_mem_supportedOperators_lightCone ev h.1 hU

variable [Fintype Γ.Cell]

/-- When every cell has positive cost, the backward light cone of `R` lies in the
`depth`-fold neighbourhood of `R`. -/
theorem lightCone_subset_neighbourhood (hpos : ∀ b, 0 < Γ.cost b) :
    {X Z : S → Type} → (c : Circuit Γ G X Z) → (R : Finset S) →
      c.lightCone R ⊆ Γ.neighbourhood^[c.depth] R
  | _, _, done _, R => le_rfl
  | _, _, step L next, R => by
    set D := Finset.univ.sup fun i ↦ (next i).depth
    have hU : (Finset.univ.sup fun i ↦ (next i).lightCone R) ⊆ Γ.neighbourhood^[D] R :=
      Finset.sup_le fun i _ ↦ (lightCone_subset_neighbourhood hpos (next i) R).trans
        (Γ.iterate_neighbourhood_mono (Finset.le_sup (f := fun i ↦ (next i).depth)
          (Finset.mem_univ i)) le_rfl)
    change L.lightCone _ ⊆ Γ.neighbourhood^[L.depth + D] R
    unfold Layer.depth
    split_ifs with hL
    · rw [add_comm, Function.iterate_succ_apply']
      exact (L.lightCone_subset_neighbourhood _).trans (Γ.neighbourhood_mono hU)
    · have hcells : L.cells = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun b hb ↦ hL ⟨b, ?_⟩
        exact Finset.mem_filter.mpr ⟨hb, hpos b⟩
      rw [zero_add]
      refine Finset.union_subset hU ?_
      simp [hcells]

end Circuit

end QuantumCircuit
