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
* `QuantumCircuit.Circuit.dual_mul_of_disjoint_lightCone` — the Heisenberg picture is
  multiplicative on operators with disjoint light cones.
* `QuantumCircuit.Circuit.trace_map_piKronecker_mul_mul` — on a product input, expectations of such
  operators factorize.
* `QuantumCircuit.Circuit.lightCone_comp` — the light cone of a composition.
* `QuantumCircuit.Circuit.lightCone_subset_neighbourhood` — the light cone in terms of depth.
-/

open Matrix ManyBody
open scoped Kronecker

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

omit [Fintype S] [GateFamily G] in
theorem lightCone_mono {X Y : S → Type} (L : Layer Γ G X Y) {R R' : Finset S} (h : R ⊆ R') :
    L.lightCone R ⊆ L.lightCone R' := by
  refine Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ ?_)
  intro b hb
  obtain ⟨hb, v, hv⟩ := Finset.mem_filter.mp hb
  rw [Finset.mem_inter] at hv
  exact Finset.mem_filter.mpr ⟨hb, v, Finset.mem_inter.mpr ⟨hv.1, h hv.2⟩⟩

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
    rw [dual_done]
    exact hA
  | _, _, _, _, _, _, step L next, hb, h, R, A, hA => by
    cases isEmpty_or_nonempty L.Index with
    | inl hL =>
      rw [dual_step, Finset.univ_eq_empty, Finset.sum_empty]
      exact zero_mem _
    | inr hL =>
      obtain ⟨i₀⟩ := hL
      have hU : (next i₀).dual ev A ∈ supportedOperators _
          (Finset.univ.sup fun i ↦ (next i).lightCone R) :=
        supportedOperators_mono (Finset.le_sup (f := fun i ↦ (next i).lightCone R)
          (Finset.mem_univ i₀))
          (dual_mem_supportedOperators_lightCone ev (next i₀) (hb.2 i₀) (h.2 i₀) hA)
      rw [dual_step_of_forall_eq ev L hb.1 i₀]
      exact L.dual_mem_supportedOperators_lightCone ev h.1 hU

/-- The Heisenberg picture of an unbranched circuit whose gates and onsite families are
trace-preserving is multiplicative on operators whose backward light cones are disjoint. -/
theorem dual_mul_of_disjoint_lightCone (ev : Interpretation G) : {X Z : S → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : Circuit Γ G X Z) → c.IsUnbranched →
    c.Forall ev KrausFamily.IsTP → ∀ {R R' : Finset S}, Disjoint (c.lightCone R) (c.lightCone R') →
    ∀ {A B : Matrix (Config Z) (Config Z) ℂ}, A ∈ supportedOperators Z R →
    B ∈ supportedOperators Z R' → c.dual ev (A * B) = c.dual ev A * c.dual ev B
  | X, _, i₁, i₂, i₃, i₄, done _, _, _, R, R', _, A, B, _, _ => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    rw [dual_done, dual_done, dual_done]
  | _, _, _, _, _, _, step L next, hb, h, R, R', hRR', A, B, hA, hB => by
    cases isEmpty_or_nonempty L.Index with
    | inl hL => simp [dual_step]
    | inr hL =>
      obtain ⟨i₀⟩ := hL
      have hle : ∀ R, (next i₀).lightCone R ⊆ Finset.univ.sup fun i ↦ (next i).lightCone R :=
        fun R ↦ Finset.le_sup (f := fun i ↦ (next i).lightCone R) (Finset.mem_univ i₀)
      have hsub : ∀ R, (Finset.univ.sup fun i ↦ (next i).lightCone R) ⊆
          (step L next).lightCone R := fun _ ↦ Finset.subset_union_left
      simp only [dual_step_of_forall_eq ev L hb.1 i₀]
      rw [dual_mul_of_disjoint_lightCone ev (next i₀) (hb.2 i₀) (h.2 i₀)
        ((hRR'.mono (hsub R) (hsub R')).mono (hle R) (hle R')) hA hB]
      exact L.dual_mul_of_disjoint_lightCone ev h.1 hRR'
        (supportedOperators_mono (hle R)
          (dual_mem_supportedOperators_lightCone ev (next i₀) (hb.2 i₀) (h.2 i₀) hA))
        (supportedOperators_mono (hle R')
          (dual_mem_supportedOperators_lightCone ev (next i₀) (hb.2 i₀) (h.2 i₀) hB))

/-- **The light-cone factorization.** For an unbranched circuit whose gates and onsite families
are trace-preserving, applied to a product input `⊗ₛ σₛ` with `tr σₛ = 1`, the expectations of
operators with disjoint backward light cones factorize. -/
theorem trace_map_piKronecker_mul_mul (ev : Interpretation G) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (c : Circuit Γ G X Z) (hc : c.IsUnbranched) (hTP : c.Forall ev KrausFamily.IsTP)
    (σ : (s : S) → Matrix (X s) (X s) ℂ) (hσ : ∀ s, (σ s).trace = 1) {R R' : Finset S}
    (hRR' : Disjoint (c.lightCone R) (c.lightCone R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    (c.map ev (piKronecker σ) * (A * B)).trace =
      (c.map ev (piKronecker σ) * A).trace * (c.map ev (piKronecker σ) * B).trace := by
  rw [c.trace_map_mul ev, c.trace_map_mul ev, c.trace_map_mul ev,
    c.dual_mul_of_disjoint_lightCone ev hc hTP hRR' hA hB]
  exact trace_piKronecker_mul_mul σ hσ hRR'
    (c.dual_mem_supportedOperators_lightCone ev hc hTP hA)
    (c.dual_mem_supportedOperators_lightCone ev hc hTP hB)

theorem lightCone_mono : {X Z : S → Type} → (c : Circuit Γ G X Z) → {R R' : Finset S} →
    R ⊆ R' → c.lightCone R ⊆ c.lightCone R'
  | _, _, done _, _, _, h => h
  | _, _, step L next, _, _, h =>
    L.lightCone_mono (Finset.sup_mono_fun fun i _ ↦ lightCone_mono (next i) h)

/-- The backward light cone through a composition lies in the light cone through the first
circuit of the light cone through the second. -/
theorem lightCone_comp {Z : S → Type} (R : Finset S) : {X Y : S → Type} →
    (c : Circuit Γ G X Y) → (c' : Circuit Γ G Y Z) →
      (c.comp c').lightCone R ⊆ c.lightCone (c'.lightCone R)
  | _, _, done _, _ => le_rfl
  | _, _, step L next, c' =>
    L.lightCone_mono (Finset.sup_mono_fun fun i _ ↦ lightCone_comp R (next i) c')

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
