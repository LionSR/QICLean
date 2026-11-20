/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Support
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Operators on one of two systems of sites

Two systems of sites `A` and `B` form the system with sites `A ⊕ B`, whose configurations are
pairs of configurations of the two systems. An operator `M` on the first system acts on the
union as `M ⊗ 1`, and an operator on the second as `1 ⊗ M`. An operator supported on a region
`S` of `A` is supported on the region `S ⊔ ∅` of `A ⊕ B`, and similarly on the other side. The
basis types form one family on `A ⊕ B`; identical sites are the constant family.

## Main definitions

* `ManyBody.inlOp`, `ManyBody.inrOp` — `M ⊗ 1` and `1 ⊗ M` on the sites `A ⊕ B`.

## Main results

* `ManyBody.inlOp_mem_supportedOperators`, `ManyBody.inrOp_mem_supportedOperators` — supports.
* `ManyBody.inlOp_add_inrOp` — `M ⊗ 1 + 1 ⊗ N` in the coordinates of the two systems.
-/

open Matrix
open scoped Kronecker

namespace ManyBody

variable {A B : Type*} [Fintype A] [Fintype B] {Z : A ⊕ B → Type*} [∀ v, DecidableEq (Z v)]

/-- The operator `M ⊗ 1` on the sites `A ⊕ B`, for an operator `M` on the sites `A`. -/
noncomputable def inlOp (M : Matrix (Config fun a ↦ Z (.inl a)) (Config fun a ↦ Z (.inl a)) ℂ) :
    Matrix (Config Z) (Config Z) ℂ :=
  (M ⊗ₖ (1 : Matrix (Config fun b ↦ Z (.inr b)) (Config fun b ↦ Z (.inr b)) ℂ)).submatrix
    (Equiv.sumPiEquivProdPi Z) (Equiv.sumPiEquivProdPi Z)

/-- The operator `1 ⊗ M` on the sites `A ⊕ B`, for an operator `M` on the sites `B`. -/
noncomputable def inrOp (M : Matrix (Config fun b ↦ Z (.inr b)) (Config fun b ↦ Z (.inr b)) ℂ) :
    Matrix (Config Z) (Config Z) ℂ :=
  ((1 : Matrix (Config fun a ↦ Z (.inl a)) (Config fun a ↦ Z (.inl a)) ℂ) ⊗ₖ M).submatrix
    (Equiv.sumPiEquivProdPi Z) (Equiv.sumPiEquivProdPi Z)

omit [Fintype A] in
theorem inlOp_apply (M : Matrix (Config fun a ↦ Z (.inl a)) (Config fun a ↦ Z (.inl a)) ℂ)
    (σ τ : Config Z) :
    inlOp M σ τ = if (fun b ↦ σ (.inr b)) = (fun b ↦ τ (.inr b)) then
      M (fun a ↦ σ (.inl a)) (fun a ↦ τ (.inl a)) else 0 := by
  simp [inlOp, one_apply]

omit [Fintype B] in
theorem inrOp_apply (M : Matrix (Config fun b ↦ Z (.inr b)) (Config fun b ↦ Z (.inr b)) ℂ)
    (σ τ : Config Z) :
    inrOp M σ τ = if (fun a ↦ σ (.inl a)) = (fun a ↦ τ (.inl a)) then
      M (fun b ↦ σ (.inr b)) (fun b ↦ τ (.inr b)) else 0 := by
  simp [inrOp, one_apply]

/-- `M ⊗ 1 + 1 ⊗ N` in the coordinates of the two systems. -/
theorem inlOp_add_inrOp
    (M : Matrix (Config fun a ↦ Z (.inl a)) (Config fun a ↦ Z (.inl a)) ℂ)
    (N : Matrix (Config fun b ↦ Z (.inr b)) (Config fun b ↦ Z (.inr b)) ℂ) :
    inlOp M + inrOp N =
      (M ⊗ₖ (1 : Matrix (Config fun b ↦ Z (.inr b)) (Config fun b ↦ Z (.inr b)) ℂ) +
        (1 : Matrix (Config fun a ↦ Z (.inl a)) (Config fun a ↦ Z (.inl a)) ℂ) ⊗ₖ N).submatrix
        (Equiv.sumPiEquivProdPi Z) (Equiv.sumPiEquivProdPi Z) := by
  rw [inlOp, inrOp]
  rfl

omit [Fintype A] in
theorem inlOp_sum {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (Config fun a ↦ Z (.inl a)) (Config fun a ↦ Z (.inl a)) ℂ) :
    inlOp (∑ i ∈ s, M i) = ∑ i ∈ s, inlOp (M i) := by
  ext σ τ
  simp only [inlOp_apply, Matrix.sum_apply]
  split_ifs <;> simp

omit [Fintype B] in
theorem inrOp_sum {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (Config fun b ↦ Z (.inr b)) (Config fun b ↦ Z (.inr b)) ℂ) :
    inrOp (∑ i ∈ s, M i) = ∑ i ∈ s, inrOp (M i) := by
  ext σ τ
  simp only [inrOp_apply, Matrix.sum_apply]
  split_ifs <;> simp

omit [Fintype A] in
theorem conjTranspose_inlOp
    (M : Matrix (Config fun a ↦ Z (.inl a)) (Config fun a ↦ Z (.inl a)) ℂ) :
    (inlOp M)ᴴ = inlOp Mᴴ := by
  simp [inlOp, conjTranspose_submatrix, conjTranspose_kronecker]

omit [Fintype B] in
theorem conjTranspose_inrOp
    (M : Matrix (Config fun b ↦ Z (.inr b)) (Config fun b ↦ Z (.inr b)) ℂ) :
    (inrOp M)ᴴ = inrOp Mᴴ := by
  simp [inrOp, conjTranspose_submatrix, conjTranspose_kronecker]

variable [DecidableEq A] [DecidableEq B] [∀ v, Fintype (Z v)]

/-- An operator supported on a region `S` of `A` acts on the sites `A ⊕ B` with support
`S ⊔ ∅`. -/
theorem inlOp_mem_supportedOperators {S : Finset A}
    {M : Matrix (Config fun a ↦ Z (.inl a)) (Config fun a ↦ Z (.inl a)) ℂ}
    (hM : M ∈ supportedOperators (fun a ↦ Z (.inl a)) S) :
    inlOp M ∈ supportedOperators Z (S.disjSum ∅) := by
  rw [mem_supportedOperators_iff] at hM ⊢
  refine ⟨fun σ τ ⟨w, hw, hne⟩ ↦ ?_, fun σ τ σ' τ' h₁ h₂ h₃ h₄ ↦ ?_⟩
  · rw [inlOp_apply]
    rcases w with a | b
    · split_ifs
      · exact hM.1 _ _ ⟨a, fun h ↦ hw (Finset.inl_mem_disjSum.mpr h), hne⟩
      · rfl
    · rw [ite_eq_right fun h ↦ hne (congrFun h b)]
  · have hr (ρ ρ' : Config Z) (h : ∀ w ∉ S.disjSum ∅, ρ w = ρ' w) :
        (fun b ↦ ρ (.inr b)) = fun b ↦ ρ' (.inr b) :=
      funext fun b ↦ h (.inr b) (by simp)
    rw [inlOp_apply, inlOp_apply, ite_eq_left (hr _ _ h₃), ite_eq_left (hr _ _ h₄)]
    exact hM.2 _ _ _ _ (fun a ha ↦ h₁ (.inl a) (Finset.inl_mem_disjSum.mpr ha))
      (fun a ha ↦ h₂ (.inl a) (Finset.inl_mem_disjSum.mpr ha))
      (fun a ha ↦ h₃ (.inl a) fun h ↦ ha (Finset.inl_mem_disjSum.mp h))
      (fun a ha ↦ h₄ (.inl a) fun h ↦ ha (Finset.inl_mem_disjSum.mp h))

/-- An operator supported on a region `T` of `B` acts on the sites `A ⊕ B` with support
`∅ ⊔ T`. -/
theorem inrOp_mem_supportedOperators {T : Finset B}
    {M : Matrix (Config fun b ↦ Z (.inr b)) (Config fun b ↦ Z (.inr b)) ℂ}
    (hM : M ∈ supportedOperators (fun b ↦ Z (.inr b)) T) :
    inrOp M ∈ supportedOperators Z ((∅ : Finset A).disjSum T) := by
  rw [mem_supportedOperators_iff] at hM ⊢
  refine ⟨fun σ τ ⟨w, hw, hne⟩ ↦ ?_, fun σ τ σ' τ' h₁ h₂ h₃ h₄ ↦ ?_⟩
  · rw [inrOp_apply]
    rcases w with a | b
    · rw [ite_eq_right fun h ↦ hne (congrFun h a)]
    · split_ifs
      · exact hM.1 _ _ ⟨b, fun h ↦ hw (Finset.inr_mem_disjSum.mpr h), hne⟩
      · rfl
  · have hl (ρ ρ' : Config Z) (h : ∀ w ∉ (∅ : Finset A).disjSum T, ρ w = ρ' w) :
        (fun a ↦ ρ (.inl a)) = fun a ↦ ρ' (.inl a) :=
      funext fun a ↦ h (.inl a) (by simp)
    rw [inrOp_apply, inrOp_apply, ite_eq_left (hl _ _ h₃), ite_eq_left (hl _ _ h₄)]
    exact hM.2 _ _ _ _ (fun b hb ↦ h₁ (.inr b) (Finset.inr_mem_disjSum.mpr hb))
      (fun b hb ↦ h₂ (.inr b) (Finset.inr_mem_disjSum.mpr hb))
      (fun b hb ↦ h₃ (.inr b) fun h ↦ hb (Finset.inr_mem_disjSum.mp h))
      (fun b hb ↦ h₄ (.inr b) fun h ↦ hb (Finset.inr_mem_disjSum.mp h))

end ManyBody
