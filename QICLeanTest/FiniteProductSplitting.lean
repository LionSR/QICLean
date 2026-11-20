/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FiniteProductSplitting

/-! Regression examples for finite-product purification splitting. -/

open scoped Matrix Kronecker Matrix.Norms.L2Operator

namespace FiniteProductSplittingTest

/-- Three local dimensions differ, and the third region supplies an unused
buffer. The coordinate split reconstructs every configuration exactly. -/
private def localDimension (v : Fin 3) : ℕ := if v = 0 then 2 else if v = 1 then 3 else 5

example (ψ : EuclideanSpace ℂ ((v : Fin 3) → Fin (localDimension v)))
    (x : (v : Fin 3) → Fin (localDimension v)) :
    ManyBody.splitTwoRegionsState (fun v ↦ Fin (localDimension v)) ψ {0} {1}
      (by decide)
      (ManyBody.splitTwoRegionsEquiv (fun v ↦ Fin (localDimension v)) {0} {1}
        (by decide) x) = ψ x := by
  simp only [ManyBody.splitTwoRegionsState, Equiv.symm_apply_apply]

/-- With no physical sites the global configuration space still has dimension
one, and the coordinate state is normalized. -/
example :
    star (ManyBody.splitTwoRegionsState (fun _ : PEmpty ↦ Fin 0)
      (EuclideanSpace.single (fun v : PEmpty ↦ v.elim) 1) ∅ ∅ (by simp)) ⬝ᵥ
      ManyBody.splitTwoRegionsState (fun _ : PEmpty ↦ Fin 0)
        (EuclideanSpace.single (fun v : PEmpty ↦ v.elim) 1) ∅ ∅ (by simp) = 1 := by
  apply ManyBody.splitTwoRegionsState_unit
  simp

/-- Empty regions have zero mutual information in a unit state, so splitting
must be exact. This checks the zero-error endpoint rather than a positive bound. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) :
    ∃ (W : Matrix
        (Fin (Fintype.card (ManyBody.RegionConfig β ∅)) ×
          (Fin (Fintype.card (ManyBody.RegionConfig β ∅)) ⊕
            ManyBody.RegionConfig β (∅ ∪ ∅)ᶜ))
        (ManyBody.RegionConfig β (∅ ∪ ∅)ᶜ) ℂ)
      (s : Fin (Fintype.card (ManyBody.RegionConfig β ∅)) ×
        Fin (Fintype.card (ManyBody.RegionConfig β ∅)) → ℂ)
      (s' : Fin (Fintype.card (ManyBody.RegionConfig β ∅)) ×
        (Fin (Fintype.card (ManyBody.RegionConfig β ∅)) ⊕
          ManyBody.RegionConfig β (∅ ∪ ∅)ᶜ) → ℂ),
      W.IsIsometry ∧ star s ⬝ᵥ s = 1 ∧ star s' ⬝ᵥ s' = 1 ∧
        ((1 : Matrix _ _ ℂ) ⊗ₖ W) *ᵥ
          ManyBody.splitTwoRegionsState β ψ ∅ ∅ (by simp) =
            Matrix.tensorPurification s s' := by
  obtain ⟨W, s, s', hW, hs, hs', hnorm, _⟩ :=
    ManyBody.exists_isIsometry_splitTwoRegionsState_norm_sub_le β ψ hψ ∅ ∅ (by simp)
  refine ⟨W, s, s', hW, hs, hs', ?_⟩
  have hz : ‖WithLp.toLp 2 ((((1 : Matrix _ _ ℂ) ⊗ₖ W) *ᵥ
      ManyBody.splitTwoRegionsState β ψ ∅ ∅ (by simp)) -
      Matrix.tensorPurification s s')‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    simpa [FiniteProduct.mutualInformation, ManyBody.regionEntropy_empty β ψ hψ] using hnorm
  exact sub_eq_zero.mp ((WithLp.toLp_eq_zero 2).mp (norm_eq_zero.mp hz))

end FiniteProductSplittingTest
