/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap
import QICLean.Spectral.Gap.EigenvalueGap

/-!
# Gaps of operators applied on the fibers of a finite product

Extending an operator independently over a finite spectator space preserves every nonnegative
lower norm bound `δ ‖x‖ ≤ ‖G x‖` on the orthogonal complement of its kernel, and over a nonempty
spectator space the extension has exactly the same such bounds as the operator. Replacing one
nonempty finite spectator space by another therefore preserves the bound, whatever their
dimensions. No positivity or symmetry of the operator is needed. The quadratic-form inequality
`γ ⟨G x, x⟩ ≤ ⟨G x, G x⟩` also passes to the extension.

Moved from TNLean (Apache-2.0) at commit `49b78ed821`: the gap statements of
`TNLean/MPS/ParentHamiltonian/Martingale/SpectatorGapEquivalence.lean` and
`TNLean/MPS/ParentHamiltonian/Martingale/FiberwiseQuadraticFormGap.lean`. Changes: the fiber
lemmas of the first file are in `QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap`; the
operator may have different source and target where this is free.

## Main results

* `ContinuousLinearMap.norm_gap_rightFiberwiseMap` — a gap of the operator is a gap of its
  extension.
* `ContinuousLinearMap.norm_gap_rightFiberwiseMap_iff` — for a nonempty spectator space, the
  extension has exactly the gaps of the operator.
* `ContinuousLinearMap.quadraticForm_sq_ge_rightFiberwiseMap` — the quadratic-form inequality
  passes to the extension.
-/

open scoped BigOperators InnerProductSpace ComplexOrder

namespace ContinuousLinearMap

variable {I J S T : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype T]

/-- A single-fiber vector is orthogonal to the kernel of the extension exactly when its fiber
is orthogonal to the kernel of the operator. -/
theorem singleRightFiber_mem_orthogonal_ker_rightFiberwiseMap_iff
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (s : S) (x : EuclideanSpace ℂ I) :
    singleRightFiber s x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ ↔
      x ∈ (LinearMap.ker G.toLinearMap)ᗮ := by
  classical
  rw [mem_orthogonal_ker_rightFiberwiseMap_iff]
  constructor
  · intro h
    simpa using h s
  · intro h t
    by_cases ht : t = s
    · simpa [ht] using h
    · simp [ht]

/-- A lower norm bound on the orthogonal complement of the kernel extends to all finite
spectator fibers with the same constant, even if the spectator type is empty. -/
theorem norm_gap_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hGap : ∀ x ∈ (LinearMap.ker G.toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G x‖) :
    ∀ x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖rightFiberwiseMap (S := S) G x‖ := by
  intro x hx
  have hFiber := (mem_orthogonal_ker_rightFiberwiseMap_iff G x).mp hx
  apply (sq_le_sq₀ (mul_nonneg hδ (norm_nonneg _)) (norm_nonneg _)).mp
  calc
    (δ * ‖x‖) ^ 2 = ∑ s, (δ * ‖rightFiber x s‖) ^ 2 := by
      rw [mul_pow, norm_sq_eq_sum_norm_sq_rightFiber, Finset.mul_sum]
      simp only [mul_pow]
    _ ≤ ∑ s, ‖G (rightFiber x s)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      exact (sq_le_sq₀ (mul_nonneg hδ (norm_nonneg _)) (norm_nonneg _)).mpr
        (hGap _ (hFiber s))
    _ = ‖rightFiberwiseMap (S := S) G x‖ ^ 2 := by
      rw [norm_sq_eq_sum_norm_sq_rightFiber]
      simp only [rightFiber_rightFiberwiseMap]

/-- An extension over a nonempty finite spectator space has exactly the same nonnegative lower
norm bounds on the orthogonal complement of the kernel as the operator. -/
theorem norm_gap_rightFiberwiseMap_iff [Nonempty S]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖rightFiberwiseMap (S := S) G x‖) ↔
      ∀ x ∈ (LinearMap.ker G.toLinearMap)ᗮ, δ * ‖x‖ ≤ ‖G x‖ := by
  constructor
  · intro hGap x hx
    let s : S := Classical.choice ‹Nonempty S›
    have hSingle :=
      (singleRightFiber_mem_orthogonal_ker_rightFiberwiseMap_iff G s x).mpr hx
    simpa only [rightFiberwiseMap_singleRightFiber, norm_singleRightFiber] using
      hGap (singleRightFiber s x) hSingle
  · exact norm_gap_rightFiberwiseMap G hδ

/-- Replacing a nonempty finite spectator space by any other nonempty finite spectator space
preserves a lower norm bound on the orthogonal complement of the kernel exactly. -/
theorem norm_gap_rightFiberwiseMap_iff_rightFiberwiseMap [Nonempty S] [Nonempty T]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ,
      δ * ‖x‖ ≤ ‖rightFiberwiseMap (S := S) G x‖) ↔
      ∀ x ∈ (LinearMap.ker (rightFiberwiseMap (S := T) G).toLinearMap)ᗮ,
        δ * ‖x‖ ≤ ‖rightFiberwiseMap (S := T) G x‖ :=
  (norm_gap_rightFiberwiseMap_iff (S := S) G hδ).trans
    (norm_gap_rightFiberwiseMap_iff (S := T) G hδ).symm

/-- The inequality `G² ≥ γ G` is preserved when `G` is applied independently on every fiber. -/
theorem quadraticForm_sq_ge_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) {γ : ℝ}
    (hG : ∀ u,
      γ * (⟪G u, u⟫_ℂ).re ≤ (⟪G u, G u⟫_ℂ).re)
    (v : EuclideanSpace ℂ (I × S)) :
    γ * (⟪rightFiberwiseMap (S := S) G v, v⟫_ℂ).re ≤
      (⟪rightFiberwiseMap (S := S) G v,
        rightFiberwiseMap (S := S) G v⟫_ℂ).re := by
  rw [inner_rightFiberwiseMap, inner_rightFiberwiseMap, Complex.re_sum, Complex.re_sum,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  simpa only [rightFiber_rightFiberwiseMap] using hG (rightFiber v s)

end ContinuousLinearMap

namespace LinearMap.IsPositive

variable {I S : Type*} [Fintype I] [Fintype S]

/-- A gap above the kernel of a positive operator, every eigenvalue other than `0` being at least
`γ ≥ 0`, gives the quadratic-form inequality `G² ≥ γ G` for its independent extension over a
finite spectator space. -/
theorem quadraticForm_sq_ge_rightFiberwiseMap_of_forall_hasEigenvalue
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsPositive) {γ : ℝ} (hγ : 0 ≤ γ)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue G.toLinearMap μ → μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ v : EuclideanSpace ℂ (I × S),
      γ * (⟪ContinuousLinearMap.rightFiberwiseMap (S := S) G v, v⟫_ℂ).re ≤
        (⟪ContinuousLinearMap.rightFiberwiseMap (S := S) G v,
          ContinuousLinearMap.rightFiberwiseMap (S := S) G v⟫_ℂ).re :=
  ContinuousLinearMap.quadraticForm_sq_ge_rightFiberwiseMap G
    (hG.quadraticForm_sq_ge_of_forall_hasEigenvalue hγ hGap)

end LinearMap.IsPositive
