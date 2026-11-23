/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap
import QICLean.Spectral.Gap.EigenvalueGap
import QICLean.Spectral.Gap.IsometricConjugationGap

/-!
# Gaps of operators applied on the fibers of a finite product

Extending an operator independently over a finite spectator space preserves every nonnegative
lower norm bound `δ ‖x‖ ≤ ‖G x‖` on the orthogonal complement of its kernel, and over a nonempty
spectator space the extension has exactly the same such bounds as the operator. No positivity
or symmetry of the operator is needed. The quadratic-form inequality
`γ ⟨G x, x⟩ ≤ ⟨G x, G x⟩` also passes to the extension. An operator that an isometric
coordinate change turns into such an extension inherits the operator form `κ P ≤ H` of the gap
above the kernel, and for a positive operator the eigenvalue form of the gap.

Moved from TNLean (Apache-2.0) at commit `49b78ed821`: the gap statements of
`TNLean/MPS/ParentHamiltonian/Martingale/SpectatorGapEquivalence.lean` and
`TNLean/MPS/ParentHamiltonian/Martingale/FiberwiseQuadraticFormGap.lean`. Changes: the fiber
lemmas of the first file are in `QICLean.Analysis.TensorProduct.EuclideanFiberwiseMap`; the
operator may have different source and target where this is free. The transport of the gap along
an isometric coordinate change is moved from TNLean,
`TNLean/MPS/ParentHamiltonian/Gap/Comparison/IntervalGapTransport.lean` at commit `600676ccac`.

## Main results

* `ContinuousLinearMap.norm_gap_rightFiberwiseMap` — a gap of the operator is a gap of its
  extension.
* `ContinuousLinearMap.norm_gap_rightFiberwiseMap_iff` — for a nonempty spectator space, the
  extension has exactly the gaps of the operator.
* `ContinuousLinearMap.quadraticForm_sq_ge_rightFiberwiseMap` — the quadratic-form inequality
  passes to the extension.
* `ContinuousLinearMap.smul_orthogonal_ker_projection_le_of_conj_rightFiberwiseMap`,
  `ContinuousLinearMap.forall_hasEigenvalue_of_conj_rightFiberwiseMap` — the gap passes to an
  operator isometrically conjugate to the extension.
-/

open scoped BigOperators InnerProductSpace ComplexOrder

namespace ContinuousLinearMap

variable {I J S : Type*} [Fintype I] [Fintype J] [Fintype S]

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

namespace ContinuousLinearMap

variable {E I S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [Fintype I] [Fintype S]

/-- **The operator form of the gap under a fiberwise conjugacy.** Let an isometric coordinate
change `U` turn `G` into the extension of `H` over the spectator fibers `S`. If `κ P ≤ H` for
the orthogonal projection `P` onto the orthogonal complement of `ker H`, then the same bound
holds for `G` and the projection onto the orthogonal complement of `ker G`. -/
theorem smul_orthogonal_ker_projection_le_of_conj_rightFiberwiseMap
    (U : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × S)) (G : E →ₗ[ℂ] E)
    (H : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) {κ : ℝ}
    (hConj : U.toLinearEquiv.conj G =
      (rightFiberwiseMap (S := S) H.toContinuousLinearMap).toLinearMap)
    (hLocal : (κ : ℂ) • (LinearMap.ker H)ᗮ.starProjection.toLinearMap ≤ H) :
    (κ : ℂ) • (LinearMap.ker G)ᗮ.starProjection.toLinearMap ≤ G := by
  have hProj := U.conj_starProjection_ker_of_conj G _
    (by simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using! hConj)
  rw [ker_starProjection_rightFiberwiseMap] at hProj
  have hProjConj : U.toLinearEquiv.conj (LinearMap.ker G).starProjection.toLinearMap =
      (rightFiberwiseMap (S := S) (LinearMap.ker H).starProjection).toLinearMap := by
    simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using! hProj
  have hId : rightFiberwiseMap (S := S) (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ I)) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (I × S)) := rfl
  have hOrth : U.toLinearEquiv.conj (LinearMap.ker G)ᗮ.starProjection.toLinearMap =
      (rightFiberwiseMap (S := S) (LinearMap.ker H)ᗮ.starProjection).toLinearMap := by
    simp only [Submodule.starProjection_orthogonal, ContinuousLinearMap.toLinearMap_sub,
      ContinuousLinearMap.coe_id, map_sub, LinearEquiv.conj_id, hProjConj,
      rightFiberwiseMap_sub, hId]
  refine (U.conj_le_conj_iff _ _).mp ?_
  simpa only [map_smul, hOrth, hConj, rightFiberwiseMap_smul,
    ContinuousLinearMap.toLinearMap_smul] using
    (rightFiberwiseMap_mono (S := S) (G := (κ : ℂ) • (LinearMap.ker H)ᗮ.starProjection)
      (H := H.toContinuousLinearMap) hLocal)

/-- **The gap under a fiberwise conjugacy.** Let an isometric coordinate change `U` turn `G` into
the extension of a positive operator `H` over the spectator fibers `S`. If every eigenvalue of
`H` other than `0` is at least `κ > 0`, then so is every eigenvalue of `G` other than `0`. -/
theorem forall_hasEigenvalue_of_conj_rightFiberwiseMap
    (U : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × S)) (G : E →ₗ[ℂ] E)
    (H : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) {κ : ℝ}
    (hκ : 0 < κ) (hPos : H.IsPositive)
    (hConj : U.toLinearEquiv.conj G =
      (rightFiberwiseMap (S := S) H.toContinuousLinearMap).toLinearMap)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue H μ → μ = 0 ∨ (κ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue G μ → μ = 0 ∨ (κ : ℂ) ≤ μ :=
  LinearMap.forall_hasEigenvalue_of_smul_orthogonal_ker_projection_le G
    (smul_orthogonal_ker_projection_le_of_conj_rightFiberwiseMap U G H hConj
      (hPos.smul_orthogonal_ker_projection_le_of_forall_hasEigenvalue hκ.le hGap))

end ContinuousLinearMap
