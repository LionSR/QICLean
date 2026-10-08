/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GaussianFilter.GroundEstimate

/-!
# Consumers of the actual Gaussian ground-vector estimates

The two-dimensional examples have common ground energy `-7` and gap `2`, with
different ground lines. The Hermitian input has a non-real overlap because the
target ground vector has phase `I`. It also has an excited component, so the
estimates test Gaussian suppression as well as conjugation. The tests include
zero variance, unrenormalized truncation, and the real-overlap contraction result.

The shifted-projector fixture adapts `QICLeanTest/GaussianSpectralGap.lean` and
`QICLeanTest/PositiveGapUniqueness.lean`; all estimates below concern the actual
integral, with no coefficient identity supplied as a hypothesis.
-/

open Complex Matrix GaussianFilter
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal ComplexOrder

namespace GaussianGroundEstimateTest

variable {n : Type*} [Fintype n] [DecidableEq n]

private noncomputable def H (Ω : EuclideanSpace ℂ n) : Matrix n n ℂ :=
  ((-7 : ℝ) : ℂ) • 1 + ((2 : ℝ) : ℂ) •
    (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))

omit [Fintype n] in
private theorem hermitian (Ω : EuclideanSpace ℂ n) : (H Ω).IsHermitian := by
  have hp : (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))).IsHermitian := by
    rw [IsHermitian, conjTranspose_vecMulVec, star_star]
  exact (isHermitian_one.smul (Complex.conj_ofReal (-7))).add
    ((isHermitian_one.sub hp).smul (Complex.conj_ofReal 2))

omit [Fintype n] in
private theorem gap (Ω : EuclideanSpace ℂ n) :
    (H Ω - ((-7 : ℝ) : ℂ) • 1 - ((2 : ℝ) : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
  rw [H, add_sub_cancel_left, sub_self]
  exact PosSemidef.zero

private theorem ground (Ω : EuclideanSpace ℂ n) (hΩ : ‖Ω‖ = 1) :
    H Ω *ᵥ WithLp.ofLp Ω = ((-7 : ℝ) : ℂ) • WithLp.ofLp Ω := by
  have hself : ⟪Ω, Ω⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hlin : toEuclideanLin (H Ω) Ω = ((-7 : ℝ) : ℂ) • Ω := by
    simp only [H, map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, toLpLin_one, LinearMap.id_apply,
      toEuclideanLin_vecMulVec_star_self_apply, hself, one_smul, sub_self, smul_zero,
      add_zero]
  exact congrArg WithLp.ofLp hlin

private noncomputable def Ψ : EuclideanSpace ℂ Bool := PiLp.single 2 false 1

private noncomputable def Φ : EuclideanSpace ℂ Bool := I • PiLp.single 2 true 1

private def W : Matrix Bool Bool ℂ := fun _ _ => 1

private theorem norm_Ψ : ‖Ψ‖ = 1 := by simp [Ψ]

private theorem norm_Φ : ‖Φ‖ = 1 := by simp [Φ, norm_smul]

private theorem overlap : ⟪Φ, toEuclideanLin W Ψ⟫_ℂ = -I := by
  rw [Φ, inner_smul_left, EuclideanSpace.inner_single_left]
  change star I * (star (1 : ℂ) * (W *ᵥ Pi.single false 1) true) = -I
  simp [W]

-- A Hermitian input with unit ground vectors does not force a real overlap.
example : W.IsHermitian ∧ ⟪Φ, toEuclideanLin W Ψ⟫_ℂ ≠
    star ⟪Φ, toEuclideanLin W Ψ⟫_ℂ := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp [W, Matrix.conjTranspose_apply]
  · rw [overlap]
    intro heq
    have him := congrArg Complex.im heq
    norm_num at him

-- Both actual integral bounds use the right phase: -I forward and +I backward.
example :
    ‖toEuclideanLin (gaussianIntertwiner 2 (H Φ) (H Ψ) W) Ψ - (-I) • Φ‖ ≤
        Real.exp (-4) * ‖W‖ ∧
      ‖toEuclideanLin (gaussianIntertwiner 2 (H Φ) (H Ψ) W)ᴴ Φ - I • Ψ‖ ≤
        Real.exp (-4) * ‖W‖ := by
  have h := gaussianIntertwiner_two_sided_ground_estimate 2 (hermitian Φ) (hermitian Ψ) W
    norm_Ψ norm_Φ (ground Ψ norm_Ψ) (ground Φ norm_Φ) (gap Ψ) (gap Φ) two_pos
  norm_num [overlap, Complex.star_def] at h ⊢
  exact h

-- Zero variance is a supported endpoint, without a density or positive-width assumption.
example : ‖toEuclideanLin W Ψ - (-I) • Φ‖ ≤ ‖W‖ ∧
    ‖toEuclideanLin Wᴴ Φ - I • Ψ‖ ≤ ‖W‖ := by
  have h := gaussianIntertwiner_two_sided_ground_estimate 0 (hermitian Φ) (hermitian Ψ) W
    norm_Ψ norm_Φ (ground Ψ norm_Ψ) (ground Φ norm_Φ) (gap Ψ) (gap Φ) two_pos
  simpa [overlap, Complex.star_def] using h

-- At variance 2 and cutoff 3, the two-sided error is the residual plus 2 exp(-9/4).
example :
    let ε := (Real.exp (-4) + 2 * Real.exp (-(9 / 4 : ℝ))) * ‖W‖
    ‖toEuclideanLin (gaussianIntertwinerTruncated 2 3 (H Φ) (H Ψ) W) Ψ - (-I) • Φ‖ ≤ ε ∧
      ‖toEuclideanLin (gaussianIntertwinerTruncated 2 3 (H Φ) (H Ψ) W)ᴴ Φ - I • Ψ‖ ≤ ε := by
  have h := gaussianIntertwinerTruncated_two_sided_ground_estimate 2
    (by norm_num : (0 : ℝ) ≤ 3) (hermitian Φ) (hermitian Ψ) W
    norm_Ψ norm_Φ (ground Ψ norm_Ψ) (ground Φ norm_Φ) (gap Ψ) (gap Φ) two_pos
  norm_num [overlap, Complex.star_def] at h ⊢
  exact h

-- The real-overlap result yields both manuscript estimates and the operator contraction.
example (h : ℝ≥0) :
    ‖gaussianIntertwiner h (H Ψ) (H Ψ) 1‖ ≤ 1 ∧
      ‖toEuclideanLin (gaussianIntertwiner h (H Ψ) (H Ψ) 1) Ψ - Ψ‖ ≤
        Real.exp (-(h : ℝ) * 2 ^ 2 / 2) ∧
      ‖toEuclideanLin (gaussianIntertwiner h (H Ψ) (H Ψ) 1)ᴴ Ψ - Ψ‖ ≤
        Real.exp (-(h : ℝ) * 2 ^ 2 / 2) := by
  have hz : ⟪Ψ, toEuclideanLin (1 : Matrix Bool Bool ℂ) Ψ⟫_ℂ = (1 : ℂ) := by
    simp [inner_self_eq_norm_sq_to_K, norm_Ψ]
  simpa using gaussianIntertwiner_two_sided_of_real_overlap h (hermitian Ψ) (hermitian Ψ)
    (by simp : ‖(1 : Matrix Bool Bool ℂ)‖ ≤ 1) norm_Ψ norm_Ψ
    (ground Ψ norm_Ψ) (ground Ψ norm_Ψ) (gap Ψ) (gap Ψ) two_pos hz

end GaussianGroundEstimateTest

/--
info: 'GaussianFilter.norm_gaussianIntertwiner_ground_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwiner_ground_le

/--
info: 'GaussianFilter.gaussianIntertwiner_two_sided_ground_estimate' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwiner_two_sided_ground_estimate

/--
info: 'GaussianFilter.gaussianIntertwiner_two_sided_of_real_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwiner_two_sided_of_real_overlap

/--
info: 'GaussianFilter.norm_gaussianIntertwinerTruncated_ground_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.norm_gaussianIntertwinerTruncated_ground_le

/--
info: 'GaussianFilter.gaussianIntertwinerTruncated_two_sided_ground_estimate' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms GaussianFilter.gaussianIntertwinerTruncated_two_sided_ground_estimate
