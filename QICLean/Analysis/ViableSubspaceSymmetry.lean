/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Symmetry of closeness in equal dimension

For two finite-dimensional subspaces of the same dimension, the squared
projection loss is the same in both directions. This is the geometric
symmetry used when comparing the Ritz space and the original ground space
in ALVV, arXiv:1602.08828v2, Definition `d:close`, lines 469–474, and the
last step of `t:alg1`, lines 1811–1817. No Hamiltonian conclusion is assumed.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Closeness is symmetric for subspaces of equal dimension, with the same
squared error. This supports the equal-dimension ground-space comparison
in ALVV, arXiv:1602.08828v2, Definition `d:close` and `t:alg1`, lines 1811–1817.
Zero subspaces and arbitrary real error parameters are included. -/
theorem IsCloseTo.symm_of_finrank_eq {δ : ℝ} {U T : Submodule 𝕜 E}
    (h : IsCloseTo δ U T) (hdim : Module.finrank 𝕜 U = Module.finrank 𝕜 T) :
    IsCloseTo δ T U := by
  by_cases hδ : δ < 1
  · have hc : 0 < 1 - δ := sub_pos.mpr hδ
    have hvec := isCloseTo_iff.mp h
    let f : T →ₗ[𝕜] U := U.orthogonalProjectionOnto.toLinearMap.comp T.subtype
    have hfinj : Function.Injective f := by
      apply LinearMap.ker_eq_bot.mp
      apply eq_bot_iff.mpr
      intro t ht
      have hzero : U.starProjection (t : E) = 0 := by
        have heq := congrArg Subtype.val (LinearMap.mem_ker.mp ht)
        exact heq
      have hsq : ‖(t : E)‖ ^ 2 ≤ 0 := by
        apply _root_.le_of_mul_le_mul_left ?_ hc
        simpa only [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
          hvec t t.property
      have htzero : (t : E) = 0 := by
        apply norm_eq_zero.mp
        nlinarith only [hsq, norm_nonneg (t : E)]
      simpa only [Submodule.mem_bot] using (Subtype.ext htzero : t = 0)
    have hfsurj : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mp hfinj
    apply isCloseTo_iff.mpr
    intro u hu
    by_cases hu0 : u = 0
    · simp only [hu0, map_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
        le_refl]
    obtain ⟨t, ht⟩ := hfsurj ⟨u, hu⟩
    have hproj : U.starProjection (t : E) = u := congrArg Subtype.val ht
    have htnorm : (1 - δ) * ‖(t : E)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      simpa only [hproj] using hvec t t.property
    have hpair : ⟪(t : E), u⟫_𝕜 = ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
      calc
        ⟪(t : E), u⟫_𝕜 = ⟪U.starProjection (t : E), u⟫_𝕜 := by
          rw [U.inner_starProjection_left_eq_right, U.starProjection_eq_self_iff.mpr hu]
        _ = ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
          rw [hproj, inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
    have hpairT : ⟪(t : E), T.starProjection u⟫_𝕜 = ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
      rw [← T.inner_starProjection_left_eq_right,
        T.starProjection_eq_self_iff.mpr t.property]
      exact hpair
    have hCS : ‖u‖ ^ 2 ≤ ‖(t : E)‖ * ‖T.starProjection u‖ := by
      have hbound := re_inner_le_norm (𝕜 := 𝕜) (t : E) (T.starProjection u)
      rwa [hpairT, RCLike.ofReal_re] at hbound
    have hsq : (‖u‖ ^ 2) ^ 2 ≤ ‖(t : E)‖ ^ 2 * ‖T.starProjection u‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (sq_nonneg ‖u‖) hCS 2
    have hprod : ((1 - δ) * ‖u‖ ^ 2) * ‖u‖ ^ 2 ≤
        ‖T.starProjection u‖ ^ 2 * ‖u‖ ^ 2 := by
      calc
        _ = (1 - δ) * (‖u‖ ^ 2) ^ 2 := by simp only [pow_two, mul_assoc]
        _ ≤ (1 - δ) * (‖(t : E)‖ ^ 2 * ‖T.starProjection u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hc.le
        _ = ((1 - δ) * ‖(t : E)‖ ^ 2) * ‖T.starProjection u‖ ^ 2 :=
          (mul_assoc _ _ _).symm
        _ ≤ ‖u‖ ^ 2 * ‖T.starProjection u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right htnorm (sq_nonneg _)
        _ = ‖T.starProjection u‖ ^ 2 * ‖u‖ ^ 2 := mul_comm _ _
    exact _root_.le_of_mul_le_mul_right hprod (sq_pos_of_pos (norm_pos_iff.mpr hu0))
  · apply isCloseTo_iff.mpr
    intro u _hu
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hδ))
      (sq_nonneg ‖u‖)).trans (sq_nonneg _)

end Submodule
