/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceSymmetry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Subspaces constructed from approximations to an orthonormal basis

The actual linear map taking a target orthonormal basis to prescribed
approximating vectors is controlled by their summed squared errors.
A total error below one makes this map injective; its actual range has
the target dimension and approximates the target in both directions.
The zero-dimensional target is included.

These are finite-dimensional auxiliaries for the mathematical basis
consequence of ALVV, arXiv:1602.08828v2, introductory statement at line 288
and Theorem `thm:al-ld`, lines 1096–1105. They construct no Hamiltonian
filter and make no algorithmic claim. Closeness is the source's
Definition `d:close`, lines 469–474.
-/

open scoped BigOperators InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- The actual basis-defined map differs from inclusion by at most the
summed squared basis errors times the input squared norm. This is a
finite Cauchy--Schwarz estimate used for the basis consequence of ALVV,
arXiv:1602.08828v2, line 288 and Theorem `thm:al-ld`, lines 1096–1105. -/
theorem norm_constr_sub_sq_le_sum
    (T : Submodule 𝕜 E) (b : OrthonormalBasis ι 𝕜 T) (phi : ι → E) (x : T) :
    ‖b.toBasis.constr 𝕜 phi x - (x : E)‖ ^ 2 ≤
      (∑ i, ‖phi i - (b i : E)‖ ^ 2) * ‖x‖ ^ 2 := by
  classical
  have hx : ∑ i, b.repr x i • (b i : E) = (x : E) := by
    have h := congrArg (fun y : T ↦ (y : E)) (b.sum_repr x)
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
  have hF : b.toBasis.constr 𝕜 phi x = ∑ i, b.repr x i • phi i := by
    simp only [Module.Basis.constr_apply_fintype, Module.Basis.equivFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply]
  have herror : b.toBasis.constr 𝕜 phi x - (x : E) =
      ∑ i, b.repr x i • (phi i - (b i : E)) := by
    rw [hF, ← hx]
    simp only [smul_sub, Finset.sum_sub_distrib]
  have hn : ‖b.toBasis.constr 𝕜 phi x - (x : E)‖ ≤
      ∑ i, ‖b.repr x i‖ * ‖phi i - (b i : E)‖ := by
    rw [herror]
    exact (norm_sum_le _ _).trans_eq (by simp only [norm_smul])
  have hcoeff : (∑ i, ‖b.repr x i‖ ^ 2) = ‖x‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, b.repr.norm_map]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i ↦ ‖b.repr x i‖) (fun i ↦ ‖phi i - (b i : E)‖)
  have hs := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hCS
  rw [hcoeff, mul_comm] at hs
  exact hs

variable [FiniteDimensional 𝕜 E]

/-- Summed squared errors below one make the actual basis-defined map
injective. Its range has the target dimension, is the actual span of the
prescribed vectors, and approximates the target in both directions.
A finite-dimensional auxiliary for ALVV, arXiv:1602.08828v2, line 288
and Theorem `thm:al-ld`, lines 1096–1105. The target and prescribed vectors are arbitrary. -/
theorem range_constr_isCloseTo_of_sum_norm_sq_le
    (T : Submodule 𝕜 E) (b : OrthonormalBasis ι 𝕜 T) (phi : ι → E)
    (delta : ℝ) (hdelta : delta < 1)
    (hsum : (∑ i, ‖phi i - (b i : E)‖ ^ 2) ≤ delta) :
    let F := b.toBasis.constr 𝕜 phi
    let V := LinearMap.range F
    Function.Injective F ∧ Module.finrank 𝕜 V = Module.finrank 𝕜 T ∧
      V = Submodule.span 𝕜 (Set.range phi) ∧
      Submodule.IsCloseTo delta V T ∧ Submodule.IsCloseTo delta T V := by
  classical
  intro F V
  have herr (x : T) : ‖F x - (x : E)‖ ^ 2 ≤ delta * ‖x‖ ^ 2 :=
    (b.norm_constr_sub_sq_le_sum T phi x).trans
      (mul_le_mul_of_nonneg_right hsum (sq_nonneg _))
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h := herr x
    rw [hx, zero_sub, norm_neg] at h
    change ‖x‖ ^ 2 ≤ delta * ‖x‖ ^ 2 at h
    by_contra hne
    have hpos := mul_pos (sub_pos.mpr hdelta) (sq_pos_of_pos (norm_pos_iff.mpr hne))
    nlinarith only [h, hpos]
  have hdim : Module.finrank 𝕜 V = Module.finrank 𝕜 T :=
    LinearMap.finrank_range_of_inj hinj
  have hspan : V = Submodule.span 𝕜 (Set.range phi) := b.toBasis.constr_range 𝕜
  have hclose : Submodule.IsCloseTo delta V T := by
    apply Submodule.isCloseTo_iff.mpr
    intro x hx
    let t : T := ⟨x, hx⟩
    have hmin : ‖x - V.starProjection x‖ ≤ ‖x - F t‖ := by
      rw [Submodule.starProjection_minimal]
      change _ ≤ ‖x - (⟨F t, ⟨t, rfl⟩⟩ : V)‖
      exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ ↦ norm_nonneg _⟩ _
    have herror : ‖x - V.starProjection x‖ ^ 2 ≤ delta * ‖x‖ ^ 2 := by
      have h := herr t
      rw [norm_sub_rev] at h
      exact (pow_le_pow_left₀ (norm_nonneg _) hmin 2).trans h
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection x V
    rw [Submodule.starProjection_orthogonal] at hpy
    simp only [sub_apply, ContinuousLinearMap.id_apply] at hpy
    nlinarith only [herror, hpy]
  exact ⟨hinj, hdim, hspan, hclose, hclose.symm_of_finrank_eq hdim⟩

end OrthonormalBasis
