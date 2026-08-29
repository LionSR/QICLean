/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.EigenspaceMap
import QICLean.Channel.Semigroup.Primitivity.Helpers

/-!
# Spectral mapping for exponential semigroups

This file supplies the reverse spectral information needed in Wolf Proposition
7.5.  Forward spectral mapping alone does not control the multiplicity of the
fixed eigenvalue of an exponential.

## Main results

* `exists_generator_eigenvalue_of_expSemigroup_hasEigenvalue`: every
  eigenvalue of `exp(tL)` is the exponential of an eigenvalue of `L`.
* `exists_nonzero_generator_eigenvalue_of_expSemigroup_fixed_not_generator_fixed`:
  a fixed vector of `exp(tL)` which does not belong to `ker L` produces a
  nonzero eigenvalue `μ` of `L` satisfying `exp(tμ) = 1`.

The second statement records the multiplicity information used in Wolf
Chapter 7, Proposition 7.5, lines 279--280.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators NNReal TNOperatorSpace
open Matrix Finset NormedSpace TNLean

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The generator commutes with each member of its exponential semigroup. -/
theorem generator_comm_expSemigroup
    (L : Mat →ₗ[ℂ] Mat) (t : ℝ) :
    Commute L (expSemigroup L t) := by
  rw [Commute]
  apply endEquiv.injective
  rw [map_mul, map_mul, expSemigroup_toCLM]
  exact (expSemigroupCLM_mul_generator_comm (endEquiv L) t).symm

/-- **Reverse spectral mapping for eigenvalues.** Every eigenvalue `λ` of
`exp(tL)` is `exp(tμ)` for an eigenvalue `μ` of the generator `L`.

The `λ`-eigenspace of `exp(tL)` is invariant under `L`.  Restricting `L` to
that nonzero finite-dimensional space gives an eigenvector common to both
operators, and forward spectral mapping on this vector identifies `λ`. -/
theorem exists_generator_eigenvalue_of_expSemigroup_hasEigenvalue
    (L : Mat →ₗ[ℂ] Mat) (t : ℝ) (ν : ℂ)
    (hν : Module.End.HasEigenvalue (expSemigroup L t) ν) :
    ∃ μ : ℂ, Module.End.HasEigenvalue L μ ∧
      Complex.exp ((t : ℂ) * μ) = ν := by
  obtain ⟨X, hX⟩ := hν.exists_hasEigenvector
  have hEX : expSemigroup L t X = ν • X :=
    Module.End.mem_eigenspace_iff.mp hX.1
  let q : Module.End ℂ Mat := expSemigroup L t - ν • 1
  have hqX : q X = 0 := by
    simp [q, hEX]
  have hLq : Commute L q := by
    exact (generator_comm_expSemigroup L t).sub_right
      ((Commute.one_right L).smul_right ν)
  obtain ⟨μ, Y, hY_ne, hqY, hLY⟩ :=
    Module.End.exists_eigenvector_mem_ker_of_commute L q hLq hX.2 hqX
  have hEY : expSemigroup L t Y = ν • Y := by
    apply sub_eq_zero.mp
    simpa [q] using hqY
  have hExpY := expSemigroup_apply_eigenvector L Y μ hLY t
  have hscalar : Complex.exp ((t : ℂ) * μ) = ν := by
    have hsmul : (Complex.exp ((t : ℂ) * μ) - ν) • Y = 0 := by
      rw [sub_smul, ← hExpY, hEY, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hY_ne)
  exact ⟨μ, hasEigenvalue_of_eigenvector_eq L μ Y hLY hY_ne, hscalar⟩

/-- If `L Y = 0`, then the integral of its exponential semigroup sends `Y`
to `t Y`. -/
theorem intervalIntegral_expSemigroupCLM_apply_of_generator_apply_eq_zero
    (L : Mat →ₗ[ℂ] Mat) (t : ℝ) {Y : Mat} (hLY : L Y = 0) :
    intervalIntegral (fun s : ℝ => expSemigroupCLM (endEquiv L) s)
        0 t MeasureTheory.volume Y = (t : ℂ) • Y := by
  let evalY : MatrixCLM (Fin D) →L[ℝ] Mat :=
    (ContinuousLinearMap.apply ℂ Mat Y).restrictScalars ℝ
  have hInt : IntervalIntegrable
      (fun s : ℝ => expSemigroupCLM (endEquiv L) s)
      MeasureTheory.volume 0 t :=
    (expSemigroupCLM_continuous (endEquiv L)).intervalIntegrable 0 t
  have hfix (s : ℝ) : expSemigroupCLM (endEquiv L) s Y = Y := by
    change expSemigroup L s Y = Y
    rw [expSemigroup_apply_eigenvector L Y 0 (by simpa using hLY)]
    simp
  calc
    intervalIntegral (fun s : ℝ => expSemigroupCLM (endEquiv L) s)
          0 t MeasureTheory.volume Y =
        evalY (intervalIntegral (fun s : ℝ => expSemigroupCLM (endEquiv L) s)
          0 t MeasureTheory.volume) := rfl
    _ = intervalIntegral
          (fun s : ℝ => evalY (expSemigroupCLM (endEquiv L) s))
          0 t MeasureTheory.volume := (evalY.intervalIntegral_comp_comm hInt).symm
    _ = intervalIntegral (fun _ : ℝ => Y) 0 t MeasureTheory.volume := by
          exact intervalIntegral.integral_congr fun s _ => hfix s
    _ = (t : ℂ) • Y := by
          simp [intervalIntegral.integral_const]

/-- **Reverse fixed-space resonance.** Let `t ≠ 0`. If `X` is fixed by
`exp(tL)` but `L X ≠ 0`, then `L` has a nonzero eigenvalue `μ` satisfying
`exp(tμ) = 1`.

Write `P_t = ∫₀ᵗ exp(sL) ds`.  The factorization
`exp(tL)-1 = P_t L` places `L X` in `ker P_t`.  Since `P_t` commutes with `L`,
this kernel contains an eigenvector of `L`.  Its eigenvalue cannot vanish,
because `P_t` acts as multiplication by `t` on `ker L`. -/
theorem exists_nonzero_generator_eigenvalue_of_expSemigroup_fixed_not_generator_fixed
    (L : Mat →ₗ[ℂ] Mat) (t : ℝ) (ht : t ≠ 0) {X : Mat}
    (hX_fix : expSemigroup L t X = X) (hLX_ne : L X ≠ 0) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Module.End.HasEigenvalue L μ ∧
      Complex.exp ((t : ℂ) * μ) = 1 := by
  let L' : MatrixCLM (Fin D) := endEquiv L
  let P : MatrixCLM (Fin D) :=
    intervalIntegral (fun s : ℝ => expSemigroupCLM L' s)
      0 t MeasureTheory.volume
  have hPLX : P (L X) = 0 := by
    have hzero : (expSemigroupCLM L' t - 1) X = 0 := by
      have hX_fix' : expSemigroupCLM L' t X = X := by
        change endEquiv (expSemigroup L t) X = X
        rw [expSemigroup_toCLM]
        exact hX_fix
      simpa using sub_eq_zero.mpr hX_fix'
    rw [expSemigroupCLM_sub_one_eq_intervalIntegral_mul] at hzero
    change P (L' X) = 0
    simpa [P] using hzero
  have hLP : Commute L P.toLinearMap := by
    rw [Commute]
    apply LinearMap.ext
    intro Y
    change endEquiv L (P Y) = P (endEquiv L Y)
    have hcomm := DFunLike.congr_fun
      (intervalIntegral_expSemigroupCLM_mul_generator_comm L' t).symm Y
    simpa [L', P, Module.End.mul_eq_comp, LinearMap.comp_apply,
      mul_apply_eq_comp] using hcomm
  obtain ⟨μ, Y, hY_ne, hPY, hLY⟩ :=
    Module.End.exists_eigenvector_mem_ker_of_commute
      L P.toLinearMap hLP hLX_ne hPLX
  have hμ_ne : μ ≠ 0 := by
    intro hμ
    subst μ
    have hLY_zero : L Y = 0 := by simpa using hLY
    have hPY_eq :=
      intervalIntegral_expSemigroupCLM_apply_of_generator_apply_eq_zero L t hLY_zero
    have ht_complex : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    apply hY_ne
    apply (smul_eq_zero.mp ?_).resolve_left ht_complex
    rw [← hPY_eq]
    exact hPY
  have hY_fix : expSemigroup L t Y = Y := by
    have hPY' : P Y = 0 := hPY
    have hzero : (expSemigroupCLM L' t - 1) Y = 0 := by
      rw [expSemigroupCLM_sub_one_eq_intervalIntegral_mul]
      change P (L Y) = 0
      rw [hLY, map_smul, hPY', smul_zero]
    have hfix' : expSemigroupCLM L' t Y = Y := sub_eq_zero.mp hzero
    change endEquiv (expSemigroup L t) Y = Y
    rw [expSemigroup_toCLM]
    exact hfix'
  have hExpY := expSemigroup_apply_eigenvector L Y μ hLY t
  have hroot : Complex.exp ((t : ℂ) * μ) = 1 := by
    have hsmul : (Complex.exp ((t : ℂ) * μ) - 1) • Y = 0 := by
      rw [sub_smul, one_smul, ← hExpY, hY_fix, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_right hY_ne)
  exact ⟨μ, hμ_ne, hasEigenvalue_of_eigenvector_eq L μ Y hLY hY_ne, hroot⟩

end -- noncomputable section
