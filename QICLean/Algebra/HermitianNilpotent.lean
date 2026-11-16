/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixSpectralDecomp
import QICLean.Algebra.HermitianHelpers
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Hermitian functionals and rank-one nilpotent maps

Two Hermitian matrices in dimension at least two have a common nonzero
complex-linear annihilating functional that is real on Hermitian inputs.
This constructs a Hermitian-preserving, trace-zero nilpotent map whose
composition with a supplied linear map remains nonzero.

These are algebraic ingredients for the coupled-corner root-selection
argument associated with arXiv:1708.00029, Theorem 4.1. They do not assert
complete positivity or support inside a prescribed Choi face.
-/

namespace Matrix

private theorem recover_isometric_congruence {b : ℕ}
    (V : Matrix (Fin b) (Fin b) ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix (Fin b) (Fin b) ℂ) : Vᴴ * (V * X * Vᴴ) * V = X := by
  calc
    Vᴴ * (V * X * Vᴴ) * V = (Vᴴ * V) * X * (Vᴴ * V) := by
      simp only [Matrix.mul_assoc]
    _ = X := by rw [hV, Matrix.one_mul, Matrix.mul_one]

/-- Two Hermitian matrices in dimension at least two admit a common
nonzero complex-linear annihilating functional, real on Hermitian inputs.
Diagonalize the first matrix and combine two independent off-diagonal
Hermitian functionals to kill the second. This is the functional step in
the written coupled-corner construction for arXiv:1708.00029, Theorem 4.1. -/
theorem exists_hermitian_functional_killing_pair {b : ℕ} (hb : 2 ≤ b)
    (ρ u : Matrix (Fin b) (Fin b) ℂ) (hρ : ρ.IsHermitian) (hu : u.IsHermitian) :
    ∃ φ : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] ℂ,
      φ ≠ 0 ∧ φ ρ = 0 ∧ φ u = 0 ∧
      (∀ X, X.IsHermitian → IsSelfAdjoint (φ X)) := by
  classical
  let i : Fin b := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hb⟩
  let j : Fin b := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hb⟩
  have hij : i ≠ j := by
    intro h
    have h' := congrArg Fin.val h
    norm_num [i, j] at h'
  let V := hρ.eigenvectorUnitary
  let Vm : Matrix (Fin b) (Fin b) ℂ := V
  have hV : Vmᴴ * Vm = 1 := by
    simpa only [Vm, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  let Dg : Matrix (Fin b) (Fin b) ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ hρ.eigenvalues)
  have hρeq : ρ = Vm * Dg * Vmᴴ := by
    simpa only [Vm, V, Dg, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Function.comp_def] using hρ.spectral_theorem
  have hCompρ : Vmᴴ * ρ * Vm = Dg := by
    rw [hρeq]
    exact recover_isometric_congruence Vm hV Dg
  let C : Module.End ℂ (Matrix (Fin b) (Fin b) ℂ) :=
    { toFun := fun X => Vmᴴ * X * Vm
      map_add' := by intros; rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hC (X : Matrix (Fin b) (Fin b) ℂ) : C X = Vmᴴ * X * Vm := rfl
  have hRecover (X : Matrix (Fin b) (Fin b) ℂ) : C (Vm * X * Vmᴴ) = X :=
    recover_isometric_congruence Vm hV X
  let e (k l : Fin b) : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => X k l
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let f := (e i j + e j i) ∘ₗ C
  let g := Complex.I • ((e i j - e j i) ∘ₗ C)
  have hf (X : Matrix (Fin b) (Fin b) ℂ) : f X = (C X) i j + (C X) j i := rfl
  have hg (X : Matrix (Fin b) (Fin b) ℂ) :
      g X = Complex.I * ((C X) i j - (C X) j i) := rfl
  have hfρ : f ρ = 0 := by
    simp only [hf, hC, hCompρ]
    simp [Dg, hij, hij.symm]
  have hgρ : g ρ = 0 := by
    simp only [hg, hC, hCompρ]
    simp [Dg, hij, hij.symm]
  have hfHerm (X : Matrix (Fin b) (Fin b) ℂ) (hX : X.IsHermitian) :
      IsSelfAdjoint (f X) := by
    have hY := Matrix.isHermitian_conjTranspose_mul_mul Vm hX
    change star (f X) = f X
    simp only [hf, hC, star_add, hY.apply i j, hY.apply j i]
    ring
  have hgHerm (X : Matrix (Fin b) (Fin b) ℂ) (hX : X.IsHermitian) :
      IsSelfAdjoint (g X) := by
    have hY := Matrix.isHermitian_conjTranspose_mul_mul Vm hX
    change star (g X) = g X
    simp only [hg, hC, star_mul, star_sub, hY.apply i j, hY.apply j i]
    rw [Complex.star_def, Complex.conj_I]
    ring
  have hfOne : f (Vm * Matrix.single i j 1 * Vmᴴ) = 1 := by
    rw [hf, hRecover]
    simp [hij, hij.symm]
  have hfne : f ≠ 0 := by
    intro h
    have hh := congrArg
      (fun L : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] ℂ =>
        L (Vm * Matrix.single i j 1 * Vmᴴ)) h
    have hOne : (1 : ℂ) = 0 := by
      simpa only [hfOne, LinearMap.zero_apply] using hh
    exact one_ne_zero hOne
  by_cases hfu : f u = 0
  · exact ⟨f, hfne, hfρ, hfu, hfHerm⟩
  · let Z : Matrix (Fin b) (Fin b) ℂ :=
      (-Complex.I / 2) • (Matrix.single i j 1 - Matrix.single j i 1)
    have hfZ : f (Vm * Z * Vmᴴ) = 0 := by
      rw [hf, hRecover]
      norm_num [Z, Matrix.smul_apply, Matrix.sub_apply, hij, hij.symm, smul_eq_mul]
    have hgZ : g (Vm * Z * Vmᴴ) = 1 := by
      rw [hg, hRecover]
      norm_num [Z, Matrix.smul_apply, Matrix.sub_apply, hij, hij.symm, smul_eq_mul,
        Complex.I_sq]
    let φ := g u • f - f u • g
    refine ⟨φ, ?_, ?_, ?_, ?_⟩
    · intro h
      have hh := congrArg
        (fun L : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] ℂ => L (Vm * Z * Vmᴴ)) h
      change g u * f (Vm * Z * Vmᴴ) - f u * g (Vm * Z * Vmᴴ) = 0 at hh
      rw [hfZ, hgZ, mul_zero, mul_one, zero_sub] at hh
      exact hfu (neg_eq_zero.mp hh)
    · change g u * f ρ - f u * g ρ = 0
      rw [hfρ, hgρ, mul_zero, mul_zero, sub_self]
    · change g u * f u - f u * g u = 0
      ring
    · intro X hX
      have hgu : star (g u) = g u := hgHerm u hu
      have hfu' : star (f u) = f u := hfHerm u hu
      have hgX : star (g X) = g X := hgHerm X hX
      have hfX : star (f X) = f X := hfHerm X hX
      change star (g u * f X - f u * g X) = g u * f X - f u * g X
      rw [star_sub, star_mul, star_mul, hgu, hfu', hgX, hfX]
      ring

/-- A nonzero image of a traceless Hermitian direction gives a rank-one
Hermitian-preserving nilpotent endomorphism with zero output trace that
kills a prescribed Hermitian matrix. The supplied linear map does not
annihilate this endomorphism. This is an algebraic construction; it makes
no complete-positivity or Choi-support assertion. -/
theorem exists_trace_zero_nilpotent_of_traceless_hermitian_image {b c : ℕ}
    (hb : 2 ≤ b) (ρ u : Matrix (Fin b) (Fin b) ℂ)
    (hρ : ρ.IsHermitian) (hu : u.IsHermitian) (hTr : u.trace = 0)
    (Q : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin c) (Fin c) ℂ)
    (hQu : Q u ≠ 0) :
    ∃ H : Module.End ℂ (Matrix (Fin b) (Fin b) ℂ),
      H ρ = 0 ∧ H * H = 0 ∧ (∀ X, (H X).trace = 0) ∧
      (∀ X, X.IsHermitian → (H X).IsHermitian) ∧ Q ∘ₗ H ≠ 0 := by
  obtain ⟨φ, hφne, hφρ, hφu, hφHerm⟩ :=
    exists_hermitian_functional_killing_pair hb ρ u hρ hu
  let H := φ.smulRight u
  have hH (X : Matrix (Fin b) (Fin b) ℂ) : H X = φ X • u := rfl
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hH, hφρ, zero_smul]
  · ext X : 1
    change H (H X) = 0
    rw [hH, hH, map_smul, hφu, smul_zero, zero_smul]
  · intro X
    rw [hH, Matrix.trace_smul, hTr, smul_zero]
  · intro X hX
    rw [hH]
    exact hu.smul (hφHerm X hX)
  · intro hZero
    apply hφne
    ext X : 1
    change φ X = 0
    have h := congrArg
      (fun L : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin c) (Fin c) ℂ => L X) hZero
    change Q (φ X • u) = 0 at h
    rw [map_smul] at h
    exact (smul_eq_zero.mp h).resolve_right hQu

/-- If a complex-linear map is not trace preparation from a fixed
trace-one Hermitian matrix, it does not annihilate every traceless
Hermitian matrix. This uses complex linearity, without positivity of
either the reference matrix or the map. -/
theorem exists_traceless_hermitian_image_of_not_trace_preparation {b c : ℕ}
    (ρ : Matrix (Fin b) (Fin b) ℂ) (hρ : ρ.IsHermitian) (hTrρ : ρ.trace = 1)
    (Q : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin c) (Fin c) ℂ)
    (hQ : ¬ ∀ X, Q X = X.trace • Q ρ) :
    ∃ u : Matrix (Fin b) (Fin b) ℂ,
      u.IsHermitian ∧ u.trace = 0 ∧ Q u ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hHerm (Y : Matrix (Fin b) (Fin b) ℂ) (hY : Y.IsHermitian) :
      Q Y = Y.trace • Q ρ := by
    have hTraceSelf : IsSelfAdjoint Y.trace := by
      change star Y.trace = Y.trace
      rw [← Matrix.trace_conjTranspose, hY.eq]
    have hZero : Q (Y - Y.trace • ρ) = 0 := by
      apply h
      · exact hY.sub (hρ.smul hTraceSelf)
      · rw [Matrix.trace_sub, Matrix.trace_smul, hTrρ, smul_eq_mul,
          mul_one, sub_self]
    rw [map_sub, map_smul] at hZero
    exact sub_eq_zero.mp hZero
  apply hQ
  intro X
  obtain ⟨H₁, H₂, hH₁, hH₂, hX⟩ := exists_isHermitian_eq_add_smul_I X
  rw [hX, map_add, map_smul, hHerm H₁ hH₁, hHerm H₂ hH₂,
    Matrix.trace_add, Matrix.trace_smul, add_smul, smul_smul, smul_eq_mul]

/-- A complex-linear map that is not trace preparation admits a
trace-zero Hermitian-preserving nilpotent direction which it does not
annihilate. The direction kills the supplied trace-one Hermitian
matrix. Complete positivity and Choi support remain separate conditions. -/
theorem exists_trace_zero_nilpotent_of_not_trace_preparation {b c : ℕ}
    (hb : 2 ≤ b) (ρ : Matrix (Fin b) (Fin b) ℂ)
    (hρ : ρ.IsHermitian) (hTrρ : ρ.trace = 1)
    (Q : Matrix (Fin b) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin c) (Fin c) ℂ)
    (hQ : ¬ ∀ X, Q X = X.trace • Q ρ) :
    ∃ H : Module.End ℂ (Matrix (Fin b) (Fin b) ℂ),
      H ρ = 0 ∧ H * H = 0 ∧ (∀ X, (H X).trace = 0) ∧
      (∀ X, X.IsHermitian → (H X).IsHermitian) ∧ Q ∘ₗ H ≠ 0 := by
  obtain ⟨u, hu, hTr, hQu⟩ :=
    exists_traceless_hermitian_image_of_not_trace_preparation ρ hρ hTrρ Q hQ
  exact exists_trace_zero_nilpotent_of_traceless_hermitian_image hb ρ u hρ hu hTr Q hQu

end Matrix
