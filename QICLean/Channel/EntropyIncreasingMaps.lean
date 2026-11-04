/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Jensen
import QICLean.Analysis.TraceCFC
import QICLean.Channel.Basic

/-!
# Entropy increasing positive maps

Wolf, Eq. (8.22), characterizes unital positive trace-preserving maps by increase of the
trace of any globally strictly concave function on density matrices. Positivity suffices;
neither complete positivity nor invertibility of the density matrix is required.
-/

open scoped BigOperators ComplexOrder
open Matrix

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] in
private lemma single_diagonal_posSemidef (j : n) :
    (single j j (1 : ℂ) : Matrix n n ℂ).PosSemidef := by
  rw [← diagonal_single]
  exact PosSemidef.diagonal fun i ↦ by simp [Pi.single_apply]; split_ifs <;> simp

private lemma diagonal_spectral_sum (a : n → ℝ) :
    diagonal (fun j ↦ (a j : ℂ)) = ∑ j, (a j : ℂ) • single j j (1 : ℂ) := by
  simp only [smul_single, smul_eq_mul, mul_one, sum_single_eq_diagonal]

private lemma trace_unitary_conj (u : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    trace (Unitary.conjStarAlgAut ℂ _ u A) = trace A := by
  rw [Unitary.conjStarAlgAut_apply, trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

private lemma positive_unitary_conj (u : unitary (Matrix n n ℂ)) :
    IsPositiveMap (Unitary.conjStarAlgAut ℂ _ u).toAlgEquiv.toLinearMap := by
  intro A hA
  simpa [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] using
    hA.mul_mul_conjTranspose_same (B := (u : Matrix n n ℂ))

/-- Scalar Jensen for the actual spectral coefficients of a positive, unital,
trace-preserving map, expressed in diagonal coordinates. -/
private lemma sum_concave_le_of_diagonal_map
    {S : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hS : IsPositiveMap S)
    (hS1 : S 1 = 1) (htr : IsTracePreservingMap S)
    {a b : n → ℝ} (hab : S (diagonal (fun j ↦ (a j : ℂ))) =
      diagonal (fun i ↦ (b i : ℂ)))
    {h : ℝ → ℝ} (hh : ConcaveOn ℝ Set.univ h) :
    ∑ j, h (a j) ≤ ∑ i, h (b i) := by
  let M : n → n → ℝ := fun i j ↦ (S (single j j 1) i i).re
  have hM : ∀ i j, 0 ≤ M i j := by
    intro i j
    exact (hS _ (single_diagonal_posSemidef j)).diag_nonneg (i := i) |>.1
  have hrow : ∀ i, ∑ j, M i j = 1 := by
    intro i
    have hs := congrArg (fun A : Matrix n n ℂ ↦ (A i i).re)
      ((map_sum S (fun j ↦ single j j (1 : ℂ)) Finset.univ).symm.trans
        ((congrArg S sum_single_one).trans hS1))
    simpa [M, Matrix.sum_apply, Complex.re_sum] using hs
  have hcol : ∀ j, ∑ i, M i j = 1 := by
    intro j
    have hs := congrArg Complex.re (htr (single j j 1))
    simpa [M, trace, Complex.re_sum] using hs
  have havg : ∀ i, ∑ j, M i j * a j = b i := by
    intro i
    rw [diagonal_spectral_sum, map_sum] at hab
    have hs := congrArg (fun A : Matrix n n ℂ ↦ (A i i).re) hab
    simpa only [Matrix.sum_apply, Complex.re_sum, map_smul, Matrix.smul_apply,
      smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, diagonal_apply_eq, M, mul_comm] using hs
  calc
    ∑ j, h (a j) = ∑ j, (∑ i, M i j) * h (a j) := by simp [hcol]
    _ = ∑ i, ∑ j, M i j * h (a j) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ ∑ i, h (b i) := by
      apply Finset.sum_le_sum
      intro i _
      have hj := hh.le_map_sum (t := Finset.univ) (p := a) (fun j _ ↦ hM i j)
        (hrow i) (fun _ _ ↦ Set.mem_univ _)
      simpa only [smul_eq_mul, havg] using hj

end Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive unital trace-preserving map increases the trace of every globally concave
function on every positive semidefinite matrix. This is the forward implication of Wolf
Eq. (8.22), without trace normalization or strict concavity. -/
theorem IsPositiveMap.trace_concave_le
    {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hT : IsPositiveMap T)
    (hT1 : T 1 = 1) (htr : IsTracePreservingMap T)
    {h : ℝ → ℝ} (hh : ConcaveOn ℝ Set.univ h)
    {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (trace (hA.isHermitian.cfc h)).re ≤
      (trace ((hT A hA).isHermitian.cfc h)).re := by
  let hB : (T A).IsHermitian := (hT A hA).isHermitian
  let U : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
    Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.isHermitian.eigenvectorUnitary
  let V : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
    Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hB.eigenvectorUnitary
  let S : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
    V.symm.toAlgEquiv.toLinearMap.comp (T.comp U.toAlgEquiv.toLinearMap)
  have hS : IsPositiveMap S := by
    intro X hX
    change (V.symm (T (U X))).PosSemidef
    rw [Unitary.conjStarAlgAut_symm]
    exact Matrix.positive_unitary_conj (star hB.eigenvectorUnitary) _
      (hT _ (Matrix.positive_unitary_conj hA.isHermitian.eigenvectorUnitary X hX))
  have hS1 : S 1 = 1 := by
    change V.symm (T (U 1)) = 1
    rw [map_one, hT1, map_one]
  have hStr : IsTracePreservingMap S := by
    intro X
    change trace (V.symm (T (U X))) = trace X
    rw [Unitary.conjStarAlgAut_symm, Matrix.trace_unitary_conj, htr,
      Matrix.trace_unitary_conj]
  have hab : S (diagonal (fun j ↦ (hA.isHermitian.eigenvalues j : ℂ))) =
      diagonal (fun i ↦ (hB.eigenvalues i : ℂ)) := by
    change V.symm (T (U _)) = _
    have hAU : U (diagonal (fun j ↦ (hA.isHermitian.eigenvalues j : ℂ))) = A :=
      hA.isHermitian.spectral_theorem.symm
    rw [hAU]
    exact V.symm_apply_eq.mpr hB.spectral_theorem
  rw [← RCLike.re_eq_complex_re, hA.isHermitian.trace_cfc_eq_sum_re,
    hB.trace_cfc_eq_sum_re]
  exact Matrix.sum_concave_le_of_diagonal_map hS hS1 hStr hab hh

namespace Matrix.IsHermitian

private lemma sum_eigenvalues_trace_one {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (htr : trace A = 1) : ∑ i, hA.eigenvalues i = 1 := by
  have hs := congrArg Complex.re (hA.trace_eq_sum_eigenvalues.symm.trans htr)
  simpa using hs

/-- Uniform Jensen bounds the concave trace of a Hermitian trace-one matrix by the
value at the maximally mixed state, as used in Wolf Eq. (8.22). -/
theorem trace_concave_le_uniform [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htr : trace A = 1)
    {h : ℝ → ℝ} (hh : ConcaveOn ℝ Set.univ h) :
    (trace (hA.cfc h)).re ≤
      (Fintype.card n : ℝ) * h ((Fintype.card n : ℝ)⁻¹) := by
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∑ _ : n, (Fintype.card n : ℝ)⁻¹ = 1 := by simp [ne_of_gt hN]
  have hj := hh.le_map_sum (t := Finset.univ) (p := hA.eigenvalues)
    (fun _ _ ↦ (inv_pos.mpr hN).le) hw (fun _ _ ↦ Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum, hA.sum_eigenvalues_trace_one htr,
    mul_one] at hj
  rw [← RCLike.re_eq_complex_re, hA.trace_cfc_eq_sum_re]
  exact (inv_mul_le_iff₀ hN).mp hj

/-- Strict Jensen rigidity at the maximally mixed state, as used in Wolf Eq. (8.22).
A Hermitian trace-one matrix whose concave trace is at least the uniform value is
the maximally mixed matrix. -/
theorem eq_smul_one_of_trace_strictConcave_ge [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (htr : trace A = 1)
    {h : ℝ → ℝ} (hh : StrictConcaveOn ℝ Set.univ h)
    (hge : (Fintype.card n : ℝ) * h ((Fintype.card n : ℝ)⁻¹) ≤
      (trace (hA.cfc h)).re) :
    A = (Fintype.card n : ℝ)⁻¹ • (1 : Matrix n n ℂ) := by
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
  have hs := hA.sum_eigenvalues_trace_one htr
  have hw : ∑ _ : n, (Fintype.card n : ℝ)⁻¹ = 1 := by
    simp [ne_of_gt hN]
  have havg : ∑ i, (Fintype.card n : ℝ)⁻¹ • hA.eigenvalues i =
      (Fintype.card n : ℝ)⁻¹ := by
    simp [smul_eq_mul, ← Finset.mul_sum, hs]
  have hreverse : h (∑ i, (Fintype.card n : ℝ)⁻¹ • hA.eigenvalues i) ≤
      ∑ i, (Fintype.card n : ℝ)⁻¹ • h (hA.eigenvalues i) := by
    rw [havg]
    simp only [smul_eq_mul]
    rw [← Finset.mul_sum]
    rw [← RCLike.re_eq_complex_re, hA.trace_cfc_eq_sum_re] at hge
    exact (le_inv_mul_iff₀ hN).mpr hge
  have heq := hh.eq_of_map_sum_eq (t := Finset.univ)
    (fun _ _ ↦ inv_pos.mpr hN) hw (fun _ _ ↦ Set.mem_univ _) hreverse
  have heigen : ∀ i, hA.eigenvalues i = (Fintype.card n : ℝ)⁻¹ := by
    intro i
    have hc : ∑ j, hA.eigenvalues j = (Fintype.card n : ℝ) * hA.eigenvalues i := by
      simp [fun j ↦ heq (Finset.mem_univ j) (Finset.mem_univ i)]
    rw [hc] at hs
    apply (mul_left_cancel₀ (ne_of_gt hN))
    rw [hs, mul_inv_cancel₀ (ne_of_gt hN)]
  rw [hA.spectral_theorem]
  have hd : diagonal (RCLike.ofReal ∘ hA.eigenvalues) =
      (Fintype.card n : ℝ)⁻¹ • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Function.comp_def, heigen]
  rw [hd, Unitary.conjStarAlgAut_apply, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.prop]

end Matrix.IsHermitian

/-- **Entropy increasing maps**, Wolf Eq. (8.22), source lines 348–361.
For any globally strictly concave real function, a positive trace-preserving complex
linear matrix endomorphism is unital exactly when it increases its functional-calculus
trace on every density matrix. Singular inputs and the zero-dimensional case are included. -/
theorem IsPositiveMap.unital_iff_trace_strictConcave_increasing
    {T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (hT : IsPositiveMap T)
    (htr : IsTracePreservingMap T)
    {h : ℝ → ℝ} (hh : StrictConcaveOn ℝ Set.univ h) :
    T 1 = 1 ↔ ∀ (A : Matrix n n ℂ) (hA : A.PosSemidef), trace A = 1 →
      (trace (hA.isHermitian.cfc h)).re ≤
        (trace ((hT A hA).isHermitian.cfc h)).re := by
  constructor
  · intro hT1 A hA _
    exact hT.trace_concave_le hT1 htr hh.concaveOn hA
  · intro hincr
    cases isEmpty_or_nonempty n with
    | inl he => exact Subsingleton.elim _ _
    | inr hn =>
      have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
      let A : Matrix n n ℂ := (Fintype.card n : ℝ)⁻¹ • 1
      have hA : A.PosSemidef := PosSemidef.one.smul (le_of_lt (inv_pos.mpr hN))
      have hA1 : trace A = 1 := by
        simp [A, trace_smul, trace_one]
      have hscalar : hA.isHermitian.cfc h = h ((Fintype.card n : ℝ)⁻¹) •
          (1 : Matrix n n ℂ) := by
        rw [← hA.isHermitian.cfc_eq]
        change cfc h ((Fintype.card n : ℝ)⁻¹ • (1 : Matrix n n ℂ)) = _
        rw [← Algebra.algebraMap_eq_smul_one, cfc_algebraMap,
          Algebra.algebraMap_eq_smul_one]
      have hb := hincr A hA hA1
      rw [hscalar] at hb
      have hmax : T A = A := (hT A hA).isHermitian.eq_smul_one_of_trace_strictConcave_ge
        ((htr A).trans hA1) hh (by simpa [trace_smul, trace_one, mul_comm] using hb)
      have hscale := congrArg (fun X : Matrix n n ℂ ↦ (Fintype.card n : ℝ) • X) hmax
      simpa [A, LinearMap.map_smul_of_tower, smul_smul, ne_of_gt hN] using hscale
