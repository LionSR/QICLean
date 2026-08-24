/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Matrix.Circulant
import QICLean.Analysis.CyclicReciprocal
import QICLean.Analysis.FiniteCoordinateNowosad.Yamagami

/-!
# Yamagami's forward cyclic matrix

This file constructs the stride-one cyclic matrix used on pp. 522--524 of
S. Yamagami, *Cyclic inequalities*, Proc. Amer. Math. Soc. 118 (1993),
521--527.  Its Fourier symbol is the one already defined in
`QICLean.Analysis.CyclicReciprocal`.  The corrected strict-disk estimate in
that file yields invertibility and the positive-semidefinite Hessian package
required by Yamagami's Lemma 3.

The only finite Fourier facts developed locally are the translation formula
for the discrete Fourier transform and its finite Parseval identity.  Mathlib
provides DFT inversion on `ZMod`, but currently provides neither of these two
forms directly.
-/

open scoped BigOperators Matrix ZMod
open AddChar Nowosad

namespace Yamagami

variable (N m : ℕ) [NeZero N]

/-- The matrix whose action is Yamagami's forward cyclic denominator:
`(Sx) i = (s - m) x i + ∑_{k=1}^m x (i+k)`.

The displayed entry formula is invariant under simultaneous cyclic
translation of its row and column indices, so this is a circulant matrix. -/
noncomputable def forwardMatrix (s : ℝ) : Matrix (ZMod N) (ZMod N) ℝ :=
  fun i j ↦
    (s - (m : ℝ)) * (if j = i then 1 else 0)
      + ∑ k : Fin m,
          if j = i + ((k.1 + 1 : ℕ) : ZMod N) then 1 else 0

omit [NeZero N] in
@[simp]
theorem forwardMatrix_apply (s : ℝ) (i j : ZMod N) :
    forwardMatrix N m s i j =
      (s - (m : ℝ)) * (if j = i then 1 else 0)
        + ∑ k : Fin m,
            if j = i + ((k.1 + 1 : ℕ) : ZMod N) then 1 else 0 :=
  rfl

/-- Matrix multiplication by the forward cyclic matrix is exactly the
previously defined forward denominator. -/
theorem forwardMatrix_mulVec (s : ℝ) (x : ZMod N → ℝ) :
    forwardMatrix N m s *ᵥ x = forwardDenominator N m s x := by
  classical
  funext i
  unfold forwardMatrix forwardDenominator Matrix.mulVec dotProduct
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  have hdiagonal :
      (∑ j : ZMod N,
        ((s - (m : ℝ)) * (if j = i then 1 else 0)) * x j) =
        (s - (m : ℝ)) * x i := by
    simp
  rw [hdiagonal]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

omit [NeZero N] in
/-- Simultaneous cyclic translation leaves every matrix entry unchanged. -/
theorem forwardMatrix_add_add (s : ℝ) (a i j : ZMod N) :
    forwardMatrix N m s (i + a) (j + a) = forwardMatrix N m s i j := by
  classical
  have hdiag : j + a = i + a ↔ j = i := by
    constructor
    · exact add_right_cancel
    · exact congrArg (fun z ↦ z + a)
  have hshift (q : ZMod N) : j + a = i + a + q ↔ j = i + q := by
    rw [show i + a + q = (i + q) + a by abel]
    constructor
    · exact add_right_cancel
    · exact congrArg (fun z ↦ z + a)
  simp only [forwardMatrix_apply, hdiag, hshift]

omit [NeZero N] in
/-- The entry formula is a `Matrix.circulant` in Mathlib's convention. -/
theorem forwardMatrix_eq_circulant (s : ℝ) :
    forwardMatrix N m s =
      Matrix.circulant (fun q : ZMod N ↦ forwardMatrix N m s q 0) := by
  ext i j
  simp only [Matrix.circulant_apply]
  simpa using forwardMatrix_add_add N m s j (i - j) 0

omit [NeZero N] in
/-- The matrix entries are nonnegative as soon as the diagonal coefficient
`s - m` is nonnegative. -/
theorem forwardMatrix_nonnegative (s : ℝ) (hms : (m : ℝ) ≤ s) :
    ∀ i j, 0 ≤ forwardMatrix N m s i j := by
  classical
  intro i j
  rw [forwardMatrix_apply]
  apply add_nonneg
  · exact mul_nonneg (sub_nonneg.mpr hms) (by split_ifs <;> norm_num)
  · apply Finset.sum_nonneg
    intro k _
    split_ifs <;> norm_num

omit [NeZero N] in
/-- The source range implies entrywise nonnegativity.  Only its upper bound
on `m` and lower bound on `s` are needed for this conclusion. -/
theorem forwardMatrix_nonnegative_of_sourceRange
    (hm₂ : m ≤ N - 2) (s : ℝ) (hs : (N : ℝ) ≤ s) :
    ∀ i j, 0 ≤ forwardMatrix N m s i j := by
  apply forwardMatrix_nonnegative N m s
  exact le_trans (by exact_mod_cast (by omega : m ≤ N)) hs

/-- Every row of the forward cyclic matrix has sum `s`. -/
theorem forwardMatrix_mulVec_one (s : ℝ) :
    forwardMatrix N m s *ᵥ (1 : ZMod N → ℝ) =
      s • (1 : ZMod N → ℝ) := by
  rw [forwardMatrix_mulVec]
  funext i
  have hone : (1 : ZMod N → ℝ) = fun _ ↦ 1 := rfl
  rw [hone, forwardDenominator_one]
  simp

private theorem sum_ite_eq_add_right (q i : ZMod N) :
    ∑ j : ZMod N, (if i = j + q then (1 : ℝ) else 0) = 1 := by
  calc
    (∑ j : ZMod N, (if i = j + q then (1 : ℝ) else 0)) =
        ∑ j : ZMod N, (if i = j then (1 : ℝ) else 0) := by
      refine Fintype.sum_equiv (Equiv.addRight q) _ _ fun j ↦ ?_
      by_cases h : i = j + q <;> simp [h]
    _ = 1 := by simp

/-- Every column of the forward cyclic matrix has sum `s`. -/
theorem forwardMatrix_transpose_mulVec_one (s : ℝ) :
    (forwardMatrix N m s).transpose *ᵥ (1 : ZMod N → ℝ) =
      s • (1 : ZMod N → ℝ) := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Pi.one_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  simp_rw [forwardMatrix_apply]
  rw [Finset.sum_add_distrib]
  rw [show (∑ j : ZMod N,
      (s - (m : ℝ)) * (if i = j then 1 else 0)) =
      s - (m : ℝ) by simp]
  rw [Finset.sum_comm]
  have hshift (k : Fin m) :
      ∑ j : ZMod N,
        (if i = j + ((k.1 + 1 : ℕ) : ZMod N) then (1 : ℝ) else 0) = 1 :=
    sum_ite_eq_add_right N ((k.1 + 1 : ℕ) : ZMod N) i
  simp_rw [hshift]
  simp

/-- The real eigenvalue of Yamagami's Hessian on the character indexed by
`j`. -/
noncomputable def hessianSymbol (s : ℝ) (j : ZMod N) : ℝ :=
  2 * (s * (symbol N m s j).re - Complex.normSq (symbol N m s j))

@[simp]
theorem symbol_zero (s : ℝ) : symbol N m s 0 = (s : ℂ) := by
  simp [symbol]

@[simp]
theorem hessianSymbol_zero (s : ℝ) : hessianSymbol N m s 0 = 0 := by
  simp [hessianSymbol]

/-- The corrected strict-disk estimate is precisely strict positivity of
the Hessian symbol away from the constant character. -/
theorem hessianSymbol_pos
    (hN : 3 ≤ N) (hm₁ : 1 ≤ m) (hm₂ : m ≤ N - 2)
    (s : ℝ) (hs : (N : ℝ) ≤ s) {j : ZMod N} (hj : j ≠ 0) :
    0 < hessianSymbol N m s j := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hspos : 0 < s := lt_of_lt_of_le hNpos hs
  have hdisk := norm_symbol_sub_half_lt_half N m hN hm₁ hm₂ s hs hj
  have hsquare :
      ‖symbol N m s j - ((s / 2 : ℝ) : ℂ)‖ ^ 2 < (s / 2) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (by positivity)).mpr hdisk
  have hweight :
      Complex.normSq (symbol N m s j) < s * (symbol N m s j).re := by
    rw [Complex.sq_norm, Complex.normSq_apply] at hsquare
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero] at hsquare
    rw [Complex.normSq_apply]
    nlinarith
  unfold hessianSymbol
  linarith

/-- Every Fourier Hessian multiplier is nonnegative in the exact corrected
Wolf range. -/
theorem hessianSymbol_nonneg
    (hN : 3 ≤ N) (hm₁ : 1 ≤ m) (hm₂ : m ≤ N - 2)
    (s : ℝ) (hs : (N : ℝ) ≤ s) (j : ZMod N) :
    0 ≤ hessianSymbol N m s j := by
  by_cases hj : j = 0
  · subst j
    simp
  · exact (hessianSymbol_pos N m hN hm₁ hm₂ s hs hj).le

/-- No cyclic-matrix Fourier multiplier vanishes in the corrected Wolf
range. -/
theorem symbol_ne_zero
    (hN : 3 ≤ N) (hm₁ : 1 ≤ m) (hm₂ : m ≤ N - 2)
    (s : ℝ) (hs : (N : ℝ) ≤ s) (j : ZMod N) :
    symbol N m s j ≠ 0 := by
  by_cases hj : j = 0
  · subst j
    rw [symbol_zero]
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le
      (by exact_mod_cast (by omega : 0 < N)) hs))
  · intro hzero
    have hpos := hessianSymbol_pos N m hN hm₁ hm₂ s hs hj
    simp [hessianSymbol, hzero] at hpos

private theorem map_forwardMatrix_mulVec (s : ℝ) (x : ZMod N → ℂ) :
    (forwardMatrix N m s).map Complex.ofRealHom *ᵥ x =
      fun i ↦
        ((s - (m : ℝ) : ℝ) : ℂ) * x i +
          ∑ k : Fin m, x (i + ((k.1 + 1 : ℕ) : ZMod N)) := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, forwardMatrix_apply,
    map_add, map_mul, map_sub, map_natCast, map_sum, apply_ite, map_one, map_zero]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp

/-- The DFT diagonalizes a cyclic translation. -/
private theorem dft_comp_add_right (x : ZMod N → ℂ) (q j : ZMod N) :
    ZMod.dft (fun i ↦ x (i + q)) j =
      ZMod.stdAddChar (j * q) * ZMod.dft x j := by
  simp only [ZMod.dft_apply, smul_eq_mul]
  calc
    (∑ i : ZMod N,
        ZMod.stdAddChar (-(i * j)) * x (i + q)) =
        ∑ i : ZMod N,
          ZMod.stdAddChar (-((i - q) * j)) * x i := by
      refine Fintype.sum_equiv (Equiv.addRight q) _ _ fun i ↦ ?_
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
    _ = ∑ i : ZMod N,
        ZMod.stdAddChar (j * q) *
          (ZMod.stdAddChar (-(i * j)) * x i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show -((i - q) * j) = j * q + -(i * j) by ring,
        map_add_eq_mul]
      ring
    _ = ZMod.stdAddChar (j * q) *
        ∑ i : ZMod N, ZMod.stdAddChar (-(i * j)) * x i := by
      rw [Finset.mul_sum]

private theorem star_stdAddChar (t : ZMod N) :
    star (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  change (starRingEnd ℂ) (ZMod.stdAddChar t) = ZMod.stdAddChar (-t)
  rw [← inv_apply_eq_conj, map_neg_eq_inv]

private theorem dft_adjoint (x y : ZMod N → ℂ) :
    star (ZMod.dft x) ⬝ᵥ y =
      star x ⬝ᵥ (fun i ↦ ZMod.dft y (-i)) := by
  rw [dotProduct, dotProduct]
  simp_rw [Pi.star_apply, ZMod.dft_apply, star_sum, smul_eq_mul,
    StarMul.star_mul, star_stdAddChar, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  congr 1 with i
  congr 1 with j
  simp only [neg_neg, mul_neg, neg_neg]
  rw [mul_comm i j]
  ring

/-- Parseval's identity for the unnormalized finite Fourier transform. -/
private theorem dft_parseval (x y : ZMod N → ℂ) :
    star (ZMod.dft x) ⬝ᵥ ZMod.dft y =
      (N : ℂ) * (star x ⬝ᵥ y) := by
  rw [dft_adjoint, ZMod.dft_dft]
  simp only [neg_neg, smul_eq_mul]
  rw [dotProduct, dotProduct, Finset.mul_sum]
  congr 1 with i
  ring

private theorem invDFT_eq_zero_mode
    (x : ZMod N → ℂ) (hx : ∀ j : ZMod N, j ≠ 0 → ZMod.dft x j = 0)
    (i : ZMod N) :
    x i = (N : ℂ)⁻¹ * ZMod.dft x 0 := by
  have hsum :
      (∑ j : ZMod N, ZMod.stdAddChar (j * i) • ZMod.dft x j) =
        ZMod.dft x 0 := by
    classical
    rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      rw [hx j hj]
      simp
    · simp
  calc
    x i = ZMod.dft.symm (ZMod.dft x) i := by
      exact (congrFun (ZMod.dft.symm_apply_apply x) i).symm
    _ = (N : ℂ)⁻¹ •
        ∑ j : ZMod N, ZMod.stdAddChar (j * i) • ZMod.dft x j :=
      ZMod.invDFT_apply (ZMod.dft x) i
    _ = (N : ℂ)⁻¹ * ZMod.dft x 0 := by rw [hsum]; rfl

private theorem eq_const_of_dft_eq_zero_of_ne
    (x : ZMod N → ℂ) (hx : ∀ j : ZMod N, j ≠ 0 → ZMod.dft x j = 0) :
    x = fun _ ↦ x 0 := by
  funext i
  rw [invDFT_eq_zero_mode N x hx i, invDFT_eq_zero_mode N x hx 0]

/-- The DFT diagonalizes the forward cyclic matrix, with eigenvalue exactly
`Yamagami.symbol`.  This is the stride-one form of Yamagami's Lemma 4. -/
theorem dft_map_forwardMatrix_mulVec (s : ℝ) (x : ZMod N → ℂ)
    (j : ZMod N) :
    ZMod.dft ((forwardMatrix N m s).map Complex.ofRealHom *ᵥ x) j =
      symbol N m s j * ZMod.dft x j := by
  rw [map_forwardMatrix_mulVec]
  have haction :
      (fun i ↦
        ((s - (m : ℝ) : ℝ) : ℂ) * x i +
          ∑ k : Fin m, x (i + ((k.1 + 1 : ℕ) : ZMod N))) =
        ((s - (m : ℝ) : ℝ) : ℂ) • x +
          ∑ k : Fin m,
            (fun i ↦ x (i + ((k.1 + 1 : ℕ) : ZMod N))) := by
    funext i
    simp [smul_eq_mul]
  rw [haction, map_add, map_smul, map_sum]
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp_rw [dft_comp_add_right]
  unfold symbol
  rw [← Finset.sum_mul]
  ring

/-- Reversing the character index conjugates the real cyclic symbol. -/
theorem symbol_neg (s : ℝ) (j : ZMod N) :
    symbol N m s (-j) = star (symbol N m s j) := by
  simp only [symbol, neg_mul]
  rw [star_add, star_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro k _
    rw [map_neg_eq_inv, inv_apply_eq_conj]
    rfl

private theorem sum_ite_mul_eq_sub_right
    (x : ZMod N → ℂ) (q i : ZMod N) :
    ∑ j : ZMod N, (if i = j + q then (1 : ℂ) else 0) * x j =
      x (i - q) := by
  calc
    (∑ j : ZMod N, (if i = j + q then (1 : ℂ) else 0) * x j) =
        ∑ j : ZMod N, (if i = j then (1 : ℂ) else 0) * x (j - q) := by
      refine Fintype.sum_equiv (Equiv.addRight q) _ _ fun j ↦ ?_
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      by_cases h : i = j + q <;> simp [h]
    _ = x (i - q) := by simp

private theorem map_transpose_forwardMatrix_mulVec
    (s : ℝ) (x : ZMod N → ℂ) :
    (forwardMatrix N m s).transpose.map Complex.ofRealHom *ᵥ x =
      fun i ↦
        ((s - (m : ℝ) : ℝ) : ℂ) * x i +
          ∑ k : Fin m, x (i - ((k.1 + 1 : ℕ) : ZMod N)) := by
  classical
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
    Matrix.transpose_apply, forwardMatrix_apply, map_add, map_mul, map_sub,
    map_natCast, map_sum, apply_ite, map_one, map_zero]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp
  · simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    exact sum_ite_mul_eq_sub_right N x
      ((k.1 + 1 : ℕ) : ZMod N) i

/-- The transpose cyclic matrix has the conjugate Fourier multiplier. -/
theorem dft_map_transpose_forwardMatrix_mulVec
    (s : ℝ) (x : ZMod N → ℂ) (j : ZMod N) :
    ZMod.dft
        ((forwardMatrix N m s).transpose.map Complex.ofRealHom *ᵥ x) j =
      symbol N m s (-j) * ZMod.dft x j := by
  rw [map_transpose_forwardMatrix_mulVec]
  have haction :
      (fun i ↦
        ((s - (m : ℝ) : ℝ) : ℂ) * x i +
          ∑ k : Fin m, x (i - ((k.1 + 1 : ℕ) : ZMod N))) =
        ((s - (m : ℝ) : ℝ) : ℂ) • x +
          ∑ k : Fin m,
            (fun i ↦ x (i + (-((k.1 + 1 : ℕ) : ZMod N)))) := by
    funext i
    simp [smul_eq_mul, sub_eq_add_neg]
  rw [haction, map_add, map_smul, map_sum]
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  simp_rw [dft_comp_add_right]
  unfold symbol
  rw [← Finset.sum_mul]
  simp only [mul_neg, neg_mul]
  ring

private theorem hessianSymbol_coe (s : ℝ) (j : ZMod N) :
    (hessianSymbol N m s j : ℂ) =
      (s : ℂ) * (symbol N m s j + star (symbol N m s j)) -
        2 * (star (symbol N m s j) * symbol N m s j) := by
  rw [Complex.star_def, Complex.add_conj,
    ← Complex.normSq_eq_conj_mul_self]
  unfold hessianSymbol
  push_cast
  ring

private theorem map_hessianMatrix (S : Matrix (ZMod N) (ZMod N) ℝ)
    (s : ℝ) :
    (hessianMatrix S s).map Complex.ofRealHom =
      (s : ℂ) • (S.map Complex.ofRealHom + S.transpose.map Complex.ofRealHom) -
        (2 : ℕ) •
          (S.transpose.map Complex.ofRealHom * S.map Complex.ofRealHom) := by
  classical
  ext i j
  unfold hessianMatrix
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.transpose_apply]
  simp only [two_nsmul]
  simp only [map_sub, map_add, smul_eq_mul, Matrix.mul_apply, map_mul,
    map_sum, Matrix.map_apply, Matrix.transpose_apply]
  have hof (r : ℝ) : Complex.ofRealHom r = (r : ℂ) := rfl
  simp only [hof]

/-- The DFT diagonalizes Yamagami's Hessian.  Its multiplier is
`q_j = 2 (s Re(λ_j) - |λ_j|²)`. -/
theorem dft_map_hessianMatrix_mulVec (s : ℝ) (x : ZMod N → ℂ)
    (j : ZMod N) :
    ZMod.dft
        ((hessianMatrix (forwardMatrix N m s) s).map Complex.ofRealHom *ᵥ x) j =
      (hessianSymbol N m s j : ℂ) * ZMod.dft x j := by
  rw [map_hessianMatrix]
  rw [two_nsmul]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  rw [map_sub, map_smul, map_add, map_add]
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [dft_map_forwardMatrix_mulVec, dft_map_transpose_forwardMatrix_mulVec,
    dft_map_transpose_forwardMatrix_mulVec,
    dft_map_forwardMatrix_mulVec, symbol_neg]
  rw [hessianSymbol_coe]
  ring

private theorem ofReal_dotProduct_hessianMatrix_mulVec
    (s : ℝ) (x : ZMod N → ℝ) :
    Complex.ofRealHom
        (x ⬝ᵥ hessianMatrix (forwardMatrix N m s) s *ᵥ x) =
      star (Complex.ofRealHom ∘ x) ⬝ᵥ
        ((hessianMatrix (forwardMatrix N m s) s).map Complex.ofRealHom *ᵥ
          (Complex.ofRealHom ∘ x)) := by
  rw [RingHom.map_dotProduct]
  apply congrArg₂ dotProduct
  · funext i
    simp
  · funext i
    simpa only [Function.comp_apply] using
      RingHom.map_mulVec Complex.ofRealHom
        (hessianMatrix (forwardMatrix N m s) s) x i

private theorem dft_hessian_quadratic_identity
    (s : ℝ) (x : ZMod N → ℝ) :
    (N : ℂ) * Complex.ofRealHom
        (x ⬝ᵥ hessianMatrix (forwardMatrix N m s) s *ᵥ x) =
      ∑ j : ZMod N,
        (hessianSymbol N m s j : ℂ) *
          Complex.normSq (ZMod.dft (Complex.ofRealHom ∘ x) j) := by
  calc
    (N : ℂ) * Complex.ofRealHom
        (x ⬝ᵥ hessianMatrix (forwardMatrix N m s) s *ᵥ x) =
        (N : ℂ) *
          (star (Complex.ofRealHom ∘ x) ⬝ᵥ
            ((hessianMatrix (forwardMatrix N m s) s).map
                Complex.ofRealHom *ᵥ (Complex.ofRealHom ∘ x))) := by
      rw [ofReal_dotProduct_hessianMatrix_mulVec]
    _ = star (ZMod.dft (Complex.ofRealHom ∘ x)) ⬝ᵥ
        ZMod.dft
          ((hessianMatrix (forwardMatrix N m s) s).map
              Complex.ofRealHom *ᵥ (Complex.ofRealHom ∘ x)) := by
      exact (dft_parseval N (Complex.ofRealHom ∘ x)
        ((hessianMatrix (forwardMatrix N m s) s).map
          Complex.ofRealHom *ᵥ (Complex.ofRealHom ∘ x))).symm
    _ = ∑ j : ZMod N,
        (hessianSymbol N m s j : ℂ) *
          Complex.normSq (ZMod.dft (Complex.ofRealHom ∘ x) j) := by
      rw [dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.star_apply]
      rw [dft_map_hessianMatrix_mulVec]
      rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
      ring

private theorem hessian_quadratic_identity
    (s : ℝ) (x : ZMod N → ℝ) :
    (N : ℝ) *
        (x ⬝ᵥ hessianMatrix (forwardMatrix N m s) s *ᵥ x) =
      ∑ j : ZMod N,
        hessianSymbol N m s j *
          Complex.normSq (ZMod.dft (Complex.ofRealHom ∘ x) j) := by
  apply Complex.ofReal_injective
  push_cast
  exact dft_hessian_quadratic_identity N m s x

private theorem hessianMatrix_isHermitian
    (S : Matrix (ZMod N) (ZMod N) ℝ) (s : ℝ) :
    (hessianMatrix S s).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  unfold hessianMatrix
  exact ((Matrix.isSymm_add_transpose_self S).smul s).sub
    ((Matrix.isSymm_transpose_mul_self S).smul (2 : ℕ))

/-- Yamagami's negative-Hessian representative is positive semidefinite in
the exact corrected Wolf range. -/
theorem hessianMatrix_forwardMatrix_posSemidef
    (hN : 3 ≤ N) (hm₁ : 1 ≤ m) (hm₂ : m ≤ N - 2)
    (s : ℝ) (hs : (N : ℝ) ≤ s) :
    (hessianMatrix (forwardMatrix N m s) s).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hessianMatrix_isHermitian N (forwardMatrix N m s) s) ?_
  intro x
  have hsum :
      0 ≤ ∑ j : ZMod N,
        hessianSymbol N m s j *
          Complex.normSq (ZMod.dft (Complex.ofRealHom ∘ x) j) := by
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg
      (hessianSymbol_nonneg N m hN hm₁ hm₂ s hs j)
      (Complex.normSq_nonneg _)
  have hproduct :
      0 ≤ (N : ℝ) *
        (x ⬝ᵥ hessianMatrix (forwardMatrix N m s) s *ᵥ x) := by
    rw [hessian_quadratic_identity N m s x]
    exact hsum
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (by omega : 0 < N)
  have hquadratic :
      0 ≤ x ⬝ᵥ hessianMatrix (forwardMatrix N m s) s *ᵥ x := by
    nlinarith
  simpa using hquadratic

/-- In the corrected Wolf range, the kernel of Yamagami's Hessian is
exactly the line spanned by the constant vector. -/
theorem hessianMatrix_forwardMatrix_mulVec_eq_zero_iff_isScalarVector
    (hN : 3 ≤ N) (hm₁ : 1 ≤ m) (hm₂ : m ≤ N - 2)
    (s : ℝ) (hs : (N : ℝ) ≤ s) (x : ZMod N → ℝ) :
    hessianMatrix (forwardMatrix N m s) s *ᵥ x = 0 ↔
      IsScalarVector x := by
  constructor
  · intro hx
    let xℂ : ZMod N → ℂ := Complex.ofRealHom ∘ x
    have hxℂ :
        (hessianMatrix (forwardMatrix N m s) s).map Complex.ofRealHom *ᵥ
            xℂ = 0 := by
      funext i
      dsimp [xℂ]
      calc
        ((hessianMatrix (forwardMatrix N m s) s).map Complex.ofRealHom *ᵥ
            (Complex.ofRealHom ∘ x)) i =
            Complex.ofRealHom
              ((hessianMatrix (forwardMatrix N m s) s *ᵥ x) i) := by
          simpa only [Function.comp_apply] using
            (RingHom.map_mulVec Complex.ofRealHom
              (hessianMatrix (forwardMatrix N m s) s) x i).symm
        _ = 0 := by rw [hx]; rfl
    have hfreq : ∀ j : ZMod N, j ≠ 0 → ZMod.dft xℂ j = 0 := by
      intro j hj
      have hd := dft_map_hessianMatrix_mulVec N m s xℂ j
      rw [hxℂ, map_zero, Pi.zero_apply] at hd
      apply (mul_eq_zero.mp hd.symm).resolve_left
      exact_mod_cast
        (ne_of_gt (hessianSymbol_pos N m hN hm₁ hm₂ s hs hj))
    have hconst := eq_const_of_dft_eq_zero_of_ne N xℂ hfreq
    refine ⟨x 0, ?_⟩
    funext i
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    apply Complex.ofReal_injective
    have hi := congrFun hconst i
    simpa [xℂ] using hi
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul,
      hessianMatrix_mulVec_one_eq_zero (forwardMatrix N m s) s
        (forwardMatrix_mulVec_one N m s)
        (forwardMatrix_transpose_mulVec_one N m s)]
    exact smul_zero c

/-- Yamagami's cyclic matrix is invertible throughout the exact corrected
Wolf range `N ≥ 3`, `1 ≤ m ≤ N - 2`, and `N ≤ s`. -/
theorem forwardMatrix_isUnit_det
    (hN : 3 ≤ N) (hm₁ : 1 ≤ m) (hm₂ : m ≤ N - 2)
    (s : ℝ) (hs : (N : ℝ) ≤ s) :
    IsUnit (forwardMatrix N m s).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  apply sub_eq_zero.mp
  let z : ZMod N → ℝ := x - y
  have hz : forwardMatrix N m s *ᵥ z = 0 := by
    dsimp [z]
    rw [Matrix.mulVec_sub, hxy, sub_self]
  let zℂ : ZMod N → ℂ := Complex.ofRealHom ∘ z
  have hzℂ :
      (forwardMatrix N m s).map Complex.ofRealHom *ᵥ zℂ = 0 := by
    funext i
    dsimp [zℂ]
    calc
      ((forwardMatrix N m s).map Complex.ofRealHom *ᵥ
          (Complex.ofRealHom ∘ z)) i =
          Complex.ofRealHom ((forwardMatrix N m s *ᵥ z) i) := by
        simpa only [Function.comp_apply] using
          (RingHom.map_mulVec Complex.ofRealHom (forwardMatrix N m s) z i).symm
      _ = 0 := by rw [hz]; rfl
  have hfreq : ∀ j : ZMod N, ZMod.dft zℂ j = 0 := by
    intro j
    have hdiag := dft_map_forwardMatrix_mulVec N m s zℂ j
    rw [hzℂ, map_zero, Pi.zero_apply] at hdiag
    exact (mul_eq_zero.mp hdiag.symm).resolve_left
      (symbol_ne_zero N m hN hm₁ hm₂ s hs j)
  have hzℂ_zero : zℂ = 0 := by
    apply (ZMod.dft (N := N) (E := ℂ)).injective
    funext j
    simpa using hfreq j
  have hz_zero : z = 0 := by
    funext i
    have hi := congrFun hzℂ_zero i
    change (z i : ℂ) = 0 at hi
    exact Complex.ofReal_injective (by simpa using hi)
  exact hz_zero

/-- Yamagami's reciprocal functional is the composed Nowosad functional
`L_{S⁻¹}(Sx)` for the forward cyclic matrix `S`.  The identity is valid
with Lean's total division and therefore needs no positivity hypothesis on
`x`. -/
theorem functional_eq_lambdaT_inverseOperator_mulVec
    (s : ℝ) (hS : IsUnit (forwardMatrix N m s).det) (x : ZMod N → ℝ) :
    functional N m s x =
      lambdaT (inverseOperator (forwardMatrix N m s))
        (forwardMatrix N m s *ᵥ x) := by
  unfold functional lambdaT
  rw [inverseOperator_apply, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hS, Matrix.one_mulVec]
  rw [← forwardMatrix_mulVec N m s x]
  unfold coordinateSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.inv_apply, Pi.mul_apply, div_eq_mul_inv]
  ring



end Yamagami
