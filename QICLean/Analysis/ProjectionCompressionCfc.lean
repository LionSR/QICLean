/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Lagrange

/-!
# Functional calculus on the range of a commuting projection

Let `P` be a matrix that commutes with a Hermitian matrix `Z`. If a second Hermitian matrix `Y`
agrees with `Z` after multiplication by `P`, then so do all their continuous functions:
`P f(Y) = P f(Z)`. For an orthogonal projection `P` commuting with `A`, the operator
`P A + (1 - P)` is `A` on the range of `P`, extended by the identity on the orthogonal
complement; it is positive definite when `A` is, its functional calculus is computed block by
block, and two such operators commute exactly when `P A B = P B A`.

These facts let an operator defined on an invariant subspace be represented on the whole space
without changing anything it does on that subspace.

## Main declarations

* `Matrix.mul_cfc_eq_mul_cfc_of_mul_eq` — `P Y = P Z` with `[P, Z] = 0` gives `P f(Y) = P f(Z)`.
* `Matrix.cfc_proj_mul_add` — `f(P Y + (1 - P) Z) = P f(Y) + (1 - P) f(Z)`.
* `Matrix.PosDef.proj_mul_add_one_sub` — `P A + (1 - P)` is positive definite.
* `Matrix.proj_mul_add_one_sub_mul` — the product of two such operators.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- If `P` commutes with `Z` and `P Y = P Z`, then `P Y^k = P Z^k` for every `k`. -/
theorem mul_pow_eq_mul_pow_of_mul_eq {P Y Z : Matrix m m ℂ} (hPZ : Commute P Z)
    (h : P * Y = P * Z) (k : ℕ) : P * Y ^ k = P * Z ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc P * Y ^ (k + 1) = P * Y ^ k * Y := by rw [pow_succ, Matrix.mul_assoc]
      _ = Z ^ k * (P * Y) := by rw [ih, (hPZ.pow_right k).eq, Matrix.mul_assoc]
      _ = P * Z ^ (k + 1) := by
        rw [h, ← Matrix.mul_assoc, ← (hPZ.pow_right k).eq, Matrix.mul_assoc, ← pow_succ]

/-- **Functional calculus on the range of a commuting matrix.** If `P` commutes with the
Hermitian matrix `Z` and `P Y = P Z` for a Hermitian `Y`, then `P f(Y) = P f(Z)` for every
real function `f`. Both functions agree with one interpolating polynomial on the two
spectra. -/
theorem mul_cfc_eq_mul_cfc_of_mul_eq {P Y Z : Matrix m m ℂ} (hY : Y.IsHermitian)
    (hZ : Z.IsHermitian) (hPZ : Commute P Z) (h : P * Y = P * Z) (f : ℝ → ℝ) :
    P * cfc f Y = P * cfc f Z := by
  classical
  have hfin : (spectrum ℝ Y ∪ spectrum ℝ Z).Finite :=
    Matrix.finite_real_spectrum.union Matrix.finite_real_spectrum
  set s := hfin.toFinset
  set q : Polynomial ℝ := Lagrange.interpolate s id f
  have hq : ∀ x ∈ spectrum ℝ Y ∪ spectrum ℝ Z, q.eval x = f x := fun x hx => by
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) f (Set.injOn_id _)
      (hfin.mem_toFinset.mpr hx)
    exact this
  have hcY : cfc f Y = Polynomial.aeval Y q := by
    rw [← cfc_polynomial q Y hY.isSelfAdjoint]
    exact cfc_congr fun x hx => (hq x (Or.inl hx)).symm
  have hcZ : cfc f Z = Polynomial.aeval Z q := by
    rw [← cfc_polynomial q Z hZ.isSelfAdjoint]
    exact cfc_congr fun x hx => (hq x (Or.inr hx)).symm
  rw [hcY, hcZ, Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm, mul_smul_comm, mul_pow_eq_mul_pow_of_mul_eq hPZ h]

/-- **Block functional calculus.** For an orthogonal projection `P` commuting with the
Hermitian matrices `Y` and `Z`, `f(P Y + (1 - P) Z) = P f(Y) + (1 - P) f(Z)`. -/
theorem cfc_proj_mul_add {P Y Z : Matrix m m ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (hY : Y.IsHermitian) (hZ : Z.IsHermitian) (hPY : Commute P Y) (hPZ : Commute P Z)
    (f : ℝ → ℝ) : cfc f (P * Y + (1 - P) * Z) = P * cfc f Y + (1 - P) * cfc f Z := by
  set W := P * Y + (1 - P) * Z
  have hQ : (1 - P).IsHermitian := isHermitian_one.sub hP
  have hPQ : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_zero]
  have hPYh : (P * Y).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, hP.eq, hY.eq, hPY.eq]
  have hQZ : Commute (1 - P) Z := (Commute.one_left Z).sub_left hPZ
  have hQZh : ((1 - P) * Z).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, hQ.eq, hZ.eq, hQZ.eq]
  have hW : W.IsHermitian := hPYh.add hQZh
  have hPW : P * W = P * Y := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, hPQ, Matrix.zero_mul,
      add_zero]
  have hQW : (1 - P) * W = (1 - P) * Z := by
    rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP, hQQ, Matrix.zero_mul,
      zero_add]
  have e1 := mul_cfc_eq_mul_cfc_of_mul_eq hW hY hPY hPW f
  have e2 := mul_cfc_eq_mul_cfc_of_mul_eq hW hZ hQZ hQW f
  calc cfc f W = P * cfc f W + (1 - P) * cfc f W := by
        rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
    _ = P * cfc f Y + (1 - P) * cfc f Z := by rw [e1, e2]

/-- The special case `Z = 1`: `f(P Y + (1 - P)) = P f(Y) + f(1) (1 - P)`. -/
theorem cfc_proj_mul_add_one_sub {P Y : Matrix m m ℂ} (hP : P.IsHermitian) (hPP : P * P = P)
    (hY : Y.IsHermitian) (hPY : Commute P Y) (f : ℝ → ℝ) :
    cfc f (P * Y + (1 - P)) = P * cfc f Y + (f 1 : ℂ) • (1 - P) := by
  have h := cfc_proj_mul_add hP hPP hY isHermitian_one hPY (Commute.one_right P) f
  rw [Matrix.mul_one, cfc_apply_one, Algebra.algebraMap_eq_smul_one,
    Matrix.mul_smul, Matrix.mul_one] at h
  rw [h, Complex.coe_smul]

/-- `P A + (1 - P)` commutes with everything that commutes with `P` and `A`. -/
theorem commute_proj_mul_add_one_sub {P A X : Matrix m m ℂ} (hPX : Commute P X)
    (hAX : Commute A X) : Commute (P * A + (1 - P)) X :=
  ((hPX.mul_left hAX).add_left ((Commute.one_left X).sub_left hPX))

/-- **Products of extended operators.** For an idempotent `P` commuting with `A`,
`(P A + (1 - P)) (P B + (1 - P)) = P (A B) + (1 - P)`. -/
theorem proj_mul_add_one_sub_mul {P A B : Matrix m m ℂ} (hPP : P * P = P)
    (hPA : Commute P A) :
    (P * A + (1 - P)) * (P * B + (1 - P)) = P * (A * B) + (1 - P) := by
  have hPQ : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hQP : (1 - P) * P = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_zero]
  have h1 : P * A * (P * B) = P * (A * B) := by
    calc P * A * (P * B) = P * (A * P) * B := by simp only [Matrix.mul_assoc]
      _ = P * (A * B) := by rw [← hPA.eq, ← Matrix.mul_assoc, hPP, Matrix.mul_assoc]
  have h2 : P * A * (1 - P) = 0 := by
    have hc : Commute A (1 - P) := (Commute.one_right A).sub_right hPA.symm
    rw [Matrix.mul_assoc, hc.eq, ← Matrix.mul_assoc, hPQ, Matrix.zero_mul]
  have h3 : (1 - P) * (P * B) = 0 := by rw [← Matrix.mul_assoc, hQP, Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2, h3, hQQ, add_zero, zero_add]

/-- Two extended operators commute exactly when `P A B = P B A`. -/
theorem commute_proj_mul_add_one_sub_iff {P A B : Matrix m m ℂ} (hPP : P * P = P)
    (hPA : Commute P A) (hPB : Commute P B) :
    Commute (P * A + (1 - P)) (P * B + (1 - P)) ↔ P * (A * B) = P * (B * A) := by
  rw [Commute, SemiconjBy, proj_mul_add_one_sub_mul hPP hPA, proj_mul_add_one_sub_mul hPP hPB]
  exact add_left_injective _ |>.eq_iff

/-- **Positivity of the extension.** For an orthogonal projection `P` commuting with a positive
definite `A`, the operator `P A + (1 - P)` is positive definite. -/
theorem PosDef.proj_mul_add_one_sub {P A : Matrix m m ℂ} (hA : A.PosDef) (hP : P.IsHermitian)
    (hPP : P * P = P) (hPA : Commute P A) : (P * A + (1 - P)).PosDef := by
  have hQ : (1 - P).IsHermitian := isHermitian_one.sub hP
  have hPAh : (P * A).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, hP.eq, hA.isHermitian.eq, hPA.eq]
  refine PosDef.of_dotProduct_mulVec_pos (hPAh.add hQ) fun x hx => ?_
  have hPQ : P * (1 - P) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hQQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPQ, sub_zero]
  have hPAP : P * A = P * A * P := by
    rw [Matrix.mul_assoc, ← hPA.eq, ← Matrix.mul_assoc, hPP]
  have e1 : star x ⬝ᵥ ((P * A) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (A *ᵥ (P *ᵥ x)) := by
    rw [hPAP, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec, hP.eq, Matrix.dotProduct_mulVec]
  have e2 : star x ⬝ᵥ ((1 - P) *ᵥ x) = star ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) := by
    rw [Matrix.star_mulVec, hQ.eq, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hQQ]
  rw [Matrix.add_mulVec, dotProduct_add, e1, e2]
  have hsplit : x = P *ᵥ x + (1 - P) *ᵥ x := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  by_cases hPx : P *ᵥ x = 0
  · have hQx : (1 - P) *ᵥ x ≠ 0 := fun h => hx (by rw [hsplit, hPx, h, add_zero])
    rw [hPx, Matrix.mulVec_zero, dotProduct_zero, zero_add]
    exact dotProduct_star_self_pos_iff.mpr hQx
  · exact add_pos_of_pos_of_nonneg (hA.dotProduct_mulVec_pos hPx)
      (dotProduct_star_self_nonneg _)

/-- **Real powers of the extension.** For an orthogonal projection `P` commuting with a positive
definite `A`, `(P A + (1 - P))^r = P A^r + (1 - P)`. -/
theorem PosDef.rpow_proj_mul_add_one_sub {P A : Matrix m m ℂ} (hA : A.PosDef)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPA : Commute P A) (r : ℝ) :
    (P * A + (1 - P)) ^ r = P * A ^ r + (1 - P) := by
  rw [CFC.rpow_eq_cfc_real (hA.proj_mul_add_one_sub hP hPP hPA).posSemidef.nonneg,
    CFC.rpow_eq_cfc_real hA.posSemidef.nonneg,
    cfc_proj_mul_add_one_sub hP hPP hA.isHermitian hPA, Real.one_rpow, Complex.ofReal_one,
    one_smul]

/-- **Whitening the extensions.** For an orthogonal projection `P` commuting with positive
definite `A` and `B`, the whitened extension
`(P A + (1 - P))^{-1/2} (P B + (1 - P)) (P A + (1 - P))^{-1/2}` is the extension of
`A^{-1/2} B A^{-1/2}`. -/
theorem PosDef.whiten_proj_mul_add_one_sub {P A B : Matrix m m ℂ} (hA : A.PosDef)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPA : Commute P A) (hPB : Commute P B) :
    (P * A + (1 - P)) ^ (-(1 / 2) : ℝ) * (P * B + (1 - P)) *
        (P * A + (1 - P)) ^ (-(1 / 2) : ℝ) =
      P * (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) + (1 - P) := by
  have hPr : Commute P (A ^ (-(1 / 2) : ℝ)) := by
    rw [CFC.rpow_def]
    exact (Commute.cfc_nnreal hPA.symm _).symm
  rw [hA.rpow_proj_mul_add_one_sub hP hPP hPA, proj_mul_add_one_sub_mul hPP hPr,
    proj_mul_add_one_sub_mul hPP (hPr.mul_right hPB)]

/-- **Transfer of a lower bound to the extension.** If `Q = P Q P` and
`Q ≤ A^{-1/2} B A^{-1/2}` for a positive definite `A` and a matrix `B`, both commuting with
the orthogonal projection `P`, then `Q` is also below the whitened extension. -/
theorem PosDef.le_whiten_proj_mul_add_one_sub {P A B Q : Matrix m m ℂ} (hA : A.PosDef)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPA : Commute P A) (hPB : Commute P B)
    (hQ : P * Q * P = Q) (hle : Q ≤ A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) :
    Q ≤ (P * A + (1 - P)) ^ (-(1 / 2) : ℝ) * (P * B + (1 - P)) *
      (P * A + (1 - P)) ^ (-(1 / 2) : ℝ) := by
  rw [hA.whiten_proj_mul_add_one_sub hP hPP hPA hPB]
  set R := A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)
  have hPr : Commute P (A ^ (-(1 / 2) : ℝ)) := by
    rw [CFC.rpow_def]
    exact (Commute.cfc_nnreal hPA.symm _).symm
  have hPR : Commute P R := (hPr.mul_right hPB).mul_right hPr
  have h1 : P * R * P = P * R := by rw [Matrix.mul_assoc, ← hPR.eq, ← Matrix.mul_assoc, hPP]
  have hQle : Q ≤ P * R := by
    rw [Matrix.le_iff] at hle ⊢
    have := hle.conjTranspose_mul_mul_same P
    rwa [hP.eq, Matrix.mul_sub, Matrix.sub_mul, hQ, h1] at this
  have hQP : (1 - P).PosSemidef := by
    have hQ' : (1 - P).IsHermitian := isHermitian_one.sub hP
    have e : 1 - P = (1 - P)ᴴ * (1 - P) := by
      rw [hQ'.eq, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self,
        sub_zero]
    rw [e]; exact posSemidef_conjTranspose_mul_self _
  exact hQle.trans (le_add_of_nonneg_right (Matrix.nonneg_iff_posSemidef.mpr hQP))

end Matrix
