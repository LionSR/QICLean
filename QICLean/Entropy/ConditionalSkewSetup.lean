/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcComplex
import QICLean.Channel.PartialTrace
import QICLean.Entropy.MarginalPhaseSetup

/-!
# The scalar function of the conditional skew estimate

Let `θ` be a vector on `P = P₀ P₁` and `W = (x U) F`, with marginals `ρ_P`, `ρ_W` and
`ρ_Y` (`Y = x U`), and let `h` be an operator on `P₀ x`.  The function of the conditional
skew estimate is
$$f(z)=\langle\theta,\rho_P^{[z]}\rho_Y^{[-z]}h\rho_P^{[-z]}\rho_Y^{[z]}\theta\rangle,$$
with powers vanishing on the kernels and every operator tensored with the identity on
the remaining factors.  This file sets up the lifts, the powers, the function, and the
facts that the support projections fix `θ`.

## Main definitions

* `Entropy.ConditionalSkew.margP`, `margW`, `margY`.
* `Entropy.ConditionalSkew.liftP`, `liftY`, `liftH`.
* `Entropy.ConditionalSkew.skewFun`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Lemma 5.3 (`lem:skew`),
  `04-conditional.tex`, lines 487–507.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁]
  [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F]

/-- The power function `t ↦ t^z` vanishing at zero. -/
def suppPowFun (z : ℂ) (t : ℝ) : ℂ := if t = 0 then 0 else ((t : ℝ) : ℂ) ^ z

/-- The marginal `ρ_P` on `P = P₀ P₁`. -/
def margP (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix (P₀ × P₁) (P₀ × P₁) ℂ :=
  partialTraceRight (vecMulVec θ (star θ))

/-- The marginal `ρ_W` on `W = (x U) F`. -/
def margW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix ((X × U) × F) ((X × U) × F) ℂ :=
  partialTraceLeft (vecMulVec θ (star θ))

/-- The marginal `ρ_Y` on `Y = x U`. -/
def margY (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix (X × U) (X × U) ℂ :=
  partialTraceRight (margW θ)

theorem posSemidef_margP (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : (margP θ).PosSemidef :=
  (posSemidef_vecMulVec_self_star θ).partialTraceRight

theorem posSemidef_margW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : (margW θ).PosSemidef :=
  (posSemidef_vecMulVec_self_star θ).partialTraceLeft

theorem posSemidef_margY (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : (margY θ).PosSemidef :=
  (posSemidef_margW θ).partialTraceRight

/-- An operator on `P`, tensored with the identity on `W`. -/
def liftP (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  A ⊗ₖ (1 : Matrix ((X × U) × F) ((X × U) × F) ℂ)

/-- An operator on `Y = x U`, tensored with the identity on `P` and `F`. -/
def liftY (B : Matrix (X × U) (X × U) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix F F ℂ))

/-- The regrouping `(P₀ P₁)((x U) F) → (P₀ x)(P₁ (U F))`. -/
def regroup (q : (P₀ × P₁) × ((X × U) × F)) : (P₀ × X) × (P₁ × (U × F)) :=
  ((q.1.1, q.2.1.1), (q.1.2, (q.2.1.2, q.2.2)))

/-- An operator on `P₀ x`, tensored with the identity on `P₁ U F`. -/
def liftH (h : Matrix (P₀ × X) (P₀ × X) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  (h ⊗ₖ (1 : Matrix (P₁ × (U × F)) (P₁ × (U × F)) ℂ)).submatrix regroup regroup

/-- The function `f(z) = ⟨θ, ρ_P^{[z]} ρ_Y^{[-z]} h ρ_P^{[-z]} ρ_Y^{[z]} θ⟩` of the
conditional skew estimate.  Area-law manuscript, `04-conditional.tex`, lines 495–500. -/
def skewFun (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (h : Matrix (P₀ × X) (P₀ × X) ℂ) (z : ℂ) : ℂ :=
  star θ ⬝ᵥ ((liftP (cfcC (margP θ) (suppPowFun z)) * liftY (cfcC (margY θ) (suppPowFun (-z))) *
    liftH h * liftP (cfcC (margP θ) (suppPowFun (-z))) *
    liftY (cfcC (margY θ) (suppPowFun z))) *ᵥ θ)

section Lifts

theorem liftP_mul (A B : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    liftP (X := X) (U := U) (F := F) A * liftP B = liftP (A * B) := by
  rw [liftP, liftP, liftP, ← mul_kronecker_mul, Matrix.one_mul]

theorem liftY_mul (A B : Matrix (X × U) (X × U) ℂ) :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) A * liftY B = liftY (A * B) := by
  rw [liftY, liftY, liftY, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.one_mul]

theorem liftP_liftY_comm (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) (B : Matrix (X × U) (X × U) ℂ) :
    liftP (F := F) A * liftY B = liftY B * liftP A := by
  rw [liftP, liftY, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_one]

theorem conjTranspose_liftP (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    (liftP (X := X) (U := U) (F := F) A)ᴴ = liftP Aᴴ := by
  rw [liftP, liftP, conjTranspose_kronecker, conjTranspose_one]

theorem conjTranspose_liftY (B : Matrix (X × U) (X × U) ℂ) :
    (liftY (P₀ := P₀) (P₁ := P₁) (F := F) B)ᴴ = liftY Bᴴ := by
  rw [liftY, liftY, conjTranspose_kronecker, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_one]

theorem conjTranspose_liftH (h : Matrix (P₀ × X) (P₀ × X) ℂ) :
    (liftH (U := U) (F := F) (P₁ := P₁) h)ᴴ = liftH hᴴ := by
  rw [liftH, liftH, conjTranspose_submatrix, conjTranspose_kronecker, conjTranspose_one]

theorem liftP_one : liftP (X := X) (U := U) (F := F) (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) = 1 := by
  rw [liftP, one_kronecker_one]

theorem liftY_one : liftY (P₀ := P₀) (P₁ := P₁) (F := F) (1 : Matrix (X × U) (X × U) ℂ) = 1 := by
  rw [liftY, one_kronecker_one, one_kronecker_one]

end Lifts

section Support

theorem suppPowFun_zero_add_ker (t : ℝ) :
    suppPowFun 0 t + (if t = 0 then 1 else 0) = 1 := by
  unfold suppPowFun; split_ifs <;> simp

theorem ker_mul_id (t : ℝ) : (if t = 0 then (1 : ℂ) else 0) * (t : ℂ) = 0 := by
  split_ifs with h <;> simp [h]

theorem dotProduct_mulVec_eq_trace' {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ (M *ᵥ v) = (M * vecMulVec v (star v)).trace := by
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- A Hermitian projection `K` on `P` with `tr (ρ_P K) = 0` annihilates `θ`. -/
theorem liftP_mulVec_eq_zero (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    {K : Matrix (P₀ × P₁) (P₀ × P₁) ℂ} (hK : Kᴴ = K) (hKK : K * K = K)
    (htr : (margP θ * K).trace = 0) : liftP K *ᵥ θ = 0 := by
  rw [← dotProduct_star_self_eq_zero, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    conjTranspose_liftP, hK, liftP_mul, hKK, dotProduct_mulVec_eq_trace', trace_mul_comm, liftP,
    ← trace_partialTraceRight_mul]
  exact htr

/-- A Hermitian projection `K` on `Y` with `tr (ρ_Y K) = 0` annihilates `θ`. -/
theorem liftY_mulVec_eq_zero (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    {K : Matrix (X × U) (X × U) ℂ} (hK : Kᴴ = K) (hKK : K * K = K)
    (htr : (margY θ * K).trace = 0) : liftY (P₀ := P₀) (P₁ := P₁) (F := F) K *ᵥ θ = 0 := by
  rw [← dotProduct_star_self_eq_zero, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
    conjTranspose_liftY, hK, liftY_mul, hKK, dotProduct_mulVec_eq_trace', trace_mul_comm, liftY,
    ← trace_partialTraceLeft_mul, ← trace_partialTraceRight_mul]
  exact htr

/-- The kernel indicator `t ↦ 1_{t = 0}`. -/
def kerFun (t : ℝ) : ℂ := if t = 0 then 1 else 0

theorem cfcC_ker_isHermitian {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (cfcC A kerFun)ᴴ = cfcC A kerFun := by
  rw [conjTranspose_cfcC hA]; congr 1; funext t; unfold kerFun; split_ifs <;> simp

theorem cfcC_ker_mul_self {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : cfcC A kerFun * cfcC A kerFun = cfcC A kerFun := by
  rw [cfcC_mul hA]; congr 1; funext t; unfold kerFun; split_ifs <;> simp

theorem mul_cfcC_ker {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : A * cfcC A kerFun = 0 := by
  calc A * cfcC A kerFun = cfcC A (fun t => (t : ℂ)) * cfcC A kerFun := by rw [cfcC_id hA]
    _ = 0 := by
      rw [cfcC_mul hA, cfcC_eq_spectralFun hA, ← zero_smul ℂ (1 : Matrix n n ℂ),
        ← spectralFun_const hA.eigenvectorUnitary 0]
      congr 1; funext k; unfold kerFun; split_ifs with h <;> simp [h]

theorem cfcC_supp_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : cfcC A (suppPowFun 0) = 1 - cfcC A kerFun := by
  rw [eq_sub_iff_add_eq, cfcC_add hA, ← cfcC_one hA]
  congr 1; funext t; unfold suppPowFun kerFun; split_ifs <;> simp

theorem liftP_sub (A B : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    liftP (X := X) (U := U) (F := F) (A - B) = liftP A - liftP B := by
  ext i j; simp [liftP, sub_mul]

theorem liftY_sub (A B : Matrix (X × U) (X × U) ℂ) :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) (A - B) = liftY A - liftY B := by
  ext i j; simp [liftY, sub_mul, mul_sub]

theorem liftP_supp_zero_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    liftP (cfcC (margP θ) (suppPowFun 0)) *ᵥ θ = θ := by
  have hA := (posSemidef_margP θ).1
  rw [cfcC_supp_zero hA, liftP_sub, liftP_one, sub_mulVec,
    one_mulVec, liftP_mulVec_eq_zero θ (cfcC_ker_isHermitian hA) (cfcC_ker_mul_self hA)
      (by rw [mul_cfcC_ker hA, trace_zero]), sub_zero]

theorem liftY_supp_zero_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) (cfcC (margY θ) (suppPowFun 0)) *ᵥ θ = θ := by
  have hA := (posSemidef_margY θ).1
  rw [cfcC_supp_zero hA, liftY_sub, liftY_one, sub_mulVec, one_mulVec, liftY_mulVec_eq_zero θ (cfcC_ker_isHermitian hA)
      (cfcC_ker_mul_self hA) (by rw [mul_cfcC_ker hA, trace_zero]), sub_zero]

end Support

section Powers

theorem suppPow_mul {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (z w : ℂ) :
    cfcC A (suppPowFun z) * cfcC A (suppPowFun w) = cfcC A (suppPowFun (z + w)) := by
  rw [cfcC_mul hA]; congr 1; funext t
  unfold suppPowFun
  split_ifs with h
  · simp
  · rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 h)]

theorem conjTranspose_suppPow {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) (z : ℂ) :
    (cfcC A (suppPowFun z))ᴴ = cfcC A (suppPowFun (starRingEnd ℂ z)) := by
  rw [conjTranspose_cfcC hA.1]
  refine cfcC_congr_of_nonneg hA fun t ht => ?_
  unfold suppPowFun
  split_ifs with h
  · simp
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    have harg : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_ne_zero.symm
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal]

end Powers

section Values

theorem star_dotProduct_mulVec_eq {n : Type*} [Fintype n] (M : Matrix n n ℂ) (x y : n → ℂ) :
    star x ⬝ᵥ (M *ᵥ y) = star (Mᴴ *ᵥ x) ⬝ᵥ y := by
  rw [star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec]

variable (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (h : Matrix (P₀ × X) (P₀ × X) ℂ)

/-- `f(0) = ⟨θ, h θ⟩`.  Area-law manuscript, `04-conditional.tex`, line 510. -/
theorem skewFun_zero : skewFun θ h 0 = star θ ⬝ᵥ (liftH h *ᵥ θ) := by
  have hP := (posSemidef_margP θ)
  have hY := (posSemidef_margY θ)
  rw [skewFun, neg_zero, ← mulVec_mulVec, liftY_supp_zero_mulVec, ← mulVec_mulVec,
    liftP_supp_zero_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, star_dotProduct_mulVec_eq,
    conjTranspose_liftP, conjTranspose_suppPow hP, map_zero, liftP_supp_zero_mulVec,
    star_dotProduct_mulVec_eq, conjTranspose_liftY, conjTranspose_suppPow hY, map_zero,
    liftY_supp_zero_mulVec]

theorem conj_ofReal_mul_I (y : ℝ) : starRingEnd ℂ ((y : ℂ) * Complex.I) = -((y : ℂ) * Complex.I) := by
  simp [Complex.conj_ofReal]

/-- On the imaginary axis, `f(iy) = ⟨v, h v⟩` with `v = ρ_P^{[-iy]} ρ_Y^{[iy]} θ`.  Area-law
manuscript, `04-conditional.tex`, lines 532–533. -/
theorem skewFun_imag (y : ℝ) :
    skewFun θ h ((y : ℂ) * Complex.I) =
      star (liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
          (liftY (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ)) ⬝ᵥ
        (liftH h *ᵥ (liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
          (liftY (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ))) := by
  have hP := (posSemidef_margP θ)
  have hY := (posSemidef_margY θ)
  rw [skewFun, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
    star_dotProduct_mulVec_eq, star_dotProduct_mulVec_eq, conjTranspose_liftP,
    conjTranspose_suppPow hP, conj_ofReal_mul_I, conjTranspose_liftY, conjTranspose_suppPow hY,
    map_neg, conj_ofReal_mul_I, neg_neg, mulVec_mulVec, ← liftP_liftY_comm, ← mulVec_mulVec]

/-- The vector `v = ρ_P^{[-iy]} ρ_Y^{[iy]} θ` has the norm of `θ`. -/
theorem dotProduct_star_imag_vector (y : ℝ) :
    star (liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
        (liftY (P₀ := P₀) (P₁ := P₁) (F := F) (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ)) ⬝ᵥ
      (liftP (cfcC (margP θ) (suppPowFun (-((y : ℂ) * Complex.I)))) *ᵥ
        (liftY (cfcC (margY θ) (suppPowFun ((y : ℂ) * Complex.I))) *ᵥ θ)) = star θ ⬝ᵥ θ := by
  have hP := (posSemidef_margP θ)
  have hY := (posSemidef_margY θ)
  rw [star_mulVec_dotProduct, conjTranspose_liftP, conjTranspose_suppPow hP, map_neg,
    conj_ofReal_mul_I, neg_neg, mulVec_mulVec, liftP_mul, suppPow_mul hP.1, add_neg_cancel,
    mulVec_mulVec, liftP_liftY_comm, ← mulVec_mulVec, liftP_supp_zero_mulVec, star_mulVec_dotProduct,
    conjTranspose_liftY, conjTranspose_suppPow hY, conj_ofReal_mul_I, mulVec_mulVec, liftY_mul,
    suppPow_mul hY.1, neg_add_cancel, liftY_supp_zero_mulVec]

end Values

end Entropy.ConditionalSkew

end
