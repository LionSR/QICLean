/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.PathDerivative

/-!
# The derivative of the filtered norm

For a differentiable path `M(q)` of positive definite matrices and a nonzero vector `pre`,
put `N(q)² = ‖M(q)^{-1/4} pre‖²`, `v = M^{-1/4} pre / N` and
`𝖧 = M^{-1/2} M' M^{-1/2}`. Then
$$-\partial_q\log N^2=\int_{\mathbb R}m_{1/4}(u)\,
  \langle M^{-iu}v,\mathsf H M^{-iu}v\rangle\,du$$
(area-law paper, Proposition 7.4, displays `transport:norm-derivative` and
`transport:g-fourier`, `06-transport.tex` lines 470--491).

The proof follows the source: diagonalize `M = U diag(x) U*`. The derivative `G'` of
`G = M^{-1/2}` is obtained from `G M G = 1`, which gives
`G'_{rt} (√x_r + √x_t) = -x_r^{-1/2} D_{rt} x_t^{-1/2}` in the eigenbasis. The coefficient of
`D_{rt}` is then the scalar identity `g_{1/4}(log x_r - log x_t) = (x_r x_t)^{1/4} /
(√x_r + √x_t)` (line 479), and the Fourier formula of Lemma 7.3 turns `g_{1/4}` into the
integral over `u`.

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Set Filter Topology MeasureTheory Complex

namespace Matrix.Transport

/-! ### Scalar identities -/

/-- `g_{1/4}(w) = 1 / (2 cosh (w/4))`. -/
theorem sinhRatio_quarter (w : ℝ) : Real.sinhRatio (1 / 4) w = 1 / (2 * Real.cosh (w / 4)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [Real.sinhRatio_zero]; norm_num
  · rw [Real.sinhRatio_of_ne_zero _ hw]
    have h2 : w / 2 = 2 * (w / 4) := by ring
    have hs : Real.sinh (w / 4) ≠ 0 := by
      rw [Ne, Real.sinh_eq_zero]; intro h; apply hw; linarith
    have hc : Real.cosh (w / 4) ≠ 0 := (Real.cosh_pos _).ne'
    rw [h2, Real.sinh_two_mul, show 1 / 4 * w = w / 4 by ring]
    field_simp

/-- The coefficient identity of the norm derivative (`06-transport.tex` lines 476--481): for
`x, y > 0`,
`x^{-3/4} y^{-3/4} g_{1/4}(log x - log y) = x^{-1/2} y^{-1/2} / (x^{1/2} + y^{1/2})`. -/
theorem rpow_mul_sinhRatio_quarter {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x ^ (-(1 / 4) : ℝ) * y ^ (-(1 / 4) : ℝ) * (x ^ (-(1 / 2) : ℝ) * y ^ (-(1 / 2) : ℝ)) *
        Real.sinhRatio (1 / 4) (Real.log x - Real.log y) =
      x ^ (-(1 / 2) : ℝ) * y ^ (-(1 / 2) : ℝ) / (x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ)) := by
  rw [sinhRatio_quarter, Real.cosh_eq]
  simp only [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
  set α := Real.log x
  set β := Real.log y
  have hd1 : Real.exp ((α - β) / 4) + Real.exp (-((α - β) / 4)) ≠ 0 := by positivity
  have hd2 : Real.exp (α * (1 / 2)) + Real.exp (β * (1 / 2)) ≠ 0 := by positivity
  field_simp
  simp only [← Real.exp_add]
  rw [mul_add, ← Real.exp_add, ← Real.exp_add]
  congr 1 <;> congr 1 <;> ring

/-! ### Fourier integrals of finite exponential sums -/

theorem quarter_mem_Ioo : (1 / 4 : ℝ) ∈ Ioo (0 : ℝ) (1 / 2) := by norm_num

theorem norm_cexp_I_mul_mul (u z : ℝ) : ‖cexp (I * u * z)‖ = 1 := by
  rw [show I * u * z = ((u * z : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

theorem integrable_cexp_mul_fourierWeight (z : ℝ) :
    Integrable fun u : ℝ => cexp (I * u * z) * (fourierWeight u : ℂ) :=
  (Real.integrable_sinhRatioDensity quarter_mem_Ioo).ofReal.bdd_mul (c := 1)
    (by fun_prop) (ae_of_all _ fun u => (norm_cexp_I_mul_mul u z).le)

/-- The Fourier formula applied termwise to a finite exponential sum
(`06-transport.tex` lines 487--489). -/
theorem integral_fourierWeight_mul_re_sum {κ : Type*} [Fintype κ] (z : κ → ℝ) (β : κ → ℂ) :
    ∫ u : ℝ, fourierWeight u * (∑ k, β k * cexp (I * u * z k)).re =
      (∑ k, β k * (Real.sinhRatio (1 / 4) (z k) : ℂ)).re := by
  have hint : ∀ k, Integrable fun u : ℝ => β k * (cexp (I * u * z k) * (fourierWeight u : ℂ)) :=
    fun k => (integrable_cexp_mul_fourierWeight (z k)).const_mul _
  calc ∫ u : ℝ, fourierWeight u * (∑ k, β k * cexp (I * u * z k)).re
      = ∫ u : ℝ, (∑ k, β k * (cexp (I * u * z k) * (fourierWeight u : ℂ))).re := by
        congr 1; funext u
        rw [← Complex.re_ofReal_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = (∫ u : ℝ, ∑ k, β k * (cexp (I * u * z k) * (fourierWeight u : ℂ))).re :=
        integral_re (integrable_finsetSum _ fun k _ => hint k)
    _ = (∑ k, β k * (Real.sinhRatio (1 / 4) (z k) : ℂ)).re := by
        rw [integral_finsetSum _ fun k _ => hint k]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul, Complex.integral_exp_mul_sinhRatioDensity quarter_mem_Ioo]

/-! ### Spectral coordinates -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvector unitary of a Hermitian matrix, as a matrix. -/
noncomputable abbrev eigU {M : Matrix n n ℂ} (hM : M.IsHermitian) : Matrix n n ℂ :=
  (hM.eigenvectorUnitary : Matrix n n ℂ)

theorem star_eigU_mul {M : Matrix n n ℂ} (hM : M.IsHermitian) : star (eigU hM) * eigU hM = 1 :=
  Unitary.coe_star_mul_self _

theorem eigU_mul_star {M : Matrix n n ℂ} (hM : M.IsHermitian) : eigU hM * star (eigU hM) = 1 :=
  Unitary.coe_mul_star_self _

theorem cfc_eq_eigen {M : Matrix n n ℂ} (hM : M.IsHermitian) (f : ℝ → ℝ) :
    cfc f M = eigU hM * diagonal (fun i => ((f (hM.eigenvalues i) : ℝ) : ℂ)) * star (eigU hM) := by
  rw [hM.cfc_eq]; rfl

theorem rpow_eq_eigen {M : Matrix n n ℂ} (hM : M.PosDef) (s : ℝ) :
    M ^ s = eigU hM.isHermitian *
      diagonal (fun i => ((hM.isHermitian.eigenvalues i ^ s : ℝ) : ℂ)) *
        star (eigU hM.isHermitian) := by
  rw [CFC.rpow_eq_cfc_real hM.posSemidef.nonneg, cfc_eq_eigen]

theorem log_eq_eigen {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    CFC.log M = eigU hM * diagonal (fun i => ((Real.log (hM.eigenvalues i) : ℝ) : ℂ)) *
      star (eigU hM) :=
  cfc_eq_eigen hM _

theorem imagPow_eq_eigen {M : Matrix n n ℂ} (hM : M.IsHermitian) (u : ℝ) :
    imagPow M u = eigU hM *
      diagonal (fun i => cexp (((-u : ℝ) : ℂ) * (I * (Real.log (hM.eigenvalues i) : ℂ)))) *
        star (eigU hM) := by
  have hUinv : (eigU hM)⁻¹ = star (eigU hM) := Matrix.inv_eq_left_inv (star_eigU_mul hM)
  have hunit : IsUnit (eigU hM) := isUnit_iff_exists_inv.mpr ⟨_, eigU_mul_star hM⟩
  rw [imagPow, hermitianUnitaryPath, log_eq_eigen hM]
  have hsm : (-u : ℝ) • (I • (eigU hM * diagonal (fun i => ((Real.log (hM.eigenvalues i) : ℝ) : ℂ)) *
      star (eigU hM))) = eigU hM * diagonal (fun i => ((-u : ℝ) : ℂ) *
        (I * (Real.log (hM.eigenvalues i) : ℂ))) * (eigU hM)⁻¹ := by
    rw [hUinv]
    have : diagonal (fun i => ((-u : ℝ) : ℂ) * (I * (Real.log (hM.eigenvalues i) : ℂ))) =
        (-u : ℝ) • (I • diagonal (fun i => ((Real.log (hM.eigenvalues i) : ℝ) : ℂ))) := by
      ext i j; simp only [diagonal_apply, smul_apply]; split_ifs <;> simp [Complex.real_smul]
    rw [this]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hsm, Matrix.exp_conj _ _ hunit, exp_diagonal, Pi.exp_def, hUinv]
  simp only [← Complex.exp_eq_exp_ℂ]

/-- A unitary preserves the sesquilinear pairing. -/
theorem star_mulVec_dotProduct_mulVec {U : Matrix n n ℂ} (hU : star U * U = 1) (a b : n → ℂ) :
    star (U *ᵥ a) ⬝ᵥ (U *ᵥ b) = star a ⬝ᵥ b := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose, hU, one_mulVec]

/-- **The quadratic form in spectral coordinates.** For `W = U diag(e) U*`, `H = U K U*` and
`v = U c`, `⟨W v, H W v⟩ = ∑_{r,t} c̄_r ē_r K_{rt} e_t c_t`. -/
theorem quadForm_eigen {U K : Matrix n n ℂ} (hU : star U * U = 1) (e c : n → ℂ) :
    star ((U * diagonal e * star U) *ᵥ (U *ᵥ c)) ⬝ᵥ
        ((U * K * star U) *ᵥ ((U * diagonal e * star U) *ᵥ (U *ᵥ c))) =
      ∑ r, ∑ t, star (c r) * (star (e r) * K r t * e t) * c t := by
  have h1 : (U * diagonal e * star U) *ᵥ (U *ᵥ c) = U *ᵥ (diagonal e *ᵥ c) := by
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one, mulVec_mulVec]
  have h2 : ∀ y, (U * K * star U) *ᵥ (U *ᵥ y) = U *ᵥ (K *ᵥ y) := fun y => by
    rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one, mulVec_mulVec]
  rw [h1, h2, star_mulVec_dotProduct_mulVec hU]
  simp only [dotProduct, Pi.star_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mulVec_diagonal, mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mulVec_diagonal, star_mul']
  ring

end Matrix.Transport
