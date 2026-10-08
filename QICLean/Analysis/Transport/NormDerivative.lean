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

theorem conj_mulVec_mulVec {U : Matrix n n ℂ} (hU : star U * U = 1) (K : Matrix n n ℂ)
    (y : n → ℂ) : (U * K * star U) *ᵥ (U *ᵥ y) = U *ᵥ (K *ᵥ y) := by
  rw [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one, mulVec_mulVec]

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

/-! ### The derivative of `M^{-1/2}` along a path -/

theorem filteredNormSq_eq {M : Matrix n n ℂ} (hM : M.PosDef) (pre : n → ℂ) :
    filteredNormSq M pre = (star pre ⬝ᵥ (M ^ (-(1 / 2) : ℝ) *ᵥ pre)).re := by
  unfold filteredNormSq filteredRaw
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, (hM.rpow_isHermitian _).eq,
    hM.rpow_mul_rpow]
  norm_num

theorem rpow_neg_half_mul_self_mul {M : Matrix n n ℂ} (hM : M.PosDef) :
    M ^ (-(1 / 2) : ℝ) * M * M ^ (-(1 / 2) : ℝ) = 1 := by
  conv_lhs => rw [show M ^ (-(1 / 2) : ℝ) * M = M ^ (-(1 / 2) : ℝ) * M ^ (1 : ℝ) by
    rw [hM.rpow_one]]
  rw [hM.rpow_mul_rpow, hM.rpow_mul_rpow]
  norm_num
  exact hM.rpow_zero

/-- `q ↦ M(q)^{-1/2}` is differentiable along a differentiable path of positive definite
matrices, and its derivative `G'` satisfies `G' M G + G M' G + G M G' = 0`. -/
theorem exists_hasDerivAt_rpow_neg_half {M : ℝ → Matrix n n ℂ} {D : Matrix n n ℂ} {p : ℝ}
    (hM : ∀ q, (M q).PosDef) (hD : HasDerivAt M D p) :
    ∃ G' : Matrix n n ℂ, HasDerivAt (fun q => M q ^ (-(1 / 2) : ℝ)) G' p ∧
      G' * M p * M p ^ (-(1 / 2) : ℝ) + M p ^ (-(1 / 2) : ℝ) * D * M p ^ (-(1 / 2) : ℝ) +
        M p ^ (-(1 / 2) : ℝ) * M p * G' = 0 := by
  have hd := (differentiableWithinAt_rpow_neg_half (hM p)).hasFDerivWithinAt
  have hm : MapsTo M univ (hermitianSet n) := fun q _ => (hM q).isHermitian
  have h := (hd.restrictScalars ℝ).comp_hasDerivWithinAt p hD.hasDerivWithinAt hm
  rw [hasDerivWithinAt_univ] at h
  obtain ⟨G', hG⟩ : ∃ G', HasDerivAt (fun q => M q ^ (-(1 / 2) : ℝ)) G' p :=
    ⟨_, by convert h using 1; rfl⟩
  refine ⟨G', hG, ?_⟩
  have hprod := (hG.mul hD).mul hG
  have hconst : ((fun q => M q ^ (-(1 / 2) : ℝ)) * M * fun q => M q ^ (-(1 / 2) : ℝ)) =
      fun _ => 1 :=
    funext fun q => rpow_neg_half_mul_self_mul (hM q)
  rw [hconst] at hprod
  have := hprod.unique (hasDerivAt_const p (1 : Matrix n n ℂ))
  rw [← this]
  simp only [Pi.mul_apply]
  noncomm_ring

/-! ### The norm derivative -/

theorem filteredNormSq_pos {M : Matrix n n ℂ} (hM : M.PosDef) {pre : n → ℂ} (hpre : pre ≠ 0) :
    0 < filteredNormSq M pre := by
  have hne : filteredRaw M pre ≠ 0 := by
    intro h0
    apply hpre
    have : M ^ (1 / 4 : ℝ) *ᵥ filteredRaw M pre = pre := by
      rw [filteredRaw, mulVec_mulVec, hM.rpow_mul_rpow_neg, one_mulVec]
    rw [← this, h0, mulVec_zero]
  exact (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hne)).1

/-- `star (M^{-1/4} pre) ⬝ᵥ M^{-1/4} pre = N²` as a complex number. -/
theorem star_dotProduct_filteredRaw (M : Matrix n n ℂ) (pre : n → ℂ) :
    star (filteredRaw M pre) ⬝ᵥ filteredRaw M pre = (filteredNormSq M pre : ℂ) := by
  have h0 : 0 ≤ star (filteredRaw M pre) ⬝ᵥ filteredRaw M pre := dotProduct_star_self_nonneg _
  apply Complex.ext
  · simp [filteredNormSq]
  · simpa [filteredNormSq] using (Complex.nonneg_iff.mp h0).2.symm

/-- The filtered vector is a unit vector. -/
theorem star_dotProduct_filteredVector {M : Matrix n n ℂ} (hM : M.PosDef) {pre : n → ℂ}
    (hpre : pre ≠ 0) : star (filteredVector M pre) ⬝ᵥ filteredVector M pre = 1 := by
  have hN := filteredNormSq_pos hM hpre
  rw [filteredVector, star_smul, smul_dotProduct, dotProduct_smul, star_dotProduct_filteredRaw]
  simp only [smul_eq_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_assoc,
    ← mul_inv, Real.mul_self_sqrt hN.le, inv_mul_cancel₀ hN.ne', Complex.ofReal_one]


/-- Conjugating a sum `G' M G + G D G + G M G' = 0` into the eigenbasis of `M`. -/
theorem relation_eigen {M G' D : Matrix n n ℂ} (hM : M.PosDef)
    (hrel : G' * M * M ^ (-(1 / 2) : ℝ) + M ^ (-(1 / 2) : ℝ) * D * M ^ (-(1 / 2) : ℝ) +
      M ^ (-(1 / 2) : ℝ) * M * G' = 0) (r t : n) :
    (star (eigU hM.isHermitian) * G' * eigU hM.isHermitian) r t *
        (((hM.isHermitian.eigenvalues t ^ (1 / 2 : ℝ) : ℝ) : ℂ) +
          ((hM.isHermitian.eigenvalues r ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
      -(((hM.isHermitian.eigenvalues r ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) *
        (star (eigU hM.isHermitian) * D * eigU hM.isHermitian) r t *
          ((hM.isHermitian.eigenvalues t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) := by
  set U := eigU hM.isHermitian
  set x := hM.isHermitian.eigenvalues
  have hx : ∀ i, 0 < x i := hM.eigenvalues_pos
  have hUU : star U * U = 1 := star_eigU_mul _
  have hUU' : U * star U = 1 := eigU_mul_star _
  have hc : ∀ X : Matrix n n ℂ, star U * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hMe : M = U * diagonal (fun i => ((x i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [← hM.rpow_one, rpow_eq_eigen hM]
    simp [x, U]
  have hGe : M ^ (-(1 / 2) : ℝ) = U * diagonal (fun i => ((x i ^ (-(1 / 2) : ℝ) : ℝ) : ℂ)) *
      star U := rpow_eq_eigen hM _
  have hG'e : G' = U * (star U * G' * U) * star U := by
    simp only [← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
  have hDe : D = U * (star U * D * U) * star U := by
    simp only [← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
  set g := star U * G' * U
  set d := star U * D * U
  rw [hGe, hG'e, hDe, hMe] at hrel
  have h2 := congrArg (fun X => star U * X * U) hrel
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hc, hUU, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul] at h2
  have h3 := congrFun (congrFun h2 r) t
  simp only [← Matrix.mul_assoc, add_apply, zero_apply, mul_diagonal, diagonal_mul,
    diagonal_mul_diagonal] at h3
  have e : ∀ i, ((x i : ℝ) : ℂ) * ((x i ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) =
      ((x i ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    intro i
    rw [← Complex.ofReal_mul]
    congr 1
    rw [show x i * x i ^ (-(1 / 2) : ℝ) = x i ^ (1 : ℝ) * x i ^ (-(1 / 2) : ℝ) by
      rw [Real.rpow_one], ← Real.rpow_add (hx i)]
    norm_num
  linear_combination h3 - g r t * e t - g r t * e r

/-- **The derivative of the filtered norm** (`06-transport.tex`, display
`transport:norm-derivative` and the Fourier formula `transport:g-fourier`,
lines 470--491): for a differentiable path of positive definite matrices with
`M(p)^{-1/2} M'(p) M(p)^{-1/2} = 𝖧`,
`-∂_p log N² = ∫ m_{1/4}(u) ⟨M^{-iu} v, 𝖧 M^{-iu} v⟩ du`. -/
theorem hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt {M : ℝ → Matrix n n ℂ}
    {D : Matrix n n ℂ} {p : ℝ} (hM : ∀ q, (M q).PosDef) (hD : HasDerivAt M D p)
    {pre : n → ℂ} (hpre : pre ≠ 0) :
    HasDerivAt (fun q => -Real.log (filteredNormSq (M q) pre))
      (∫ u, fourierWeight u *
        (star (imagPow (M p) u *ᵥ filteredVector (M p) pre) ⬝ᵥ
          ((M p ^ (-(1 / 2) : ℝ) * D * M p ^ (-(1 / 2) : ℝ)) *ᵥ
            (imagPow (M p) u *ᵥ filteredVector (M p) pre))).re) p := by
  obtain ⟨G', hG, hrel⟩ := exists_hasDerivAt_rpow_neg_half hM hD
  -- The derivative of `N²`.
  let Ll : Matrix n n ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun X => star pre ⬝ᵥ (X *ᵥ pre)
      map_add' := fun X Y => by simp [add_mulVec, dotProduct_add]
      map_smul' := fun c X => by simp [smul_mulVec, dotProduct_smul] }
  have hN : HasDerivAt (fun q => filteredNormSq (M q) pre) (star pre ⬝ᵥ (G' *ᵥ pre)).re p := by
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt p
      (((LinearMap.toContinuousLinearMap Ll).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt p hG)
    convert h1 using 1
    · funext q
      simp [filteredNormSq_eq (hM q), Ll]
    · rfl
  have hNp := filteredNormSq_pos (hM p) hpre
  have hlog := (hN.log hNp.ne').neg
  convert hlog using 1
  -- Spectral coordinates at `p`.
  set Mp := M p with hMp_def
  have hMp : Mp.PosDef := hM p
  set U := eigU hMp.isHermitian
  set x := hMp.isHermitian.eigenvalues
  have hx : ∀ i, 0 < x i := hMp.eigenvalues_pos
  have hUU : star U * U = 1 := star_eigU_mul _
  have hUU' : U * star U = 1 := eigU_mul_star _
  have hc : ∀ X : Matrix n n ℂ, star U * (U * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  set N2 := filteredNormSq Mp pre
  set a := star U *ᵥ pre
  set g := star U * G' * U
  set d := star U * D * U
  have hpre_e : pre = U *ᵥ a := by rw [mulVec_mulVec, hUU', one_mulVec]
  have hG'e : G' = U * g * star U := by
    simp only [g, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
  have hDe : D = U * d * star U := by
    simp only [d, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    rw [Matrix.mul_assoc, hUU', Matrix.mul_one]
  have hpow : ∀ s : ℝ, Mp ^ s = U * diagonal (fun i => ((x i ^ s : ℝ) : ℂ)) * star U :=
    fun s => rpow_eq_eigen hMp s
  clear_value a g d
  -- The left side in coordinates.
  have hL : star pre ⬝ᵥ (G' *ᵥ pre) = ∑ r, ∑ t, star (a r) * g r t * a t := by
    rw [hG'e, hpre_e, conj_mulVec_mulVec hUU, star_mulVec_dotProduct_mulVec hUU]
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => ?_
    ring
  sorry

end Matrix.Transport
