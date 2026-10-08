/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ConditionalSkewStrip
import QICLean.Entropy.MarginalPhaseSingular
import QICLean.Analysis.SkewFromPhases

/-!
# The conditional skew estimate

This file finishes Lemma 5.3 of the area-law manuscript.  On the imaginary axis the
skew function is an expectation `f(iu) = ⟨w_u, h w_u⟩` with
`w_u = ρ̂_Y^{iu} ρ̂_{YF}^{-iu} θ` (Schmidt mirroring across `P` and `Y F`).  The comparison
vector `w_u⁰ = ρ̂_U^{iu} ρ̂_{UF}^{-iu} θ` is a unitary on `U F` applied to `θ`, so
`⟨w_u⁰, h w_u⁰⟩ = ⟨θ, h θ⟩`, and `w_u - w_u⁰` is a unitary image of the phase difference
of Lemma 5.2 applied to `θ`.  This gives
`|f(iu) - p| ≤ 4 √p |sinh π u| 𝓡_η + 4 sinh²(π u) 𝓡_η²`, and the analytic departure bound
`Complex.norm_sub_re_le_of_phase_bounds` with the rate estimate `𝓡_η ≤ 3 ℓ (min 1 η)^{1/4}`
yields the lemma.

## Main results

* `Entropy.ConditionalSkew.cfcC_kronecker_one_mulVec` — Schmidt mirroring.
* `Entropy.ConditionalSkew.norm_skewFun_imag_sub_le` — the imaginary-axis comparison.
* `Entropy.ConditionalSkew.phaseRate_le` — the rate in terms of `ℓ_h` and `η`.
* `Entropy.ConditionalSkew.conditionalSkew_le` — Lemma 5.3.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Lemma 5.3 (`lem:skew`),
  `04-conditional.tex`, lines 487–600.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix Entropy.MarginalPhase

/-- The kernel-completed phase function `t ↦ t^{iu}` for `t ≠ 0` and `1` at `0`. -/
def hatFun (u : ℝ) (t : ℝ) : ℂ := if t = 0 then 1 else ((t : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)

section Generic

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

theorem hatPhase_eq_cfcC {M : Matrix n n ℂ} (hM : M.IsHermitian) (u : ℝ) :
    hatPhase hM u = cfcC M (hatFun u) := by
  rw [cfcC_eq_spectralFun hM]; rfl

theorem hatFun_neg_mul (u t : ℝ) : hatFun (-u) t * hatFun u t = 1 := by
  unfold hatFun
  split_ifs with h
  · simp
  · rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 h)]
    push_cast
    ring_nf
    simp

theorem cfcC_hat_neg_mul {M : Matrix n n ℂ} (hM : M.IsHermitian) (u : ℝ) :
    cfcC M (hatFun (-u)) * cfcC M (hatFun u) = 1 := by
  rw [cfcC_mul hM]; simp_rw [hatFun_neg_mul]; exact cfcC_one hM

theorem cfcC_hat_mul_neg {M : Matrix n n ℂ} (hM : M.IsHermitian) (u : ℝ) :
    cfcC M (hatFun u) * cfcC M (hatFun (-u)) = 1 := by
  simpa using cfcC_hat_neg_mul hM (-u)

theorem cfcC_suppPow_imag {M : Matrix n n ℂ} (hM : M.IsHermitian) (u : ℝ) :
    cfcC M (suppPowFun ((u : ℂ) * Complex.I)) = cfcC M (hatFun u) - cfcC M kerFun := by
  rw [eq_sub_iff_add_eq, cfcC_add hM]
  congr 1; funext t; unfold suppPowFun hatFun kerFun; split_ifs <;> simp

theorem conjTranspose_cfcC_hat {M : Matrix n n ℂ} (hM : M.PosSemidef) (u : ℝ) :
    (cfcC M (hatFun u))ᴴ = cfcC M (hatFun (-u)) := by
  rw [conjTranspose_cfcC hM.1]
  refine cfcC_congr_of_nonneg hM fun t ht => ?_
  unfold hatFun
  split_ifs with h
  · simp
  · have hpos : 0 < t := lt_of_le_of_ne ht (Ne.symm h)
    have harg : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hpos.le]; exact Real.pi_ne_zero.symm
    have hc := Complex.cpow_conj (t : ℂ) ((u : ℂ) * Complex.I) harg
    rw [Complex.conj_ofReal] at hc
    rw [← hc]
    congr 1
    simp [Complex.conj_ofReal]

/-- Coefficient matrix of a vector on `n × m`. -/
def coeffMat (θ : n × m → ℂ) : Matrix n m ℂ := Matrix.of fun a b => θ (a, b)

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem partialTraceRight_vecMulVec (θ : n × m → ℂ) :
    partialTraceRight (vecMulVec θ (star θ)) = coeffMat θ * (coeffMat θ)ᴴ := by
  ext i j; simp [coeffMat, vecMulVec, mul_apply]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem partialTraceLeft_vecMulVec (θ : n × m → ℂ) :
    partialTraceLeft (vecMulVec θ (star θ)) = ((coeffMat θ)ᴴ * coeffMat θ)ᵀ := by
  ext i j; simp [coeffMat, vecMulVec, mul_apply, mul_comm]

omit [DecidableEq n] in
theorem kronecker_one_mulVec_apply (M : Matrix n n ℂ) (θ : n × m → ℂ) (a : n) (b : m) :
    ((M ⊗ₖ (1 : Matrix m m ℂ)) *ᵥ θ) (a, b) = (M * coeffMat θ) a b := by
  simp [mulVec, dotProduct, one_apply, Fintype.sum_prod_type, mul_apply, coeffMat]

omit [DecidableEq m] in
theorem one_kronecker_mulVec_apply (N : Matrix m m ℂ) (θ : n × m → ℂ) (a : n) (b : m) :
    (((1 : Matrix n n ℂ) ⊗ₖ N) *ᵥ θ) (a, b) = (coeffMat θ * Nᵀ) a b := by
  simp [mulVec, dotProduct, one_apply, Fintype.sum_prod_type, mul_apply, coeffMat,
    mul_comm]

/-- **Schmidt mirroring.**  For a vector `θ` on `n ⊗ m` with marginals `ρ_n`, `ρ_m` and any
function `g`, `(g(ρ_n) ⊗ I) θ = (I ⊗ g(ρ_m)) θ`.  Area-law manuscript,
`04-conditional.tex`, lines 532–534 and 544–546. -/
theorem cfcC_kronecker_one_mulVec (θ : n × m → ℂ) (g : ℝ → ℂ) :
    (cfcC (partialTraceRight (vecMulVec θ (star θ))) g ⊗ₖ (1 : Matrix m m ℂ)) *ᵥ θ =
      ((1 : Matrix n n ℂ) ⊗ₖ cfcC (partialTraceLeft (vecMulVec θ (star θ))) g) *ᵥ θ := by
  set C := coeffMat θ
  have hA : (C * Cᴴ).IsHermitian := isHermitian_mul_conjTranspose_self C
  have hB : (Cᴴ * C).IsHermitian := isHermitian_conjTranspose_mul_self C
  have key : cfcC (C * Cᴴ) g * C = C * cfcC (Cᴴ * C) g :=
    cfcC_mul_intertwine hA hB C (by rw [Matrix.mul_assoc]) g
  have htr : (cfcC ((Cᴴ * C)ᵀ) g)ᵀ = cfcC (Cᴴ * C) g := by
    rw [cfcC_transpose hB.transpose, transpose_transpose]
  funext ⟨a, b⟩
  rw [kronecker_one_mulVec_apply, one_kronecker_mulVec_apply, partialTraceRight_vecMulVec,
    partialTraceLeft_vecMulVec, htr, key]

omit [DecidableEq n] in
theorem norm_toLp_comp_equiv_symm {l : Type*} [Fintype l] (e : n ≃ l) (v : n → ℂ) :
    ‖(WithLp.toLp 2 (v ∘ e.symm) : EuclideanSpace ℂ l)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toLp_sq_eq_re', norm_toLp_sq_eq_re']
  congr 1
  change (star v ∘ e.symm) ⬝ᵥ (v ∘ e.symm) = star v ⬝ᵥ v
  rw [dotProduct_comp_equiv_symm]
  congr 1; funext i; simp

theorem norm_toLp_mulVec_of_unitary {R : Matrix n n ℂ} (hR : Rᴴ * R = 1) (v : n → ℂ) :
    ‖(WithLp.toLp 2 (R *ᵥ v) : EuclideanSpace ℂ n)‖ = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ n)‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_toLp_sq_eq_re', norm_toLp_sq_eq_re', star_mulVec_dotProduct, mulVec_mulVec, hR,
    one_mulVec]

theorem dotProduct_mulVec_conj_unitary {R H : Matrix n n ℂ} (hR : Rᴴ * R = 1)
    (hc : R * H = H * R) (v : n → ℂ) :
    star (R *ᵥ v) ⬝ᵥ (H *ᵥ (R *ᵥ v)) = star v ⬝ᵥ (H *ᵥ v) := by
  rw [star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, ← hc,
    ← Matrix.mul_assoc, hR, Matrix.one_mul]

/-- For `0 ≤ H ≤ 1`, `|⟨w, H w⟩ - ⟨w₀, H w₀⟩| ≤ 2 √⟨w₀, H w₀⟩ ‖w - w₀‖ + ‖w - w₀‖²`.
Area-law manuscript, `04-conditional.tex`, lines 556–559. -/
theorem norm_quadForm_sub_le {H : Matrix n n ℂ} (h0 : 0 ≤ H) (h1 : H ≤ 1) (w w₀ : n → ℂ) :
    ‖star w ⬝ᵥ (H *ᵥ w) - star w₀ ⬝ᵥ (H *ᵥ w₀)‖ ≤
      2 * √((star w₀ ⬝ᵥ (H *ᵥ w₀)).re) * ‖(WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ n)‖ +
        ‖(WithLp.toLp 2 (w - w₀) : EuclideanSpace ℂ n)‖ ^ 2 := by
  set B := CFC.sqrt H
  have hB : Bᴴ = B := (CFC.sqrt_nonneg H).isSelfAdjoint.star_eq
  have hHB : H = Bᴴ * B := by rw [hB]; exact (CFC.sqrt_mul_sqrt_self H h0).symm
  have hform : ∀ x y : n → ℂ, star x ⬝ᵥ (H *ᵥ y) = star (B *ᵥ x) ⬝ᵥ (B *ᵥ y) := by
    intro x y; rw [hHB, ← mulVec_mulVec, ← star_mulVec_dotProduct]
  have hBsq : ∀ x : n → ℂ, ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℂ n)‖ =
      √((star x ⬝ᵥ (H *ᵥ x)).re) := by
    intro x
    rw [hform, ← norm_toLp_sq_eq_re', Real.sqrt_sq (norm_nonneg _)]
  have hBle : ∀ x : n → ℂ, ‖(WithLp.toLp 2 (B *ᵥ x) : EuclideanSpace ℂ n)‖ ≤
      ‖(WithLp.toLp 2 x : EuclideanSpace ℂ n)‖ := by
    intro x
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [norm_toLp_sq_eq_re', norm_toLp_sq_eq_re', ← hform]
    have := (le_iff.1 h1).dotProduct_mulVec_nonneg x
    rw [sub_mulVec, one_mulVec, dotProduct_sub, sub_nonneg, Complex.le_def] at this
    exact this.1
  set e := w - w₀
  have hw : w = w₀ + e := by simp [e]
  have hexp : star w ⬝ᵥ (H *ᵥ w) - star w₀ ⬝ᵥ (H *ᵥ w₀) =
      star (B *ᵥ e) ⬝ᵥ (B *ᵥ w₀) + star (B *ᵥ w₀) ⬝ᵥ (B *ᵥ e) +
        star (B *ᵥ e) ⬝ᵥ (B *ᵥ e) := by
    rw [hform, hform, hw, mulVec_add, star_add, add_dotProduct, dotProduct_add, dotProduct_add]
    ring
  set a := ‖(WithLp.toLp 2 (B *ᵥ w₀) : EuclideanSpace ℂ n)‖
  set E := ‖(WithLp.toLp 2 e : EuclideanSpace ℂ n)‖
  have hBe := hBle e
  rw [hexp, ← hBsq w₀]
  calc _ ≤ ‖star (B *ᵥ e) ⬝ᵥ (B *ᵥ w₀)‖ + ‖star (B *ᵥ w₀) ⬝ᵥ (B *ᵥ e)‖ +
        ‖star (B *ᵥ e) ⬝ᵥ (B *ᵥ e)‖ := norm_add₃_le
    _ ≤ E * a + a * E + E * E := by
        gcongr
        · exact (norm_star_dotProduct_le _ _).trans (mul_le_mul_of_nonneg_right hBe (norm_nonneg _))
        · exact (norm_star_dotProduct_le _ _).trans (mul_le_mul_of_nonneg_left hBe (norm_nonneg _))
        · exact (norm_star_dotProduct_le _ _).trans (mul_le_mul hBe hBe (norm_nonneg _)
            (norm_nonneg _))
    _ = 2 * a * E + E ^ 2 := by ring

end Generic


section EtaBounds

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- Strong subadditivity: `I(x:F|U) ≥ 0`. -/
theorem condMutualInfo_nonneg {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} (hρ : ρ.PosSemidef) :
    0 ≤ condMutualInfo ρ hρ := by
  have h := strongSubadditivity_of_posSemidef ρ hρ
  have hU : marginalU ρ = partialTraceRight (partialTraceLeft ρ) := by
    ext i j
    simp only [marginalU, marginalXU, partialTraceLeft_apply, partialTraceRight_apply,
      submatrix_apply]
    exact Finset.sum_comm
  rw [vonNeumannEntropy_congr hU.symm _
    ((posSemidef_marginalXU hρ).partialTraceLeft.isHermitian)] at h
  unfold condMutualInfo
  have : vonNeumannEntropy (marginalXU ρ) (hρ.submatrix assocE).partialTraceRight.isHermitian =
      vonNeumannEntropy (partialTraceRight (reassoc ρ))
        (partialTraceRight_isHermitian (hρ.isHermitian.submatrix _)) := rfl
  rw [this]
  unfold marginalUF
  linarith

/-- `I(x:F|U) ≤ 2 log (dim x)` for a density matrix. -/
theorem condMutualInfo_le_two_log {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    condMutualInfo ρ hρ ≤ 2 * Real.log (Fintype.card X) := by
  have h1 := abs_conditionalEntropy_le_log_card hρ htr
  have h2 := abs_conditionalEntropy_le_log_card (posSemidef_marginalXU hρ)
    (by rw [trace_marginalXU, htr])
  have heq : condMutualInfo ρ hρ =
      conditionalEntropy (marginalXU ρ) (posSemidef_marginalXU hρ).isHermitian -
        conditionalEntropy ρ hρ.isHermitian := by
    simp only [condMutualInfo, conditionalEntropy, marginalU, marginalUF]
    ring
  rw [heq]
  linarith [abs_le.1 h1, abs_le.1 h2]

end EtaBounds

section Skew

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁]
  [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F]

/-- The marginal `ρ_W` reassociated to `x (U F)`. -/
def rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  (margW θ).submatrix assocE.symm assocE.symm

/-- An operator on `x (U F)`, tensored with the identity on `P`. -/
def liftR (M : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) ⊗ₖ M.submatrix assocE assocE

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem liftR_mul (A B : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) A * liftR B = liftR (A * B) := by
  rw [liftR, liftR, liftR, ← mul_kronecker_mul, Matrix.one_mul, submatrix_mul_equiv]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F]
  [DecidableEq F] in
theorem liftR_sub (A B : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) (A - B) = liftR A - liftR B := by
  ext i j; simp [liftR, mul_sub]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [Fintype U] [Fintype F] in
theorem liftR_one :
    liftR (P₀ := P₀) (P₁ := P₁) (1 : Matrix (X × (U × F)) (X × (U × F)) ℂ) = 1 := by
  rw [liftR, submatrix_one_equiv, one_kronecker_one]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F]
  [DecidableEq F] in
theorem conjTranspose_liftR (A : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (liftR (P₀ := P₀) (P₁ := P₁) A)ᴴ = liftR Aᴴ := by
  rw [liftR, liftR, conjTranspose_kronecker, conjTranspose_one, conjTranspose_submatrix]

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F]
  in
theorem liftR_embedF (B : Matrix (X × U) (X × U) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) (embedF (F := F) B) = liftY B := by
  rw [liftR, embedF, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id, liftY]

theorem liftR_cfcC_rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (g : ℝ → ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) (cfcC (rhoW θ) g) =
      (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) ⊗ₖ cfcC (margW θ) g := by
  rw [liftR, rhoW, cfcC_submatrix_equiv (posSemidef_margW θ).1, submatrix_submatrix,
    Equiv.symm_comp_self, submatrix_id_id]

theorem liftP_liftR_comm (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ)
    (B : Matrix (X × (U × F)) (X × (U × F)) ℂ) : liftP A * liftR B = liftR B * liftP A := by
  rw [liftP, liftR, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_one]

/-- Schmidt mirroring across `P` and `W`: `g(ρ_P) θ = g(ρ_W) θ`. -/
theorem liftP_cfcC_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (g : ℝ → ℂ) :
    liftP (cfcC (margP θ) g) *ᵥ θ = liftR (cfcC (rhoW θ) g) *ᵥ θ := by
  rw [liftP, liftR_cfcC_rhoW]
  exact cfcC_kronecker_one_mulVec θ g

omit [DecidableEq P₀] [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [DecidableEq F] in
theorem marginalXU_rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    marginalXU (rhoW θ) = margY θ := by
  rw [marginalXU, rhoW, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]; rfl

theorem liftP_ker_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    liftP (cfcC (margP θ) kerFun) *ᵥ θ = 0 := by
  have hA := (posSemidef_margP θ).1
  exact liftP_mulVec_eq_zero θ (cfcC_ker_isHermitian hA) (cfcC_ker_mul_self hA)
    (by rw [mul_cfcC_ker hA, trace_zero])

theorem liftY_ker_mulVec (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    liftY (P₀ := P₀) (P₁ := P₁) (F := F) (cfcC (margY θ) kerFun) *ᵥ θ = 0 := by
  have hA := (posSemidef_margY θ).1
  exact liftY_mulVec_eq_zero θ (cfcC_ker_isHermitian hA) (cfcC_ker_mul_self hA)
    (by rw [mul_cfcC_ker hA, trace_zero])

/-- The imaginary-axis vector `ρ_P^{[-iu]} ρ_Y^{[iu]} θ` equals
`w_u = ρ̂_Y^{iu} ρ̂_{YF}^{-iu} θ`.  Area-law manuscript, `04-conditional.tex`, lines 532–535. -/
theorem imag_vector_eq (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    liftP (cfcC (margP θ) (suppPowFun (-((u : ℂ) * Complex.I)))) *ᵥ
        (liftY (cfcC (margY θ) (suppPowFun ((u : ℂ) * Complex.I))) *ᵥ θ) =
      liftR (embedF (cfcC (margY θ) (hatFun u)) * cfcC (rhoW θ) (hatFun (-u))) *ᵥ θ := by
  have hP := (posSemidef_margP θ).1
  have hY := (posSemidef_margY θ).1
  have hneg : -((u : ℂ) * Complex.I) = ((-u : ℝ) : ℂ) * Complex.I := by push_cast; ring
  set a := cfcC (margP θ) (hatFun (-u))
  have hker : liftY (P₀ := P₀) (P₁ := P₁) (F := F) (cfcC (margY θ) kerFun) *ᵥ (liftP a *ᵥ θ) = 0
      := by
    rw [mulVec_mulVec, ← liftP_liftY_comm, ← mulVec_mulVec, liftY_ker_mulVec, mulVec_zero]
  rw [hneg, cfcC_suppPow_imag hP, cfcC_suppPow_imag hY, mulVec_mulVec, liftP_liftY_comm,
    ← mulVec_mulVec, liftP_sub, sub_mulVec, liftP_ker_mulVec, sub_zero, liftY_sub, sub_mulVec,
    hker, sub_zero, liftP_cfcC_mulVec, ← liftR_embedF, mulVec_mulVec, liftR_mul]

omit [Fintype X] [Fintype U] [DecidableEq U] [Fintype F] in
theorem embedF_one_kronecker (A : Matrix U U ℂ) :
    embedF (F := F) ((1 : Matrix X X ℂ) ⊗ₖ A) = (1 : Matrix X X ℂ) ⊗ₖ (A ⊗ₖ (1 : Matrix F F ℂ))
        := by
  ext ⟨x, u, f⟩ ⟨x', u', f'⟩
  simp [embedF, mul_assoc]

omit [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁] [Fintype X] [DecidableEq X]
  [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F] in
theorem regroup_bijective :
    Function.Bijective (regroup (P₀ := P₀) (P₁ := P₁) (X := X) (U := U) (F := F)) :=
  ⟨regroup_injective, fun ⟨⟨a, c⟩, ⟨b, ⟨d, e⟩⟩⟩ => ⟨⟨⟨a, b⟩, ⟨⟨c, d⟩, e⟩⟩, rfl⟩⟩

omit [Fintype P₀] [Fintype P₁] [Fintype X] [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F]
  in
theorem liftR_one_kronecker_eq (K : Matrix (U × F) (U × F) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) ((1 : Matrix X X ℂ) ⊗ₖ K) =
      ((1 : Matrix (P₀ × X) (P₀ × X) ℂ) ⊗ₖ ((1 : Matrix P₁ P₁ ℂ) ⊗ₖ K)).submatrix
        regroup regroup := by
  ext ⟨⟨a, b⟩, ⟨⟨c, d⟩, e⟩⟩ ⟨⟨a', b'⟩, ⟨⟨c', d'⟩, e'⟩⟩
  simp only [liftR, regroup, kronecker_apply, submatrix_apply, Equiv.prodAssoc_apply,
    one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

theorem liftR_one_kronecker_comm_liftH (K : Matrix (U × F) (U × F) ℂ)
    (h : Matrix (P₀ × X) (P₀ × X) ℂ) :
    liftR (P₀ := P₀) (P₁ := P₁) ((1 : Matrix X X ℂ) ⊗ₖ K) * liftH h =
      liftH h * liftR ((1 : Matrix X X ℂ) ⊗ₖ K) := by
  rw [liftR_one_kronecker_eq, liftH, ← submatrix_mul _ _ _ _ _ regroup_bijective,
    ← submatrix_mul _ _ _ _ _ regroup_bijective, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem posSemidef_rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : (rhoW θ).PosSemidef :=
  (posSemidef_margW θ).submatrix _

/-- The unitary `ρ̂_U^{iu} ρ̂_{UF}^{-iu}` on `U F`. -/
def zetaUF (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) : Matrix (U × F) (U × F) ℂ :=
  (cfcC (marginalU (rhoW θ)) (hatFun u) ⊗ₖ (1 : Matrix F F ℂ)) *
    cfcC (marginalUF (rhoW θ)) (hatFun (-u))

/-- The operator `(ρ̂_U^{-iu} ρ̂_Y^{iu}) ⊗ I_F - ρ̂_{UF}^{-iu} ρ̂_W^{iu}` on `x (U F)`. -/
def phaseDiffW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  embedF (((1 : Matrix X X ℂ) ⊗ₖ cfcC (marginalU (rhoW θ)) (hatFun (-u))) *
      cfcC (margY θ) (hatFun u)) -
    ((1 : Matrix X X ℂ) ⊗ₖ cfcC (marginalUF (rhoW θ)) (hatFun (-u))) * cfcC (rhoW θ) (hatFun u)

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] in
theorem zetaUF_unitary (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    (zetaUF θ u)ᴴ * zetaUF θ u = 1 := by
  have hU := posSemidef_marginalU (posSemidef_rhoW θ)
  have hUF := posSemidef_marginalUF (posSemidef_rhoW θ)
  rw [zetaUF, conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_cfcC_hat hU, conjTranspose_cfcC_hat hUF, neg_neg, Matrix.mul_assoc,
    ← Matrix.mul_assoc (_ ⊗ₖ _), ← mul_kronecker_mul, cfcC_hat_neg_mul hU.1, Matrix.one_mul,
    one_kronecker_one, Matrix.one_mul, cfcC_hat_mul_neg hUF.1]

theorem liftR_zetaUF_unitary (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    (liftR (P₀ := P₀) (P₁ := P₁) ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u))ᴴ *
      liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) = 1 := by
  rw [conjTranspose_liftR, liftR_mul, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul, zetaUF_unitary, one_kronecker_one, liftR_one]

/-- The comparison vector `w_u⁰ = ρ̂_U^{iu} ρ̂_{UF}^{-iu} θ` gives `⟨w_u⁰, h w_u⁰⟩ = ⟨θ, h θ⟩`.
Area-law manuscript, `04-conditional.tex`, lines 537–539. -/
theorem comparison_vector_quadForm (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    (h : Matrix (P₀ × X) (P₀ × X) ℂ) (u : ℝ) :
    star (liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *ᵥ θ) ⬝ᵥ
        (liftH h *ᵥ (liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *ᵥ θ)) =
      star θ ⬝ᵥ (liftH h *ᵥ θ) :=
  dotProduct_mulVec_conj_unitary (liftR_zetaUF_unitary θ u)
    (liftR_one_kronecker_comm_liftH _ h) θ

/-- The unitary `ρ̂_P^{-iu} ρ̂_U^{iu}` relating `w_u - w_u⁰` to the phase difference. -/
def relUnitary (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  liftP (cfcC (margP θ) (hatFun (-u))) *
    liftR (embedF ((1 : Matrix X X ℂ) ⊗ₖ cfcC (marginalU (rhoW θ)) (hatFun u)))

theorem relUnitary_unitary (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    (relUnitary θ u)ᴴ * relUnitary θ u = 1 := by
  have hP := posSemidef_margP θ
  have hU := posSemidef_marginalU (posSemidef_rhoW θ)
  rw [relUnitary, conjTranspose_mul, conjTranspose_liftP, conjTranspose_liftR,
    conjTranspose_embedF, conjTranspose_kronecker, conjTranspose_one, conjTranspose_cfcC_hat hP,
    conjTranspose_cfcC_hat hU, neg_neg, Matrix.mul_assoc, ← Matrix.mul_assoc (liftP _),
    liftP_mul, cfcC_hat_mul_neg hP.1, liftP_one, Matrix.one_mul, liftR_mul, embedF_mul,
    ← mul_kronecker_mul, Matrix.one_mul, cfcC_hat_neg_mul hU.1, one_kronecker_one, embedF_one,
    liftR_one]

/-- `w_u - w_u⁰` is a unitary image of the phase difference applied to `θ`.  Area-law
manuscript, `04-conditional.tex`, lines 540–550. -/
theorem imag_vector_sub_eq (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    liftR (embedF (cfcC (margY θ) (hatFun u)) * cfcC (rhoW θ) (hatFun (-u))) *ᵥ θ -
        liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *ᵥ θ =
      relUnitary θ u *ᵥ (liftR (phaseDiffW θ u) *ᵥ θ) := by
  have hP := (posSemidef_margP θ).1
  have hU := (posSemidef_marginalU (posSemidef_rhoW θ)).1
  have hb : embedF (F := F) ((1 : Matrix X X ℂ) ⊗ₖ cfcC (marginalU (rhoW θ)) (hatFun u)) *
      phaseDiffW θ u = embedF (cfcC (margY θ) (hatFun u)) -
        ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) * cfcC (rhoW θ) (hatFun u) := by
    rw [phaseDiffW, Matrix.mul_sub, embedF_mul, ← Matrix.mul_assoc, ← mul_kronecker_mul,
      Matrix.one_mul, cfcC_hat_mul_neg hU, one_kronecker_one, Matrix.one_mul,
      ← Matrix.mul_assoc, embedF_one_kronecker, ← mul_kronecker_mul, Matrix.one_mul, zetaUF]
  have h1 : ∀ E : Matrix (X × (U × F)) (X × (U × F)) ℂ,
      liftP (cfcC (margP θ) (hatFun (-u))) *ᵥ (liftR E *ᵥ θ) =
        liftR (E * cfcC (rhoW θ) (hatFun (-u))) *ᵥ θ := by
    intro E
    rw [mulVec_mulVec, liftP_liftR_comm, ← mulVec_mulVec, liftP_cfcC_mulVec, mulVec_mulVec,
      liftR_mul]
  have h2 : liftP (cfcC (margP θ) (hatFun (-u))) *ᵥ (liftR (((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *
      cfcC (rhoW θ) (hatFun u)) *ᵥ θ) = liftR ((1 : Matrix X X ℂ) ⊗ₖ zetaUF θ u) *ᵥ θ := by
    rw [← liftR_mul, ← mulVec_mulVec, ← liftP_cfcC_mulVec, mulVec_mulVec, liftP_liftR_comm,
      ← mulVec_mulVec, mulVec_mulVec (v := θ), liftP_mul, cfcC_hat_neg_mul hP, liftP_one,
      one_mulVec]
  rw [relUnitary, ← mulVec_mulVec, mulVec_mulVec (M := liftR _), liftR_mul, hb, liftR_sub,
    sub_mulVec, mulVec_sub, h1, h2]

/-- The reindexing `P W ≃ (x (U F)) P`. -/
def reindexE : (P₀ × P₁) × ((X × U) × F) ≃ (X × (U × F)) × (P₀ × P₁) :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr assocE (Equiv.refl _))

/-- The vector `θ` reindexed to `(x (U F)) P`, as in Lemma 5.2. -/
def thetaR (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    EuclideanSpace ℂ ((X × (U × F)) × (P₀ × P₁)) :=
  WithLp.toLp 2 (θ ∘ reindexE.symm)

omit [Fintype P₀] [Fintype P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F]
  [DecidableEq F] in
theorem kronecker_one_eq_submatrix_liftR (M : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    M ⊗ₖ (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) = (liftR M).submatrix reindexE.symm reindexE.symm := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp [liftR, reindexE, mul_comm]

omit [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem kronecker_one_mulVec_thetaR (θ : (P₀ × P₁) × ((X × U) × F) → ℂ)
    (M : Matrix (X × (U × F)) (X × (U × F)) ℂ) :
    (M ⊗ₖ (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ)) *ᵥ (thetaR θ).ofLp =
      (liftR M *ᵥ θ) ∘ reindexE.symm := by
  rw [kronecker_one_eq_submatrix_liftR, submatrix_mulVec_equiv]
  congr 2

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem norm_thetaR {θ : (P₀ × P₁) × ((X × U) × F) → ℂ} (hθ : star θ ⬝ᵥ θ = 1) :
    ‖thetaR θ‖ = 1 := by
  rw [thetaR, norm_toLp_comp_equiv_symm]
  have h := norm_toLp_sq_eq_re' θ
  rw [hθ, Complex.one_re] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 θ : EuclideanSpace ℂ ((P₀ × P₁) × ((X × U) × F)))]

omit [DecidableEq P₀] [DecidableEq P₁] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F] in
theorem partialTraceRight_thetaR (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) :
    partialTraceRight (vecMulVec (thetaR θ).ofLp (star (thetaR θ).ofLp)) = rhoW θ := by
  ext i j
  simp [thetaR, rhoW, margW, reindexE, vecMulVec]

omit [DecidableEq P₀] [DecidableEq P₁] in
theorem phaseDifference_thetaR (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (u : ℝ) :
    phaseDifference (posSemidef_vecMulVec_self_star (thetaR θ).ofLp).partialTraceRight u =
      phaseDiffW θ u := by
  simp only [phaseDifference, hatPhase_eq_cfcC]
  rw [partialTraceRight_thetaR, marginalXU_rhoW]
  rfl

theorem condMutualInfo_congr {A B : Matrix (X × (U × F)) (X × (U × F)) ℂ} (h : A = B)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : condMutualInfo A hA = condMutualInfo B hB := by
  subst h; rfl

/-- The conditional mutual information `η = I(x:F|U)_θ` of the conditional skew estimate.
Area-law manuscript, `04-conditional.tex`, line 494. -/
def skewEta (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : ℝ :=
  condMutualInfo (rhoW θ) (posSemidef_rhoW θ)

/-- Lemma 5.2 applied to `θ`: `‖w_u - w_u⁰‖ ≤ 2 |sinh π u| 𝓡_η`.  Area-law manuscript,
`04-conditional.tex`, lines 551–553. -/
theorem norm_liftR_phaseDiffW_le {θ : (P₀ × P₁) × ((X × U) × F) → ℂ} (hθ : star θ ⬝ᵥ θ = 1)
    (u : ℝ) :
    ‖(WithLp.toLp 2 (liftR (phaseDiffW θ u) *ᵥ θ) : EuclideanSpace ℂ _)‖ ≤
      2 * |Real.sinh (Real.pi * u)| * phaseRate (Fintype.card X) (skewEta θ) := by
  have h := norm_phaseDifference_mulVec_le (thetaR θ) (norm_thetaR hθ) u
  rw [phaseDifference_thetaR, kronecker_one_mulVec_thetaR, norm_toLp_comp_equiv_symm,
    condMutualInfo_congr (partialTraceRight_thetaR θ) _ (posSemidef_rhoW θ)] at h
  exact h

/-- **Imaginary-axis comparison** for the conditional skew function: with `p = ⟨θ, h θ⟩`,
`|f(iu) - p| ≤ 4 √p |sinh π u| 𝓡_η + 4 sinh²(π u) 𝓡_η²`.  Area-law manuscript,
`04-conditional.tex`, lines 531–559. -/
theorem norm_skewFun_imag_sub_le {θ : (P₀ × P₁) × ((X × U) × F) → ℂ} (hθ : star θ ⬝ᵥ θ = 1)
    {h : Matrix (P₀ × X) (P₀ × X) ℂ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (u : ℝ) :
    ‖skewFun θ h ((u : ℂ) * Complex.I) - skewFun θ h 0‖ ≤
      4 * √((skewFun θ h 0).re) * |Real.sinh (Real.pi * u)| *
          phaseRate (Fintype.card X) (skewEta θ) +
        4 * Real.sinh (Real.pi * u) ^ 2 * phaseRate (Fintype.card X) (skewEta θ) ^ 2 := by
  have hH0 : 0 ≤ liftH (P₁ := P₁) (U := U) (F := F) h :=
    nonneg_iff_posSemidef.2 (posSemidef_liftH (nonneg_iff_posSemidef.1 hh0))
  have hH1 : liftH (P₁ := P₁) (U := U) (F := F) h ≤ 1 := by
    rw [le_iff, ← liftH_one, ← liftH_sub]; exact posSemidef_liftH (le_iff.1 hh1)
  set R := phaseRate (Fintype.card X) (skewEta θ)
  set s := |Real.sinh (Real.pi * u)|
  have hE := norm_liftR_phaseDiffW_le hθ u
  rw [skewFun_imag, imag_vector_eq, skewFun_zero, ← comparison_vector_quadForm θ h u]
  refine (norm_quadForm_sub_le hH0 hH1 _ _).trans ?_
  rw [imag_vector_sub_eq, norm_toLp_mulVec_of_unitary (relUnitary_unitary θ u),
    comparison_vector_quadForm]
  set E := ‖(WithLp.toLp 2 (liftR (phaseDiffW θ u) *ᵥ θ) : EuclideanSpace ℂ _)‖
  have hE0 : 0 ≤ E := norm_nonneg _
  have hs : Real.sinh (Real.pi * u) ^ 2 = s ^ 2 := (sq_abs _).symm
  rw [hs]
  have hp := Real.sqrt_nonneg ((star θ ⬝ᵥ (liftH (P₁ := P₁) (U := U) (F := F) h *ᵥ θ)).re)
  nlinarith [mul_le_mul_of_nonneg_left hE hp, mul_le_mul hE hE hE0 (le_trans hE0 hE)]

end Skew

section Rate

theorem neg_mul_log_le_two_sqrt {η : ℝ} (hη : 0 < η) : -(η * Real.log η) ≤ 2 * √η := by
  have hs : 0 < √η := Real.sqrt_pos.2 hη
  have h1 := Real.log_le_sub_one_of_pos (inv_pos.2 hs)
  rw [Real.log_inv] at h1
  have h2 : Real.log η = 2 * Real.log √η := by rw [Real.log_sqrt hη.le]; ring
  have h4 : -Real.log √η ≤ (√η)⁻¹ := by linarith
  rw [h2]
  calc -(η * (2 * Real.log √η)) = 2 * η * (-Real.log √η) := by ring
    _ ≤ 2 * η * (√η)⁻¹ := by gcongr
    _ = 2 * √η := by rw [mul_assoc, ← div_eq_mul_inv, Real.div_sqrt]

theorem one_le_log_exp_mul {D : ℝ} (hD : 1 ≤ D) : 1 ≤ Real.log (Real.exp 1 * D) := by
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]
  linarith [Real.log_nonneg hD]

/-- The rate of Lemma 5.2 in the form used by Lemma 5.3: for `1 ≤ D`, `log (e D) ≤ ℓ` and
`η ≤ 2 ℓ`, `𝓡_η ≤ 3 ℓ (min 1 η)^{1/4}`.  Area-law manuscript, `04-conditional.tex`,
lines 590–600. -/
theorem phaseRate_le {D ℓ η : ℝ} (hD : 1 ≤ D) (hDℓ : Real.log (Real.exp 1 * D) ≤ ℓ)
    (hη : η ≤ 2 * ℓ) : phaseRate D η ≤ 3 * ℓ * √√(min 1 η) := by
  have hL := one_le_log_exp_mul hD
  have hℓ : 1 ≤ ℓ := hL.trans hDℓ
  have heD : 0 < Real.exp 1 * D := by positivity
  unfold phaseRate
  split_ifs with h0
  · by_cases h1 : η ≤ 1
    · rw [min_eq_right h1]
      have hsη : √η ≤ 1 := Real.sqrt_le_one.mpr h1
      have hηs : η ≤ √η := by
        calc η = √η * √η := (Real.mul_self_sqrt h0.le).symm
          _ ≤ 1 * √η := by gcongr
          _ = √η := one_mul _
      have hss : √η ≤ √√η := by
        have h4 : √√η ≤ 1 := Real.sqrt_le_one.mpr hsη
        calc √η = √√η * √√η := (Real.mul_self_sqrt (Real.sqrt_nonneg η)).symm
          _ ≤ 1 * √√η := by gcongr
          _ = √√η := one_mul _
      have hlog : η * Real.log (Real.exp 1 * D / η) ≤ 3 * ℓ * √η := by
        rw [Real.log_div heD.ne' h0.ne', mul_sub]
        have := neg_mul_log_le_two_sqrt h0
        have : η * Real.log (Real.exp 1 * D) ≤ ℓ * √η := by
          calc η * Real.log (Real.exp 1 * D) ≤ √η * ℓ :=
                mul_le_mul hηs hDℓ (by linarith) (Real.sqrt_nonneg _)
            _ = ℓ * √η := mul_comm _ _
        nlinarith [Real.sqrt_nonneg η]
      have h3 : √(η * Real.log (Real.exp 1 * D / η)) ≤ 2 * ℓ * √√η := by
        calc √(η * Real.log (Real.exp 1 * D / η)) ≤ √(3 * ℓ * √η) := Real.sqrt_le_sqrt hlog
          _ = √(3 * ℓ) * √√η := Real.sqrt_mul (by linarith) _
          _ ≤ 2 * ℓ * √√η := by
              gcongr
              rw [Real.sqrt_le_left (by linarith)]
              nlinarith
      nlinarith [Real.sqrt_nonneg √η]
    · push Not at h1
      rw [min_eq_left h1.le, div_one, Real.sqrt_one, Real.sqrt_one, mul_one]
      have h3 : √(η * Real.log (Real.exp 1 * D)) ≤ 3 / 2 * ℓ := by
        rw [Real.sqrt_le_left (by linarith)]
        nlinarith
      linarith
  · positivity

theorem phaseRate_nonneg (D η : ℝ) : 0 ≤ phaseRate D η := by
  unfold phaseRate; split_ifs <;> positivity

theorem sqrt_sqrt_sqrt_eq_rpow {x : ℝ} (hx : 0 ≤ x) : √√√x = x ^ (1 / 8 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx,
    ← Real.rpow_mul hx]
  norm_num

end Rate

section Estimate

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁]
  [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F]

omit [DecidableEq P₀] [DecidableEq P₁] [DecidableEq X] [DecidableEq U] [DecidableEq F] in
theorem trace_rhoW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : (rhoW θ).trace = star θ ⬝ᵥ θ := by
  rw [← partialTraceRight_thetaR, trace_partialTraceRight, trace_vecMulVec, dotProduct_comm]
  change (star θ ∘ reindexE.symm) ⬝ᵥ (θ ∘ reindexE.symm) = _
  rw [dotProduct_comp_equiv_symm]
  congr 1

/-- The constant `C = 18 π² + 6144 e^{π² + 1}` of the conditional skew estimate. -/
def skewConst : ℝ := 18 * Real.pi ^ 2 + 6144 * Real.exp (Real.pi ^ 2 + 1)

/-- **Conditional skew estimate** (area-law manuscript, Lemma 5.3, `lem:skew`,
`04-conditional.tex`, lines 487–507).  Let `θ` be a unit vector on `P, x, U, F` with
`P = P₀ P₁`, let `0 ≤ h ≤ 1` act on `P₀ x`, put `d_h = (dim P₀)(dim x)`,
`ℓ_h = log (e d_h)` and `η = I(x:F|U)_θ`, and let
`f(z) = ⟨θ, ρ_P^{[z]} ρ_Y^{[-z]} h ρ_P^{[-z]} ρ_Y^{[z]} θ⟩` with `Y = x U`.  For
`0 < a ℓ_h ≤ 1/8` and `t = a/2`, `|f(t)| - Re f(t) ≤ C a² ℓ_h⁴ η^{1/8}` with the universal
constant `C = skewConst`. -/
theorem conditionalSkew_le {θ : (P₀ × P₁) × ((X × U) × F) → ℂ} (hθ : star θ ⬝ᵥ θ = 1)
    {h : Matrix (P₀ × X) (P₀ × X) ℂ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) {a : ℝ} (ha : 0 < a)
    (hac : a * Real.log (Real.exp 1 * Fintype.card (P₀ × X)) ≤ 1 / 8) :
    ‖skewFun θ h ((a / 2 : ℝ) : ℂ)‖ - (skewFun θ h ((a / 2 : ℝ) : ℂ)).re ≤
      skewConst * a ^ 2 * Real.log (Real.exp 1 * Fintype.card (P₀ × X)) ^ 4 *
        skewEta θ ^ (1 / 8 : ℝ) := by
  have hne : Nonempty ((P₀ × P₁) × ((X × U) × F)) := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    simp [dotProduct] at hθ
  obtain ⟨⟨⟨p0, _⟩, ⟨⟨x0, _⟩, _⟩⟩⟩ := hne
  set d : ℝ := (Fintype.card (P₀ × X) : ℝ) with hd
  set ℓ := Real.log (Real.exp 1 * d) with hℓdef
  set η := skewEta θ with hηdef
  set R := phaseRate (Fintype.card X) η with hRdef
  have hP0 : (1 : ℝ) ≤ Fintype.card P₀ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨p0⟩
  have hX1 : (1 : ℝ) ≤ Fintype.card X := by exact_mod_cast Fintype.card_pos_iff.2 ⟨x0⟩
  have hXd : (Fintype.card X : ℝ) ≤ d := by
    rw [hd, Fintype.card_prod, Nat.cast_mul]; nlinarith
  have hd1 : 1 ≤ d := hX1.trans hXd
  have hℓ1 : 1 ≤ ℓ := one_le_log_exp_mul hd1
  have hlogX : Real.log (Real.exp 1 * Fintype.card X) ≤ ℓ :=
    Real.log_le_log (by positivity) (by gcongr)
  have hlogd : Real.log d ≤ ℓ := by
    rw [hℓdef, Real.log_mul (Real.exp_pos 1).ne' (by linarith), Real.log_exp]; linarith
  have hη0 : 0 ≤ η := condMutualInfo_nonneg _
  have hη2 : η ≤ 2 * ℓ := by
    have := condMutualInfo_le_two_log (posSemidef_rhoW θ) (by rw [trace_rhoW, hθ])
    have h2 : Real.log (Fintype.card X) ≤ Real.log d := Real.log_le_log (by linarith) hXd
    change η ≤ _ at this
    linarith
  have hR := phaseRate_le hX1 hlogX hη2
  have hR0 : 0 ≤ R := phaseRate_nonneg _ _
  have hf0 := skewFun_zero_nonneg θ h hh0
  rw [Complex.nonneg_iff] at hf0
  have hherm : h.IsHermitian := (nonneg_iff_posSemidef.1 hh0).1
  have main := Complex.norm_sub_re_le_of_phase_bounds (f := skewFun θ h)
    (differentiable_skewFun θ h) (m := d ^ 2) (ℓ := ℓ) (R := R) (p := (skewFun θ h 0).re)
    (one_le_pow₀ hd1) hℓ1 (by rw [Real.log_pow]; push_cast; linarith) hR0 hf0.1
    (Complex.ext rfl (by simpa using hf0.2.symm)) (skewFun_neg_conj θ h hherm)
    (norm_skewFun_imag_le θ h hθ hh0 hh1)
    (fun z hz => norm_skewFun_le_of_strip θ hθ hh0 hh1 (hz.trans (by norm_num)))
    (norm_skewFun_imag_sub_le hθ hh0 hh1) (t := a / 2)
    (by
      rw [abs_of_pos (by positivity), le_div_iff₀ (by positivity)]
      nlinarith)
  refine main.trans ?_
  -- the rate estimates
  set μ := min 1 η with hμ
  have hμ0 : 0 ≤ μ := le_min zero_le_one hη0
  have hμ1 : μ ≤ 1 := min_le_left _ _
  set q := √√μ
  set r := √q
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq1 : q ≤ 1 := Real.sqrt_le_one.mpr (Real.sqrt_le_one.mpr hμ1)
  have hqr : q ≤ r := by
    have h4 : r ≤ 1 := Real.sqrt_le_one.mpr hq1
    calc q = r * r := (Real.mul_self_sqrt hq0).symm
      _ ≤ 1 * r := by gcongr
      _ = r := one_mul _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrη : r ≤ η ^ (1 / 8 : ℝ) := by
    rw [show r = √√√μ from rfl, sqrt_sqrt_sqrt_eq_rpow hμ0]
    exact Real.rpow_le_rpow hμ0 (min_le_right _ _) (by norm_num)
  have hR2 : R ^ 2 ≤ 9 * ℓ ^ 2 * r := by
    have : R ^ 2 ≤ (3 * ℓ * q) ^ 2 := pow_le_pow_left₀ hR0 hR 2
    have hq2 : q ^ 2 ≤ r := by nlinarith
    nlinarith
  have hsq : √(min 1 R) ≤ 2 * ℓ * r := by
    calc √(min 1 R) ≤ √(3 * ℓ * q) := Real.sqrt_le_sqrt ((min_le_right _ _).trans hR)
      _ = √(3 * ℓ) * r := Real.sqrt_mul (by linarith) _
      _ ≤ 2 * ℓ * r := by
          gcongr
          rw [Real.sqrt_le_left (by linarith)]
          nlinarith
  have hE : 0 ≤ Real.exp (Real.pi ^ 2 + 1) := (Real.exp_pos _).le
  have hℓ2 : ℓ ^ 2 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have hℓ3 : ℓ ^ 3 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have hη8 : 0 ≤ η ^ (1 / 8 : ℝ) := Real.rpow_nonneg hη0 _
  have hπ : 0 ≤ Real.pi ^ 2 := sq_nonneg _
  have hA : 8 * Real.pi ^ 2 * R ^ 2 ≤ 72 * Real.pi ^ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hR2 (by positivity : (0 : ℝ) ≤ 8 * Real.pi ^ 2)
    have h9 : 9 * ℓ ^ 2 * r ≤ 9 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by
      gcongr
    nlinarith
  have hB : 12288 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 2 * √(min 1 R) ≤
      24576 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by
    have h1 : ℓ ^ 2 * √(min 1 R) ≤ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by
      calc ℓ ^ 2 * √(min 1 R) ≤ ℓ ^ 2 * (2 * ℓ * r) := by gcongr
        _ = 2 * ℓ ^ 3 * r := by ring
        _ ≤ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by gcongr
    calc 12288 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 2 * √(min 1 R) =
        12288 * Real.exp (Real.pi ^ 2 + 1) * (ℓ ^ 2 * √(min 1 R)) := by ring
      _ ≤ 12288 * Real.exp (Real.pi ^ 2 + 1) * (2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ)) := by gcongr
      _ = _ := by ring
  calc (a / 2) ^ 2 * (8 * Real.pi ^ 2 * R ^ 2 +
        12288 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 2 * √(min 1 R)) ≤
      (a / 2) ^ 2 * (72 * Real.pi ^ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) +
        24576 * Real.exp (Real.pi ^ 2 + 1) * ℓ ^ 4 * η ^ (1 / 8 : ℝ)) := by gcongr
    _ = skewConst * a ^ 2 * ℓ ^ 4 * η ^ (1 / 8 : ℝ) := by rw [skewConst]; ring

end Estimate

end Entropy.ConditionalSkew

end
