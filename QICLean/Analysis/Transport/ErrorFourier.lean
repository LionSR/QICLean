/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Defs
import QICLean.Channel.Schwarz.TwoVariable
import QICLean.Channel.Schwarz.PositiveMapProperties

/-!
# Fourier form of the transported square

For a positive definite `R`, a matrix `L` and `s = 1/4`, the error operators
`R^{±s} L R^{∓s} - L` are Fourier integrals of the rotated commutator
`R^{1/2} L R^{-1/2} - R^{-1/2} L R^{1/2}` against the densities `q_±`, with
`|q_±| ≤ m_{1/4}/√2`. Combined with Cauchy--Schwarz this bounds
`‖(R^{±s} L R^{∓s} - L) x‖²` by the Fourier average of the squared norms of the summands
of the rotated commutator (`06-transport.tex`, lines 658--729 of the area-law paper,
Proposition 7.4). The file also records the Schwarz inequality for unital 2-positive maps
in vector form and the block structure of `M^{-iu}` used by the auxiliary-block argument
in `QICLean.Analysis.Transport.EnergyBlock`.

## Main results

* `Matrix.Transport.integral_qDensity_mul_inner` — the Fourier form of the error operators.
* `Matrix.Transport.re_star_mulVec_dotProduct_le_of_twoPositive` — `‖Ψ(K) y‖² ≤ ⟨y, Ψ(K^*K) y⟩`.
* `Matrix.Transport.nsq_conj_sub_le` — the generic transported-square bound.
* `Matrix.Transport.imagPow_fromBlocks_diag` — `M^{-iu}` acts blockwise.

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open MeasureTheory

namespace Matrix.Transport

variable {n : Type*} [Fintype n]

/-- Moving matrices across the Euclidean pairing:
`⟨X v, Y w⟩ = ⟨v, X^* Y w⟩`. -/
theorem star_mulVec_dotProduct_mulVec (X Y : Matrix n n ℂ) (v w : n → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (Y *ᵥ w) = star v ⬝ᵥ ((Xᴴ * Y) *ᵥ w) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-! ### Spectral form, Fourier densities and the Schwarz inequality -/

section Fourier

variable {m : Type*} [Fintype m] [DecidableEq m] {R : Matrix m m ℂ}

/-- Conjugation `U X U^*` by the eigenvector unitary of a Hermitian matrix. -/
noncomputable def eigConj (hR : R.IsHermitian) (X : Matrix m m ℂ) : Matrix m m ℂ :=
  (hR.eigenvectorUnitary : Matrix m m ℂ) * X * star (hR.eigenvectorUnitary : Matrix m m ℂ)

theorem star_eigU_mul_eigU (hR : R.IsHermitian) :
    star (hR.eigenvectorUnitary : Matrix m m ℂ) * (hR.eigenvectorUnitary : Matrix m m ℂ) = 1 :=
  Unitary.coe_star_mul_self _

theorem eigU_mul_star_eigU (hR : R.IsHermitian) :
    (hR.eigenvectorUnitary : Matrix m m ℂ) * star (hR.eigenvectorUnitary : Matrix m m ℂ) = 1 :=
  Unitary.coe_mul_star_self _

theorem eigConj_mul_eigConj (hR : R.IsHermitian) (X Y : Matrix m m ℂ) :
    eigConj hR X * eigConj hR Y = eigConj hR (X * Y) := by
  simp only [eigConj]
  calc _ = (hR.eigenvectorUnitary : Matrix m m ℂ) * X *
        (star (hR.eigenvectorUnitary : Matrix m m ℂ) * (hR.eigenvectorUnitary : Matrix m m ℂ)) *
        Y * star (hR.eigenvectorUnitary : Matrix m m ℂ) := by noncomm_ring
    _ = _ := by rw [star_eigU_mul_eigU, Matrix.mul_one, Matrix.mul_assoc _ X Y]

theorem eigConj_unconj (hR : R.IsHermitian) (X : Matrix m m ℂ) :
    eigConj hR (star (hR.eigenvectorUnitary : Matrix m m ℂ) * X *
      (hR.eigenvectorUnitary : Matrix m m ℂ)) = X := by
  simp only [eigConj]
  calc _ = ((hR.eigenvectorUnitary : Matrix m m ℂ) * star (hR.eigenvectorUnitary : Matrix m m ℂ)) *
        X * ((hR.eigenvectorUnitary : Matrix m m ℂ) *
          star (hR.eigenvectorUnitary : Matrix m m ℂ)) := by noncomm_ring
    _ = X := by rw [eigU_mul_star_eigU, Matrix.one_mul, Matrix.mul_one]

theorem conjTranspose_eigConj (hR : R.IsHermitian) (X : Matrix m m ℂ) :
    (eigConj hR X)ᴴ = eigConj hR Xᴴ := by
  simp only [eigConj, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem cfc_eq_eigConj (hR : R.IsHermitian) (f : ℝ → ℝ) :
    cfc f R = eigConj hR (diagonal fun a => (f (hR.eigenvalues a) : ℂ)) := by
  rw [hR.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

theorem rpow_eq_eigConj (hR : R.PosDef) (r : ℝ) :
    R ^ r = eigConj hR.isHermitian
      (diagonal fun a => (Real.exp (r * Real.log (hR.isHermitian.eigenvalues a)) : ℂ)) := by
  rw [CFC.rpow_eq_cfc_real hR.posSemidef.nonneg, cfc_eq_eigConj hR.isHermitian]
  congr 2; funext a
  rw [Real.rpow_def_of_pos (hR.eigenvalues_pos a), mul_comm]

theorem imagPow_eq_eigConj (hR : R.PosDef) (u : ℝ) :
    imagPow R u = eigConj hR.isHermitian
      (diagonal fun a => Complex.exp (-(u : ℂ) * Complex.I *
        (Real.log (hR.isHermitian.eigenvalues a) : ℂ))) := by
  have hU : IsUnit (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    (Unitary.isUnit_coe (U := hR.isHermitian.eigenvectorUnitary))
  have hinv : (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)⁻¹ =
      star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    Matrix.inv_eq_left_inv (star_eigU_mul_eigU hR.isHermitian)
  unfold imagPow hermitianUnitaryPath
  set U := (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)
  have harg : (-u) • (Complex.I • eigConj hR.isHermitian
      (diagonal fun a => ((Real.log (hR.isHermitian.eigenvalues a) : ℝ) : ℂ))) =
      U * diagonal (fun a => -(u : ℂ) * Complex.I *
        (Real.log (hR.isHermitian.eigenvalues a) : ℂ)) * U⁻¹ := by
    rw [hinv, ← Complex.coe_smul, smul_smul, eigConj, ← smul_mul_assoc, ← mul_smul_comm]
    congr 2
    ext i j
    by_cases h : i = j <;> simp [h, diagonal]
  rw [CFC.log, cfc_eq_eigConj hR.isHermitian, harg, Matrix.exp_conj _ _ hU, Matrix.exp_diagonal,
    Pi.exp_def, hinv, eigConj]
  simp only [← Complex.exp_eq_exp_ℂ]
  rfl

/-! ### The Fourier densities `q_±` -/

/-- The exponent `±1/4` of the error vectors `E_±`. -/
noncomputable abbrev signExp (sign : Bool) : ℝ := if sign then 1 / 4 else -(1 / 4)

/-- The Fourier densities `q_+(u) = m_{1/8}(u + i/8)` and `q_-(u) = -m_{1/8}(u - i/8)`
(`06-transport.tex`, display `transport:q-density`). -/
noncomputable def qDensity (sign : Bool) (u : ℝ) : ℂ :=
  if sign then Complex.sinhRatioDensity ((1 / 4 : ℝ) / 2) (u + ((1 / 4 : ℝ) / 2 : ℝ) * Complex.I)
  else -Complex.sinhRatioDensity ((1 / 4 : ℝ) / 2) (u + (-((1 / 4 : ℝ) / 2) : ℝ) * Complex.I)

theorem norm_qDensity_le (sign : Bool) (u : ℝ) :
    ‖qDensity sign u‖ ≤ fourierWeight u / √2 := by
  cases sign
  · have h := Complex.norm_sinhRatioDensity_shift_le u (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
    simp only [qDensity, Bool.false_eq_true, ↓reduceIte, norm_neg]
    convert h using 3 <;> push_cast <;> ring
  · have h := Complex.norm_sinhRatioDensity_shift_le u (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
    simp only [qDensity, ↓reduceIte]
    convert h using 3 <;> push_cast <;> ring

theorem continuous_qDensity (sign : Bool) : Continuous (qDensity sign) := by
  have hs : (1 / 4 : ℝ) ∈ Set.Ioo 0 (1 / 2) := by norm_num
  have key : ∀ τ : ℝ, |τ| ≤ (1 / 4 : ℝ) / 2 →
      Continuous fun u : ℝ => Complex.sinhRatioDensity ((1 / 4 : ℝ) / 2) (u + τ * Complex.I) := by
    intro τ hσ
    refine continuous_const.div ((Complex.differentiable_densityDenom _).continuous.comp
      (by fun_prop)) fun u => ?_
    exact Complex.densityDenom_half_ne_zero hs (by simpa using hσ)
  cases sign
  · exact (key _ (by rw [abs_neg, abs_of_pos (by norm_num)])).neg
  · exact key _ (by rw [abs_of_pos (by norm_num)])

theorem integrable_fourierWeight : Integrable fourierWeight :=
  Real.integrable_sinhRatioDensity (by norm_num)

theorem integral_fourierWeight : ∫ u, fourierWeight u = 1 / 2 := by
  rw [Real.integral_sinhRatioDensity (by norm_num)]; norm_num

theorem integrable_qDensity (sign : Bool) : Integrable (qDensity sign) :=
  (integrable_fourierWeight.div_const √2).mono' (continuous_qDensity sign).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_qDensity_le sign))

theorem integral_norm_qDensity_le (sign : Bool) :
    ∫ u, ‖qDensity sign u‖ ≤ 1 / 2 / √2 := by
  calc ∫ u, ‖qDensity sign u‖ ≤ ∫ u, fourierWeight u / √2 :=
        integral_mono (integrable_qDensity sign).norm (integrable_fourierWeight.div_const _)
          (norm_qDensity_le sign)
    _ = 1 / 2 / √2 := by rw [integral_div, integral_fourierWeight]

/-- The Fourier multiplier of `q_±` against the hyperbolic factor:
`(∫ q_±(u) e^{iuz} du) (e^{z/2} - e^{-z/2}) = e^{±z/4} - 1` (`06-transport.tex`,
displays `transport:h-def` and `transport:q-density`). -/
theorem integral_qDensity_mul_cexp_mul (sign : Bool) (z : ℝ) :
    (∫ u, qDensity sign u * Complex.exp (Complex.I * u * z)) *
        ((Real.exp (z / 2) : ℂ) - (Real.exp (-(z / 2)) : ℂ)) =
      (Real.exp (signExp sign * z) : ℂ) - 1 := by
  have hs : (1 / 4 : ℝ) ∈ Set.Ioo 0 (1 / 2) := by norm_num
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hsinh : (Real.exp (z / 2) : ℂ) - (Real.exp (-(z / 2)) : ℂ) =
      ((2 * Real.sinh (z / 2) : ℝ) : ℂ) := by
    rw [Real.sinh_eq]; push_cast; ring
  have hsh : Real.sinh (z / 2) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; intro h; exact hz (by linarith)
  simp_rw [mul_comm (qDensity sign _)]
  cases sign
  · have h := Complex.integral_exp_mul_qMinus_of_ne_zero hs hz
    simp only [qDensity, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [h, hsinh, ← Complex.ofReal_mul, div_mul_cancel₀ _ (by positivity)]
    push_cast; simp only [signExp]; push_cast; ring_nf
  · have h := Complex.integral_exp_mul_qPlus_of_ne_zero hs hz
    simp only [qDensity, ↓reduceIte] at h ⊢
    rw [h, hsinh, ← Complex.ofReal_mul, div_mul_cancel₀ _ (by positivity)]
    push_cast; simp only [signExp]; push_cast; ring_nf

theorem eigConj_sub (hR : R.IsHermitian) (X Y : Matrix m m ℂ) :
    eigConj hR (X - Y) = eigConj hR X - eigConj hR Y := by
  simp only [eigConj, Matrix.mul_sub, Matrix.sub_mul]

theorem star_dotProduct_eigConj_mulVec (hR : R.IsHermitian) (Z : Matrix m m ℂ) (x y : m → ℂ) :
    star y ⬝ᵥ (eigConj hR Z *ᵥ x) =
      ∑ a, ∑ b, star ((star (hR.eigenvectorUnitary : Matrix m m ℂ) *ᵥ y) a) * Z a b *
        (star (hR.eigenvectorUnitary : Matrix m m ℂ) *ᵥ x) b := by
  set U := (hR.eigenvectorUnitary : Matrix m m ℂ)
  have h := star_mulVec_dotProduct_mulVec (star U) Z y (star U *ᵥ x)
  rw [star_eq_conjTranspose U, conjTranspose_conjTranspose, ← star_eq_conjTranspose U] at h
  rw [eigConj, ← mulVec_mulVec, ← h]
  generalize star U *ᵥ x = x'
  generalize star U *ᵥ y = y'
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `q_±` times a bounded continuous function is integrable. -/
theorem integrable_qDensity_mul {f : ℝ → ℂ} (sign : Bool) (hf : Continuous f) {C : ℝ}
    (hC : ∀ u, ‖f u‖ ≤ C) : Integrable fun u => qDensity sign u * f u :=
  (integrable_qDensity sign).mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem integrable_qDensity_mul_cexp (sign : Bool) (z : ℝ) (k : ℂ) :
    Integrable fun u : ℝ => qDensity sign u * (Complex.exp (Complex.I * u * z) * k) :=
  integrable_qDensity_mul sign (by fun_prop) (C := ‖k‖) fun u => by
    rw [norm_mul, show Complex.I * u * z = ((u * z : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **Fourier form of the error operators** (`06-transport.tex`, displays `transport:E-def`
and the Fourier formula following it, lines 688--700): for positive definite `R`,
`⟨y, (R^{±s} L R^{∓s} - L) x⟩ = ∫ q_±(u) ⟨R^{-iu} y, (R^{1/2} L R^{-1/2} - R^{-1/2} L R^{1/2})
R^{-iu} x⟩ du` with `s = 1/4`. -/
theorem integral_qDensity_mul_inner (hR : R.PosDef) (L : Matrix m m ℂ) (sign : Bool)
    (x y : m → ℂ) :
    ∫ u, qDensity sign u * (star (imagPow R u *ᵥ y) ⬝ᵥ
      ((R ^ (1 / 2 : ℝ) * L * R ^ (-(1 / 2) : ℝ) - R ^ (-(1 / 2) : ℝ) * L * R ^ (1 / 2 : ℝ)) *ᵥ
        (imagPow R u *ᵥ x))) =
      star y ⬝ᵥ ((R ^ signExp sign * L * R ^ (-signExp sign) - L) *ᵥ x) := by
  set hH := hR.isHermitian
  set U := (hH.eigenvectorUnitary : Matrix m m ℂ)
  set ℓ : m → ℝ := fun a => Real.log (hH.eigenvalues a)
  set ex : ℝ → m → ℂ := fun r a => (Real.exp (r * ℓ a) : ℂ)
  set L' := star U * L * U
  have hL : L = eigConj hH L' := (eigConj_unconj hH L).symm
  have hpow : ∀ r : ℝ, R ^ r = eigConj hH (diagonal (ex r)) := rpow_eq_eigConj hR
  set ph : ℝ → m → ℂ := fun u a => Complex.exp (-(u : ℂ) * Complex.I * (ℓ a : ℂ))
  have hW : ∀ u, imagPow R u = eigConj hH (diagonal (ph u)) := imagPow_eq_eigConj hR
  set c : m → m → ℂ := fun a b => star ((star U *ᵥ y) a) * L' a b * (star U *ᵥ x) b
  -- the integrand in the eigenbasis
  have hint : ∀ u, star (imagPow R u *ᵥ y) ⬝ᵥ
      ((R ^ (1 / 2 : ℝ) * L * R ^ (-(1 / 2) : ℝ) - R ^ (-(1 / 2) : ℝ) * L * R ^ (1 / 2 : ℝ)) *ᵥ
        (imagPow R u *ᵥ x)) = ∑ a, ∑ b, Complex.exp (Complex.I * u * ((ℓ a - ℓ b : ℝ) : ℂ)) *
          ((ex (1 / 2) a * ex (-(1 / 2)) b - ex (-(1 / 2)) a * ex (1 / 2) b) * c a b) := by
    intro u
    rw [star_mulVec_dotProduct_mulVec, mulVec_mulVec, hW, hpow, hpow, hL, conjTranspose_eigConj,
      eigConj_mul_eigConj, eigConj_mul_eigConj, eigConj_mul_eigConj, eigConj_mul_eigConj,
      ← eigConj_sub, eigConj_mul_eigConj, eigConj_mul_eigConj, star_dotProduct_eigConj_mulVec]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hph : star (ph u a) * ph u b = Complex.exp (Complex.I * u * ((ℓ a - ℓ b : ℝ) : ℂ)) := by
      simp only [ph, ← Complex.exp_conj, Complex.star_def, map_mul, map_neg, Complex.conj_ofReal,
        Complex.conj_I, ← Complex.exp_add]
      congr 1; push_cast; ring
    simp only [diagonal_conjTranspose, sub_apply, diagonal_mul, mul_diagonal, Pi.star_apply, c]
    calc _ = (star (ph u a) * ph u b) * ((ex (1 / 2) a * ex (-(1 / 2)) b -
          ex (-(1 / 2)) a * ex (1 / 2) b) * (star ((star U *ᵥ y) a) * L' a b *
            (star U *ᵥ x) b)) := by ring
      _ = _ := by rw [hph]
  simp_rw [hint]
  rw [hpow, hpow, hL, eigConj_mul_eigConj, eigConj_mul_eigConj, ← eigConj_sub,
    star_dotProduct_eigConj_mulVec]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun a _ => ?_]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => integrable_qDensity_mul_cexp sign _ _]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h := integral_qDensity_mul_cexp_mul sign (ℓ a - ℓ b)
    simp_rw [← mul_assoc]
    rw [integral_mul_const, integral_mul_const]
    simp only [sub_apply, diagonal_mul, mul_diagonal, c, ex]
    have e1 : ((Real.exp (1 / 2 * ℓ a) : ℂ) * (Real.exp (-(1 / 2) * ℓ b) : ℂ) -
        (Real.exp (-(1 / 2) * ℓ a) : ℂ) * (Real.exp (1 / 2 * ℓ b) : ℂ)) =
        (Real.exp ((ℓ a - ℓ b) / 2) : ℂ) - (Real.exp (-((ℓ a - ℓ b) / 2)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      congr 3 <;> ring
    have e2 : (Real.exp (signExp sign * ℓ a) : ℂ) * (Real.exp (-signExp sign * ℓ b) : ℂ) =
        (Real.exp (signExp sign * (ℓ a - ℓ b)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [e1, h]
    calc _ = star ((star U *ᵥ y) a) * ((Real.exp (signExp sign * (ℓ a - ℓ b)) : ℂ) * L' a b -
          L' a b) * (star U *ᵥ x) b := by ring
      _ = _ := by rw [← e2]; ring
  · exact integrable_finsetSum _ fun b _ => integrable_qDensity_mul_cexp sign _ _

/-- **Schwarz inequality for a unital 2-positive map** (`06-transport.tex`, display
`transport:cp-schwarz`, lines 712--722): `‖Ψ(K) y‖² ≤ ⟨y, Ψ(K^*K) y⟩`. -/
theorem re_star_mulVec_dotProduct_le_of_twoPositive {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h2 : IsNPositiveMap 2 Φ) (h1 : Φ 1 = 1) (K : Matrix m m ℂ) (y : m → ℂ) :
    (star (Φ K *ᵥ y) ⬝ᵥ (Φ K *ᵥ y)).re ≤ (star y ⬝ᵥ (Φ (Kᴴ * K) *ᵥ y)).re := by
  have hpos : IsPositiveMap Φ := Is2PositiveMap.isPositiveMap h2
  have h := SchwarzTwoVariable.schwarz_two_variable Φ h2 K 1 y (Φ K *ᵥ y)
    (by simp [h1])
  rw [Matrix.mul_one, hpos.map_conjTranspose] at h
  rw [star_mulVec, ← dotProduct_mulVec]
  exact (Complex.le_def.mp h).1

end Fourier

/-! ### The transported square -/

section TransportedSquare

variable {m : Type*} [Fintype m] [DecidableEq m] {R : Matrix m m ℂ}

/-- The pairing `⟨R^{-iu} y, Z R^{-iu} x⟩` in the eigenbasis of `R`: a finite sum of
characters `e^{iu(ℓ_a - ℓ_b)}`. -/
theorem inner_imagPow_eq_sum (hR : R.PosDef) (Z : Matrix m m ℂ) (x y : m → ℂ) (u : ℝ) :
    star (imagPow R u *ᵥ y) ⬝ᵥ (Z *ᵥ (imagPow R u *ᵥ x)) =
      ∑ a, ∑ b, Complex.exp (Complex.I * u *
        ((Real.log (hR.isHermitian.eigenvalues a) - Real.log (hR.isHermitian.eigenvalues b) : ℝ) :
          ℂ)) *
        (star ((star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *ᵥ y) a) *
          (star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) * Z *
            (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)) a b *
          (star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *ᵥ x) b) := by
  set hH := hR.isHermitian
  set U := (hH.eigenvectorUnitary : Matrix m m ℂ)
  set ℓ : m → ℝ := fun a => Real.log (hH.eigenvalues a)
  set ph : ℝ → m → ℂ := fun u a => Complex.exp (-(u : ℂ) * Complex.I * (ℓ a : ℂ))
  have hZ : Z = eigConj hH (star U * Z * U) := (eigConj_unconj hH Z).symm
  rw [star_mulVec_dotProduct_mulVec, mulVec_mulVec, imagPow_eq_eigConj hR, hZ,
    conjTranspose_eigConj, eigConj_mul_eigConj, eigConj_mul_eigConj,
    star_dotProduct_eigConj_mulVec, ← hZ]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hph : star (ph u a) * ph u b = Complex.exp (Complex.I * u * ((ℓ a - ℓ b : ℝ) : ℂ)) := by
    simp only [ph, ← Complex.exp_conj, Complex.star_def, map_mul, map_neg, Complex.conj_ofReal,
      Complex.conj_I, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp only [diagonal_conjTranspose, diagonal_mul, mul_diagonal, Pi.star_apply]
  calc _ = (star (ph u a) * ph u b) * (star ((star U *ᵥ y) a) * (star U * Z * U) a b *
        (star U *ᵥ x) b) := by ring
    _ = _ := by rw [hph]

theorem continuous_inner_imagPow (hR : R.PosDef) (Z : Matrix m m ℂ) (x y : m → ℂ) :
    Continuous fun u : ℝ => star (imagPow R u *ᵥ y) ⬝ᵥ (Z *ᵥ (imagPow R u *ᵥ x)) := by
  simp_rw [inner_imagPow_eq_sum hR]
  fun_prop

theorem norm_inner_imagPow_le (hR : R.PosDef) (Z : Matrix m m ℂ) (x y : m → ℂ) :
    ∃ C, ∀ u : ℝ, ‖star (imagPow R u *ᵥ y) ⬝ᵥ (Z *ᵥ (imagPow R u *ᵥ x))‖ ≤ C := by
  refine ⟨∑ a, ∑ b, ‖star ((star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *ᵥ y) a) *
          (star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) * Z *
            (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)) a b *
          (star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *ᵥ x) b‖, fun u => ?_⟩
  rw [inner_imagPow_eq_sum hR]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun b _ => ?_))
  rw [norm_mul, show Complex.I * (u : ℂ) * _ = ((u * (Real.log (hR.isHermitian.eigenvalues a) -
    Real.log (hR.isHermitian.eigenvalues b)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

theorem conjTranspose_imagPow_mul_self (hR : R.PosDef) (u : ℝ) :
    (imagPow R u)ᴴ * imagPow R u = 1 := by
  rw [imagPow_eq_eigConj hR, conjTranspose_eigConj, eigConj_mul_eigConj, diagonal_conjTranspose,
    diagonal_mul_diagonal]
  have : (fun a => star (Complex.exp (-(u : ℂ) * Complex.I *
      (Real.log (hR.isHermitian.eigenvalues a) : ℂ))) * Complex.exp (-(u : ℂ) * Complex.I *
      (Real.log (hR.isHermitian.eigenvalues a) : ℂ))) = fun _ => 1 := by
    funext a
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    rw [← Complex.exp_zero]; congr 1; ring
  simp only [Pi.star_apply] at this ⊢
  rw [this, diagonal_one, eigConj, Matrix.mul_one, eigU_mul_star_eigU]

theorem nsq_imagPow_mulVec (hR : R.PosDef) (u : ℝ) (y : m → ℂ) :
    star (imagPow R u *ᵥ y) ⬝ᵥ (imagPow R u *ᵥ y) = star y ⬝ᵥ y := by
  rw [star_mulVec_dotProduct_mulVec, conjTranspose_imagPow_mul_self hR, one_mulVec]

omit [Fintype m] [DecidableEq m] in
theorem nsq_nonneg' [Fintype m] (y : m → ℂ) : 0 ≤ (star y ⬝ᵥ y).re := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (y i).re, sq_nonneg (y i).im]

omit [DecidableEq m] in
/-- `Re(q ⟨p, g⟩) ≤ |q| (c/2 ‖p‖² + ‖g‖²/(2c))` for `c > 0`. -/
theorem re_mul_dotProduct_le (q : ℂ) (p g : m → ℂ) {c : ℝ} (hc : 0 < c) :
    (q * (star p ⬝ᵥ g)).re ≤
      ‖q‖ * (c / 2 * (star p ⬝ᵥ p).re + 1 / (2 * c) * (star g ⬝ᵥ g).re) := by
  simp only [dotProduct, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hpp : (star (p i) * p i).re = ‖p i‖ ^ 2 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]; rfl
  have hgg : (star (g i) * g i).re = ‖g i‖ ^ 2 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]; rfl
  rw [hpp, hgg]
  calc (q * (star (p i) * g i)).re ≤ ‖q * (star (p i) * g i)‖ := Complex.re_le_norm _
    _ = ‖q‖ * (‖p i‖ * ‖g i‖) := by rw [norm_mul, norm_mul, norm_star]
    _ ≤ _ := by
      gcongr
      have key : c / 2 * ‖p i‖ ^ 2 + 1 / (2 * c) * ‖g i‖ ^ 2 - ‖p i‖ * ‖g i‖ =
          (c * ‖p i‖ - ‖g i‖) ^ 2 / (2 * c) := by field_simp; ring
      nlinarith [key, div_nonneg (sq_nonneg (c * ‖p i‖ - ‖g i‖)) (by positivity : (0 : ℝ) ≤ 2 * c)]

/-- The closing scalar step of the transported-square estimate. -/
theorem le_of_forall_pos_le_aux {N A W S' : ℝ} (hN : 0 ≤ N) (hA0 : 0 ≤ A)
    (hA : A ≤ 1 / 2 / √2) (hW : 0 ≤ W) (hS0 : 0 ≤ S')
    (h : ∀ c : ℝ, 0 < c → N ≤ c / 2 * N * (A * W) + 1 / (2 * c) * (S' / √2)) :
    N ≤ 1 / 4 * W * S' := by
  have hs2 : (0 : ℝ) < √2 := by positivity
  have ha : 0 ≤ S' / √2 := by positivity
  set P := A * W with hPdef
  rcases eq_or_lt_of_le (mul_nonneg hA0 hW : 0 ≤ P) with hAW | hAW
  · have hN0 : N ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have := h ((S' / √2 + 1) / N) (by positivity)
      rw [hPdef, ← hAW, mul_zero, zero_add] at this
      have e : 1 / (2 * ((S' / √2 + 1) / N)) * (S' / √2) =
          N * (S' / √2) / (2 * (S' / √2 + 1)) := by field_simp
      rw [e, le_div_iff₀ (by positivity)] at this
      nlinarith
    nlinarith
  · have hP0 : P ≠ 0 := hAW.ne'
    have := h (1 / P) (by positivity)
    have e1 : 1 / P / 2 * N * P = N / 2 := by field_simp
    have e2 : 1 / (2 * (1 / P)) * (S' / √2) = P * S' / (2 * √2) := by field_simp
    rw [e1, e2] at this
    have hNle : N ≤ P * S' / √2 := by
      have h2 : P * S' / (2 * √2) * 2 = P * S' / √2 := by field_simp
      linarith
    calc N ≤ P * S' / √2 := hNle
      _ ≤ 1 / 2 / √2 * W * S' / √2 := by
        gcongr
        calc P = A * W := rfl
          _ ≤ 1 / 2 / √2 * W := by gcongr
      _ = 1 / 4 * W * S' := by
        field_simp; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring

/-- **The transported square, generic form** (`06-transport.tex` lines 688--729): if
`R^{1/2} L R^{-1/2} - R^{-1/2} L R^{1/2} = ∑_{j∈S} w_j G_j` with `w_j ≥ 0` and
`‖G_j R^{-iu} x‖² ≤ t_j(u)`, then
`‖(R^{±s} L R^{∓s} - L) x‖² ≤ (1/4) W ∑_{j∈S} w_j ∫ m_s(u) t_j(u) du`, `W = ∑_{j∈S} w_j`.
The factor `W` comes from Cauchy--Schwarz over the positive measure `w_j |q_±(u)| du`. -/
theorem nsq_conj_sub_le {J : Type*} (hR : R.PosDef) (L : Matrix m m ℂ) (sign : Bool)
    (S : Finset J) {w : J → ℝ} (hw : ∀ j, 0 ≤ w j) (G : J → Matrix m m ℂ)
    (hG : R ^ (1 / 2 : ℝ) * L * R ^ (-(1 / 2) : ℝ) - R ^ (-(1 / 2) : ℝ) * L * R ^ (1 / 2 : ℝ) =
      ∑ j ∈ S, w j • G j)
    (x : m → ℂ) (t : J → ℝ → ℝ)
    (ht : ∀ j u, (star (G j *ᵥ (imagPow R u *ᵥ x)) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x))).re ≤ t j u)
    (htc : ∀ j, Continuous (t j)) (htb : ∀ j, ∃ C, ∀ u, ‖t j u‖ ≤ C) :
    (star ((R ^ signExp sign * L * R ^ (-signExp sign) - L) *ᵥ x) ⬝ᵥ
        ((R ^ signExp sign * L * R ^ (-signExp sign) - L) *ᵥ x)).re ≤
      1 / 4 * (∑ j ∈ S, w j) * ∑ j ∈ S, w j * ∫ u, fourierWeight u * t j u := by
  set F := R ^ signExp sign * L * R ^ (-signExp sign) - L
  set y := F *ᵥ x
  set N := (star y ⬝ᵥ y).re
  set A := ∫ u, ‖qDensity sign u‖
  have ht0 : ∀ j u, 0 ≤ t j u := fun j u => (nsq_nonneg' _).trans (ht j u)
  have hint_t : ∀ j, Integrable fun u => fourierWeight u * t j u := fun j =>
    integrable_fourierWeight.mul_bdd (htc j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => (htb j).choose_spec u)
  have hint_qt : ∀ j, Integrable fun u => ‖qDensity sign u‖ * t j u := fun j =>
    (integrable_qDensity sign).norm.mul_bdd (htc j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => (htb j).choose_spec u)
  have hf : ∀ j, Integrable fun u => qDensity sign u *
      (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x))) := fun j =>
    integrable_qDensity_mul sign (continuous_inner_imagPow hR _ _ _)
      (norm_inner_imagPow_le hR (G j) x y).choose_spec
  -- Fourier form and the block decomposition
  have hfour := integral_qDensity_mul_inner hR L sign x y
  rw [hG] at hfour
  simp_rw [sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, Finset.mul_sum,
    mul_smul_comm] at hfour
  have hfs : ∀ j ∈ S, Integrable fun u => w j • (qDensity sign u *
      (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))) := fun j _ => (hf j).smul (w j)
  rw [integral_finsetSum _ hfs] at hfour
  simp_rw [integral_smul] at hfour
  -- the bound for each `c > 0`
  have hmain : ∀ c : ℝ, 0 < c → N ≤ c / 2 * N * (A * ∑ j ∈ S, w j) +
      1 / (2 * c) * ((∑ j ∈ S, w j * ∫ u, fourierWeight u * t j u) / √2) := by
    intro c hc
    have hN : N = ∑ j ∈ S, w j * (∫ u, qDensity sign u *
        (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))).re := by
      have := congrArg Complex.re hfour
      simp only [Complex.re_sum, Complex.real_smul, Complex.re_ofReal_mul] at this
      exact this.symm
    have hj : ∀ j, (∫ u, qDensity sign u *
        (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))).re ≤
        c / 2 * N * A + 1 / (2 * c) * ((∫ u, fourierWeight u * t j u) / √2) := by
      intro j
      have hre := integral_re (hf j)
      simp only [RCLike.re_to_complex] at hre
      rw [← hre]
      calc ∫ u, (qDensity sign u *
            (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))).re
          ≤ ∫ u, (c / 2 * N * ‖qDensity sign u‖ + 1 / (2 * c) * (‖qDensity sign u‖ * t j u)) := by
            refine integral_mono (by simpa using (hf j).re)
              (((integrable_qDensity sign).norm.const_mul _).add
              ((hint_qt j).const_mul _)) fun u => ?_
            have h1 := re_mul_dotProduct_le (qDensity sign u) (imagPow R u *ᵥ y)
              (G j *ᵥ (imagPow R u *ᵥ x)) hc
            rw [nsq_imagPow_mulVec hR] at h1
            have h2 := mul_le_mul_of_nonneg_left (ht j u) (norm_nonneg (qDensity sign u))
            have hNy : (star y ⬝ᵥ y).re = N := rfl
            rw [hNy] at h1
            have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (2 * c))
            nlinarith [h1, h3]
        _ = c / 2 * N * A + 1 / (2 * c) * ∫ u, ‖qDensity sign u‖ * t j u := by
            rw [integral_add ((integrable_qDensity sign).norm.const_mul _)
              ((hint_qt j).const_mul _), integral_const_mul, integral_const_mul]
        _ ≤ _ := by
            gcongr
            calc ∫ u, ‖qDensity sign u‖ * t j u ≤ ∫ u, fourierWeight u / √2 * t j u :=
                  integral_mono (hint_qt j) ((hint_t j).div_const √2 |>.congr
                    (Filter.Eventually.of_forall fun u => by ring)) fun u =>
                    mul_le_mul_of_nonneg_right (norm_qDensity_le sign u) (ht0 j u)
              _ = (∫ u, fourierWeight u * t j u) / √2 := by
                  rw [← integral_div]; congr 1; funext u; ring
    have hsum : ∑ j ∈ S, w j * (∫ u, qDensity sign u *
          (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))).re ≤
        ∑ j ∈ S, w j * (c / 2 * N * A + 1 / (2 * c) * ((∫ u, fourierWeight u * t j u) / √2)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj j) (hw j)
    have heq : ∑ j ∈ S, w j * (c / 2 * N * A + 1 / (2 * c) *
          ((∫ u, fourierWeight u * t j u) / √2)) = c / 2 * N * (A * ∑ j ∈ S, w j) +
        1 / (2 * c) * ((∑ j ∈ S, w j * ∫ u, fourierWeight u * t j u) / √2) := by
      conv_rhs => simp only [Finset.mul_sum, Finset.sum_div]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  exact le_of_forall_pos_le_aux (nsq_nonneg' y) (integral_nonneg fun u => norm_nonneg _)
    (integral_norm_qDensity_le sign) (Finset.sum_nonneg fun j _ => hw j)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hw j)
      (integral_nonneg fun u => mul_nonneg (Real.sinhRatioDensity_pos (by norm_num) u).le
        (ht0 j u))) hmain

end TransportedSquare

/-! ### The doubled space -/

section Doubled

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [Fintype m] [DecidableEq m] in
theorem fromBlocks_sub' (A₁ B₁ C₁ D₁ A₂ B₂ C₂ D₂ : Matrix m m ℂ) :
    fromBlocks A₁ B₁ C₁ D₁ - fromBlocks A₂ B₂ C₂ D₂ =
      fromBlocks (A₁ - A₂) (B₁ - B₂) (C₁ - C₂) (D₁ - D₂) := by
  simp only [sub_eq_add_neg, fromBlocks_neg, fromBlocks_add]

/-- `M^{-iu}` through the real functional calculus: `cos(u log M) - i sin(u log M)`. -/
theorem imagPow_eq_cfc {R : Matrix m m ℂ} (hR : R.PosDef) (u : ℝ) :
    imagPow R u = cfc (fun x => Real.cos (u * Real.log x)) R -
      Complex.I • cfc (fun x => Real.sin (u * Real.log x)) R := by
  rw [imagPow_eq_eigConj hR, cfc_eq_eigConj hR.isHermitian, cfc_eq_eigConj hR.isHermitian]
  have hd : (diagonal fun a => Complex.exp (-(u : ℂ) * Complex.I *
      (Real.log (hR.isHermitian.eigenvalues a) : ℂ))) =
      (diagonal fun a => ((Real.cos (u * Real.log (hR.isHermitian.eigenvalues a)) : ℝ) : ℂ)) -
        Complex.I •
          diagonal fun a => ((Real.sin (u * Real.log (hR.isHermitian.eigenvalues a)) : ℝ) : ℂ) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp only [diagonal_apply_eq, sub_apply, smul_apply, smul_eq_mul]
      rw [show -(u : ℂ) * Complex.I * (Real.log (hR.isHermitian.eigenvalues a) : ℂ) =
        ((-(u * Real.log (hR.isHermitian.eigenvalues a)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_neg, Complex.sin_neg]; ring
    · simp [diagonal_apply_ne _ hab]
  rw [hd, eigConj_sub]
  simp only [eigConj, Matrix.mul_smul, Matrix.smul_mul]

/-- `M^{-iu}` of a block-diagonal positive definite matrix acts blockwise. -/
theorem imagPow_fromBlocks_diag {X Y : Matrix m m ℂ} (hX : X.PosDef) (hY : Y.PosDef) (u : ℝ) :
    imagPow (fromBlocks X 0 0 Y) u = fromBlocks (imagPow X u) 0 0 (imagPow Y u) := by
  rw [imagPow_eq_cfc (hX.fromBlocks_diag hY), imagPow_eq_cfc hX, imagPow_eq_cfc hY,
    cfc_fromBlocks_diag hX.isHermitian hY.isHermitian,
    cfc_fromBlocks_diag hX.isHermitian hY.isHermitian, fromBlocks_smul, fromBlocks_sub']
  simp

omit [DecidableEq m] in
theorem star_sumElim_zero_dotProduct (w : m → ℂ) (Z : Matrix (m ⊕ m) (m ⊕ m) ℂ) :
    star (Sum.elim w 0) ⬝ᵥ (Z *ᵥ Sum.elim w 0) = star w ⬝ᵥ (Z.toBlocks₁₁ *ᵥ w) := by
  conv_lhs => rw [← fromBlocks_toBlocks Z]
  rw [fromBlocks_mulVec, Function.star_sumElim, sumElim_dotProduct_sumElim]
  simp

end Doubled

end Matrix.Transport
