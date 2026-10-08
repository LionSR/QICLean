/-
Released under Apache 2.0 license as described in the file LICENSE.
Assisted-by: OpenAI Codex (GPT-6).
The proofs in this file are new. The imported real Gaussian foundation contains
modified openai/math proof material documented in Basic.lean.
-/
import QICLean.Probability.ComplexGaussian.Basic

/-!
# Centered circular complex Gaussian covariance

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
`04-compression.tex:279–340`, equations `compression-gaussian-covariance` and
`compression-slot-variance`. The fourth-moment identity includes every pattern
of coincident indices; no distinctness assumption is imposed.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexConjugate BigOperators ENNReal

namespace QICLean.ComplexGaussian

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Complex-valued Kronecker delta. -/
def delta (a b : ι) : ℂ := if a = b then 1 else 0

omit [Fintype ι] in
@[simp] theorem conj_delta (a b : ι) : conj (delta a b) = delta a b := by
  unfold delta
  split <;> simp

omit [Fintype ι] in
theorem delta_comm (a b : ι) : delta a b = delta b a := by
  simp only [delta, eq_comm]

private theorem sqrt_two_complex_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)

private theorem sqrt_two_complex_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)

private theorem inner_coordinateVectors (a b : ι) (r s : Fin 2) :
    ⟪coordinateVectors a r, coordinateVectors b s⟫ = if a = b ∧ r = s then 1 else 0 := by
  change ⟪EuclideanSpace.basisFun (ι × Fin 2) ℝ (a, r),
    EuclideanSpace.basisFun (ι × Fin 2) ℝ (b, s)⟫ = _
  rw [OrthonormalBasis.inner_eq_ite]
  simp only [Prod.mk.injEq]

omit [DecidableEq ι] in
private theorem pairing_coordinate (a b : ι) :
    pairing (coordinateVectors a) (coordinateVectors b)
      coordinateCoefficients coordinateCoefficients = 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [pairing, Fin.sum_univ_two, inner_coordinateVectors,
      coordinateCoefficients]
    ring_nf
    simp [Complex.I_sq]
  · simp [pairing, inner_coordinateVectors,
      coordinateCoefficients, h]

private theorem pairing_coordinate_conj (a b : ι) :
    pairing (coordinateVectors a) (coordinateVectors b)
      coordinateCoefficients (fun j ↦ conj (coordinateCoefficients j)) = delta a b := by
  by_cases h : a = b
  · subst b
    simp [pairing, Fin.sum_univ_two, inner_coordinateVectors,
      coordinateCoefficients, delta]
    field_simp [sqrt_two_complex_ne_zero]
    norm_num [Complex.I_sq, sqrt_two_complex_sq]
  · simp [pairing, inner_coordinateVectors,
      coordinateCoefficients, delta, h]

private theorem pairing_conj_coordinate (a b : ι) :
    pairing (coordinateVectors a) (coordinateVectors b)
      (fun j ↦ conj (coordinateCoefficients j)) coordinateCoefficients = delta a b := by
  by_cases h : a = b
  · subst b
    simp [pairing, Fin.sum_univ_two, inner_coordinateVectors,
      coordinateCoefficients, delta]
    field_simp [sqrt_two_complex_ne_zero]
    norm_num [Complex.I_sq, sqrt_two_complex_sq]
  · simp [pairing, inner_coordinateVectors,
      coordinateCoefficients, delta, h]

/-- The normalized complex coordinates have identity covariance.
Source: `04-compression.tex:306–309`. -/
theorem integral_coordinate_mul_conj (a b : ι) :
    (∫ x, coordinate a x * conj (coordinate b x) ∂law ι) = delta a b := by
  simp_rw [conj_coordinate]
  exact (integral_linearField_mul _ _ _ _).trans (pairing_coordinate_conj a b)

omit [DecidableEq ι] in
/-- Circular coordinates have vanishing bilinear covariance. -/
theorem integral_coordinate_mul (a b : ι) :
    (∫ x, coordinate a x * coordinate b x ∂law ι) = 0 :=
  (integral_linearField_mul _ _ _ _).trans (pairing_coordinate a b)

omit [DecidableEq ι] in
theorem memLp_coordinate_mul_conj (a b : ι) :
    MemLp (fun x ↦ coordinate a x * conj (coordinate b x)) 2 (law ι) := by
  simp_rw [conj_coordinate]
  exact memLp_linearField_mul _ _ _ _

omit [DecidableEq ι] in
theorem integrable_coordinate_four (a b c d : ι) :
    Integrable (fun x ↦ (coordinate a x * conj (coordinate b x)) *
      conj (coordinate c x * conj (coordinate d x))) (law ι) := by
  have hcd : MemLp (fun x ↦ conj (coordinate c x * conj (coordinate d x))) 2
      (law ι) := by
    simp_rw [map_mul, starRingEnd_self_apply, conj_coordinate]
    exact memLp_linearField_mul _ _ _ _
  exact (memLp_coordinate_mul_conj a b).integrable_mul hcd

/-- Complex fourth pairing, including the value `2` when all indices coincide.
Source: `04-compression.tex:326–334`. -/
theorem integral_coordinate_four_eq_pairings (a b c d : ι) :
    (∫ x, (coordinate a x * conj (coordinate b x)) *
      conj (coordinate c x * conj (coordinate d x)) ∂law ι) =
    delta a b * delta c d + delta a c * delta b d := by
  simp_rw [map_mul, starRingEnd_self_apply, conj_coordinate]
  change (∫ x, linearField (coordinateVectors a) coordinateCoefficients x *
    linearField (coordinateVectors b) (fun j ↦ conj (coordinateCoefficients j)) x *
    (linearField (coordinateVectors c) (fun j ↦ conj (coordinateCoefficients j)) x *
      linearField (coordinateVectors d) coordinateCoefficients x) ∂stdGaussian (Sample ι)) = _
  rw [integral_linearField_four, pairing_coordinate_conj, pairing_conj_coordinate,
    pairing_coordinate_conj, pairing_conj_coordinate, pairing_coordinate]
  simp

omit [DecidableEq ι] in
/-- Unit second moment of a standard circular complex Gaussian. -/
theorem integral_coordinate_norm_sq (a : ι) :
    (∫ x, ‖coordinate a x‖ ^ 2 ∂law ι) = 1 := by
  classical
  have h := integral_coordinate_mul_conj a a
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal, delta, ite_true] at h
  exact_mod_cast h

omit [DecidableEq ι] in
/-- The fourth moment is `2`, including the coincident-index case needed for centering.
Source: `04-compression.tex:328–334`. -/
theorem integral_coordinate_norm_four (a : ι) :
    (∫ x, ‖coordinate a x‖ ^ 4 ∂law ι) = 2 := by
  classical
  have h := integral_coordinate_four_eq_pairings a a a a
  have he (x : Sample ι) : (coordinate a x * conj (coordinate a x)) *
      conj (coordinate a x * conj (coordinate a x)) = ((‖coordinate a x‖ ^ 4 : ℝ) : ℂ) := by
    simp only [Complex.mul_conj', map_pow, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [he] at h
  rw [integral_complex_ofReal] at h
  norm_num [delta] at h
  exact_mod_cast h

/-- The centered coefficient of a single random source. Source:
`04-compression.tex:311–324`, equation `compression-gaussian-covariance`. -/
def centered (a b : ι) (x : Sample ι) : ℂ :=
  coordinate a x * conj (coordinate b x) - delta a b

theorem memLp_centered (a b : ι) : MemLp (centered a b) 2 (law ι) :=
  (memLp_coordinate_mul_conj a b).sub (memLp_const _)

theorem integrable_centered (a b : ι) : Integrable (centered a b) (law ι) :=
  (memLp_centered a b).integrable (by norm_num)

theorem integral_centered (a b : ι) : (∫ x, centered a b x ∂law ι) = 0 := by
  unfold centered
  rw [integral_sub ((memLp_coordinate_mul_conj a b).integrable (by norm_num))
    (integrable_const _), integral_coordinate_mul_conj]
  simp

theorem memLp_conj_centered (a b : ι) :
    MemLp (fun x ↦ conj (centered a b x)) 2 (law ι) := by
  have he (x : Sample ι) : conj (centered a b x) = centered b a x := by
    simp [centered, map_sub, map_mul, delta_comm, mul_comm]
  simp_rw [he]
  exact memLp_centered b a

theorem integrable_centered_mul_conj (a b c d : ι) :
    Integrable (fun x ↦ centered a b x * conj (centered c d x)) (law ι) :=
  (memLp_centered a b).integrable_mul (memLp_conj_centered c d)

/-- The centered circular complex Gaussian covariance, with all coincident-index cases.
Source: `eq:compression-gaussian-covariance`, `04-compression.tex:320–334`. -/
theorem integral_centered_mul_conj (a b c d : ι) :
    (∫ x, centered a b x * conj (centered c d x) ∂law ι) = delta a c * delta b d := by
  have he (x : Sample ι) : centered a b x * conj (centered c d x) =
      (coordinate a x * conj (coordinate b x)) *
        conj (coordinate c x * conj (coordinate d x)) -
      delta c d * (coordinate a x * conj (coordinate b x)) -
      delta a b * (coordinate d x * conj (coordinate c x)) + delta a b * delta c d := by
    simp only [centered, map_sub, map_mul, conj_delta, starRingEnd_self_apply]
    ring
  have hab := (memLp_coordinate_mul_conj a b).integrable (by norm_num)
  have hdc := (memLp_coordinate_mul_conj d c).integrable (by norm_num)
  have h4 := integrable_coordinate_four a b c d
  simp_rw [he]
  have hs3 := integral_add ((h4.sub (hab.const_mul (delta c d))).sub
    (hdc.const_mul (delta a b))) (integrable_const (delta a b * delta c d))
  have hs2 := integral_sub (h4.sub (hab.const_mul (delta c d)))
    (hdc.const_mul (delta a b))
  have hs1 := integral_sub h4 (hab.const_mul (delta c d))
  simp only [Pi.sub_apply] at hs3 hs2 hs1
  rw [hs3, hs2, hs1]
  simp only [integral_const_mul, integral_coordinate_mul_conj,
    integral_coordinate_four_eq_pairings, integral_const, probReal_univ, one_smul]
  rw [delta_comm d c]
  ring

/-- Sample mean of centered density-source coefficients, using fresh independent Gaussian
coordinates for each sample. Source: `04-compression.tex:311–338`. -/
def sampleAverage (k : ℕ) (a b : ι) (x : Sample (Fin k × ι)) : ℂ :=
  (k : ℂ)⁻¹ * ∑ j : Fin k, centered (j, a) (j, b) x

theorem memLp_sampleAverage (k : ℕ) (a b : ι) :
    MemLp (sampleAverage k a b) 2 (law (Fin k × ι)) :=
  (memLp_finsetSum _ fun j _ ↦ memLp_centered (j, a) (j, b)).const_mul _

theorem integral_sampleAverage (k : ℕ) (a b : ι) :
    (∫ x, sampleAverage k a b x ∂law (Fin k × ι)) = 0 := by
  unfold sampleAverage
  rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦ integrable_centered _ _)]
  simp [integral_centered]

private theorem integral_cross_sample (k : ℕ) (a b c d : ι) (j l : Fin k) :
    (∫ x, centered (j, a) (j, b) x * conj (centered (l, c) (l, d) x)
      ∂law (Fin k × ι)) = if j = l then delta a c * delta b d else 0 := by
  rw [integral_centered_mul_conj]
  by_cases h : j = l
  · subst l
    simp [delta]
  · simp [delta, h]

/-- Exact `1/k` centered covariance for averaged source coefficients. No restriction on
coincidences of `a,b,c,d`, and no dimension factor. Source: `eq:compression-slot-variance`,
`04-compression.tex:311–340`. -/
theorem integral_sampleAverage_mul_conj (k : ℕ) (hk : 0 < k) (a b c d : ι) :
    (∫ x, sampleAverage k a b x * conj (sampleAverage k c d x)
      ∂law (Fin k × ι)) = (k : ℂ)⁻¹ * (delta a c * delta b d) := by
  have he (x : Sample (Fin k × ι)) : sampleAverage k a b x *
      conj (sampleAverage k c d x) =
      (k : ℂ)⁻¹ ^ 2 * ∑ j : Fin k, ∑ l : Fin k,
        centered (j, a) (j, b) x * conj (centered (l, c) (l, d) x) := by
    simp only [sampleAverage, map_mul, map_sum, map_inv₀, map_natCast]
    calc
      _ = (k : ℂ)⁻¹ ^ 2 * ((∑ j : Fin k, centered (j, a) (j, b) x) *
          ∑ l : Fin k, conj (centered (l, c) (l, d) x)) := by ring
      _ = _ := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
  have hi (j l : Fin k) := integrable_centered_mul_conj (j, a) (j, b) (l, c) (l, d)
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ ↦
    integrable_finsetSum _ fun l _ ↦ hi j l)]
  simp_rw [integral_finsetSum _ (fun l _ ↦ hi _ l), integral_cross_sample]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hk)
  field_simp [hn]

/-- Integrability of every averaged coefficient product, for matrix second-moment use. -/
theorem integrable_sampleAverage_mul_conj (k : ℕ) (a b c d : ι) :
    Integrable (fun x ↦ sampleAverage k a b x * conj (sampleAverage k c d x))
      (law (Fin k × ι)) := by
  have hconj : MemLp (fun x ↦ conj (sampleAverage k c d x)) 2 (law (Fin k × ι)) := by
    have he (x : Sample (Fin k × ι)) : conj (sampleAverage k c d x) =
        sampleAverage k d c x := by
      simp only [sampleAverage, map_mul, map_sum, map_inv₀, map_natCast]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp [centered, map_sub, map_mul, delta_comm, mul_comm]
    simp_rw [he]
    exact memLp_sampleAverage k d c
  exact (memLp_sampleAverage k a b).integrable_mul hconj

section DensityCoefficients

variable {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]

/-- Ket endpoint pair together with bra endpoint pair for a density-source entry. -/
abbrev DensityIndex (A C : Type*) := (A × A) × (C × C)

/-- Quarter-power weight of a density-source coefficient.
Source: `04-compression.tex:311–318`. -/
def coefficientWeight (lam : A → ℝ) (mu : C → ℝ) (e : DensityIndex A C) : ℝ :=
  ((lam e.1.1 * lam e.1.2) * (mu e.2.1 * mu e.2.2)) ^ (1 / 4 : ℝ)

omit [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C] in
/-- The whole-product quarter weight equals the two factors appearing in the sampled
ket/bra operators, including zero Schmidt probabilities. Source:
`eq:compression-random-source`, `04-compression.tex:294–317`. -/
theorem coefficientWeight_eq_product_quarter (lam : A → ℝ) (mu : C → ℝ)
    (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c) (e : DensityIndex A C) :
    coefficientWeight lam mu e = (lam e.1.1 * mu e.2.1) ^ (1 / 4 : ℝ) *
      (lam e.1.2 * mu e.2.2) ^ (1 / 4 : ℝ) := by
  rw [coefficientWeight, ← Real.mul_rpow (mul_nonneg (hlam _) (hmu _))
    (mul_nonneg (hlam _) (hmu _))]
  congr 1
  ring

/-- Weighted centered coefficient of the sampled source. The Gaussian coordinate index
combines one ket index and one bra index, as in `04-compression.tex:311–318`. -/
def densityCoefficient (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (e : DensityIndex A C) (x : Sample (Fin k × (A × C))) : ℂ :=
  (coefficientWeight lam mu e : ℂ) * sampleAverage k (e.1.1, e.2.1) (e.1.2, e.2.2) x

theorem memLp_densityCoefficient (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (e : DensityIndex A C) :
    MemLp (densityCoefficient k lam mu e) 2 (law (Fin k × (A × C))) :=
  (memLp_sampleAverage k (e.1.1, e.2.1) (e.1.2, e.2.2)).const_mul _

/-- The weighted random replacement is unbiased, since its correction has mean zero.
Source: `04-compression.tex:306–318`. -/
theorem integral_densityCoefficient (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (e : DensityIndex A C) :
    (∫ x, densityCoefficient k lam mu e x ∂law (Fin k × (A × C))) = 0 := by
  unfold densityCoefficient
  rw [integral_const_mul, integral_sampleAverage, mul_zero]

private theorem quarter_power_sq (t : ℝ) (ht : 0 ≤ t) :
    (t ^ (1 / 4 : ℝ)) ^ (2 : ℕ) = Real.sqrt t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht, Real.sqrt_eq_rpow]
  norm_num

theorem integrable_densityCoefficient_mul_conj (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (e f : DensityIndex A C) :
    Integrable (fun x ↦ densityCoefficient k lam mu e x *
      conj (densityCoefficient k lam mu f x)) (law (Fin k × (A × C))) := by
  have he (x : Sample (Fin k × (A × C))) : densityCoefficient k lam mu e x *
      conj (densityCoefficient k lam mu f x) =
      ((coefficientWeight lam mu e * coefficientWeight lam mu f : ℝ) : ℂ) *
        (sampleAverage k (e.1.1, e.2.1) (e.1.2, e.2.2) x *
          conj (sampleAverage k (f.1.1, f.2.1) (f.1.2, f.2.2) x)) := by
    simp only [densityCoefficient, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [he]
  exact (integrable_sampleAverage_mul_conj _ _ _ _ _).const_mul _

/-- Diagonal weighted covariance of the random density source, for arbitrary finite and
possibly different ket and bra supports. Zero Schmidt probabilities are allowed; no bound
depends on the support dimensions. Source: `eq:compression-slot-variance`,
`04-compression.tex:311–340`. -/
theorem integral_densityCoefficient_mul_conj (k : ℕ) (hk : 0 < k)
    (lam : A → ℝ) (mu : C → ℝ) (hlam : ∀ a, 0 ≤ lam a) (hmu : ∀ c, 0 ≤ mu c)
    (e f : DensityIndex A C) :
    (∫ x, densityCoefficient k lam mu e x * conj (densityCoefficient k lam mu f x)
      ∂law (Fin k × (A × C))) =
    if e = f then (k : ℂ)⁻¹ *
      (Real.sqrt ((lam e.1.1 * lam e.1.2) * (mu e.2.1 * mu e.2.2)) : ℂ) else 0 := by
  have he (x : Sample (Fin k × (A × C))) : densityCoefficient k lam mu e x *
      conj (densityCoefficient k lam mu f x) =
      ((coefficientWeight lam mu e * coefficientWeight lam mu f : ℝ) : ℂ) *
        (sampleAverage k (e.1.1, e.2.1) (e.1.2, e.2.2) x *
          conj (sampleAverage k (f.1.1, f.2.1) (f.1.2, f.2.2) x)) := by
    simp only [densityCoefficient, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_sampleAverage_mul_conj k hk]
  by_cases h : e = f
  · subst f
    simp only [delta, ite_true, mul_one]
    have hw : coefficientWeight lam mu e * coefficientWeight lam mu e =
        Real.sqrt ((lam e.1.1 * lam e.1.2) * (mu e.2.1 * mu e.2.2)) := by
      rw [← pow_two, coefficientWeight, quarter_power_sq]
      exact mul_nonneg (mul_nonneg (hlam _) (hlam _)) (mul_nonneg (hmu _) (hmu _))
    rw [hw]
    ring
  · have hd : delta (e.1.1, e.2.1) (f.1.1, f.2.1) *
        delta (e.1.2, e.2.2) (f.1.2, f.2.2) = 0 := by
      by_cases h1 : (e.1.1, e.2.1) = (f.1.1, f.2.1)
      · have h2 : (e.1.2, e.2.2) ≠ (f.1.2, f.2.2) := by
          intro h2
          apply h
          have ha : e.1.1 = f.1.1 := congrArg (fun z : A × C ↦ z.1) h1
          have hb : e.1.2 = f.1.2 := congrArg (fun z : A × C ↦ z.1) h2
          have hc : e.2.1 = f.2.1 := congrArg (fun z : A × C ↦ z.2) h1
          have hd : e.2.2 = f.2.2 := congrArg (fun z : A × C ↦ z.2) h2
          exact Prod.ext (Prod.ext ha hb) (Prod.ext hc hd)
        simp [delta, h2]
      · simp [delta, h1]
    simp [hd, h]

end DensityCoefficients

end

end QICLean.ComplexGaussian
