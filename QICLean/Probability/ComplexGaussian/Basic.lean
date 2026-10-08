/-
Released under Apache 2.0 license as described in the file LICENSE.
Assisted-by: OpenAI Codex (GPT-6).

This file includes modified proof material from openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a:
  lean/OAI/Probability/ParisiFinite/Field.lean: field, field_covariance, field_law;
  lean/OAI/Probability/ParisiFinite/Law.lean: memLp_field_nat, integrable_real_pow,
    integrable_field_pow, field_fourth,
    memLp_field_product, integrable_field_four, polarization, fourth_norm,
    field_wick_four.
The upstream repository is distributed under Apache 2.0. Modifications:
renamed declarations and namespaces, removed unrelated imports and material,
proved the scalar fourth moment directly from Mathlib's Gaussian MGF,
and added complex linear combinations and circular-complex coordinates.
The covariance results in Covariance.lean are new proofs.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# Circular complex Gaussian coordinates

The canonical finite family consists of independent real Gaussian coordinates,
paired as `(x + I * y) / sqrt 2`. This is the normalization in
*Polynomial PEPS approximation of gapped square-grid ground states*,
`04-compression.tex:279–340`, equations `compression-random-source` and
`compression-gaussian-covariance`.

The real fourth-moment polarization used below is adapted from the upstream
proofs listed in the file notice. The scalar MGF derivative proof and the
complex-coordinate construction are new.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal ComplexConjugate BigOperators

namespace QICLean.ComplexGaussian

noncomputable section

/-- The scalar fourth moment underlying the complex pairing formula
(`04-compression.tex:326–334`). -/
theorem integral_standard_real_fourth :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := by
  let f : ℝ → ℝ := fun t ↦ Real.exp (t ^ 2 / 2)
  have h0 (t : ℝ) : HasDerivAt f (t * f t) t := by
    convert (((hasDerivAt_id t).fun_pow 2).div_const 2).exp using 1 <;>
      dsimp [f]
    all_goals ring
  have h1 (t : ℝ) : HasDerivAt (fun t ↦ t * f t) ((1 + t ^ 2) * f t) t := by
    convert (hasDerivAt_id t).fun_mul (h0 t) using 1 <;> dsimp
    all_goals ring
  have h2 (t : ℝ) : HasDerivAt (fun t ↦ (1 + t ^ 2) * f t)
      ((3 * t + t ^ 3) * f t) t := by
    convert ((hasDerivAt_const t 1).fun_add ((hasDerivAt_id t).fun_pow 2)).fun_mul (h0 t)
      using 1 <;> dsimp
    all_goals ring
  have h3 (t : ℝ) : HasDerivAt (fun t ↦ (3 * t + t ^ 3) * f t)
      ((3 + 6 * t ^ 2 + t ^ 4) * f t) t := by
    convert (((hasDerivAt_id t).const_mul 3).fun_add ((hasDerivAt_id t).fun_pow 3)).fun_mul
      (h0 t) using 1 <;> dsimp
    all_goals ring
  have d0 : deriv f = fun t ↦ t * f t := funext fun t ↦ (h0 t).deriv
  have d1 : deriv (fun t ↦ t * f t) = fun t ↦ (1 + t ^ 2) * f t :=
    funext fun t ↦ (h1 t).deriv
  have d2 : deriv (fun t ↦ (1 + t ^ 2) * f t) = fun t ↦ (3 * t + t ^ 3) * f t :=
    funext fun t ↦ (h2 t).deriv
  have d3 : deriv (fun t ↦ (3 * t + t ^ 3) * f t) =
      fun t ↦ (3 + 6 * t ^ 2 + t ^ 4) * f t := funext fun t ↦ (h3 t).deriv
  have hm := iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 1) (by simp) 4
  simp only [Pi.pow_apply] at hm
  rw [← hm, mgf_fun_id_gaussianReal]
  simp only [zero_mul, NNReal.coe_one, one_mul, zero_add]
  change iteratedDeriv 4 f 0 = 3
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, d0, d1, d2, d3]
  norm_num [f]

section RealFields

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A real linear coordinate of the standard Gaussian. -/
def realField (a : E) (x : E) : ℝ := ⟪a, x⟫

theorem memLp_realField (a : E) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (realField a) p (stdGaussian E) :=
  (innerSL ℝ a).comp_memLp' (IsGaussian.memLp_id (stdGaussian E) p hp)

theorem integrable_realField_pow (a : E) (n : ℕ) :
    Integrable (fun x ↦ realField a x ^ n) (stdGaussian E) := by
  have h := memLp_realField a n (by simp)
  exact h.integrable_norm_pow'.mono' (h.aestronglyMeasurable.pow n)
    (Filter.Eventually.of_forall fun x ↦ le_of_eq (norm_pow _ _))

theorem integral_realField_mul (a b : E) :
    (∫ x, realField a x * realField b x ∂stdGaussian E) = ⟪a, b⟫ := by
  have h := covarianceBilin_apply (μ := stdGaussian E) IsGaussian.memLp_two_id a b
  rw [covarianceBilin_stdGaussian] at h
  simpa only [realField, id_eq, integral_id_stdGaussian, sub_zero,
    innerSL_apply_apply ℝ] using h.symm

theorem realField_law (a : E) :
    (stdGaussian E).map (realField a) = gaussianReal 0 (‖a‖₊ ^ 2) := by
  change (stdGaussian E).map (innerSL ℝ a) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  congr 1
  simp only [innerSL_apply_norm]
  apply NNReal.coe_injective
  simp only [Real.coe_toNNReal', NNReal.coe_pow, coe_nnnorm,
    sup_eq_left.mpr (sq_nonneg ‖a‖)]

theorem integral_realField_fourth (a : E) :
    (∫ x, realField a x ^ 4 ∂stdGaussian E) = 3 * ‖a‖ ^ 4 := by
  have hf : HasLaw (realField a) (gaussianReal 0 (‖a‖₊ ^ 2)) (stdGaussian E) :=
    ⟨by unfold realField; fun_prop, realField_law a⟩
  have hs : HasLaw (fun t : ℝ ↦ ‖a‖ * t) (gaussianReal 0 (‖a‖₊ ^ 2))
      (gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.coe_injective
      simp [pow_two]
  calc
    _ = ∫ t : ℝ, t ^ 4 ∂gaussianReal 0 (‖a‖₊ ^ 2) := hf.integral_comp (by fun_prop)
    _ = ∫ t : ℝ, (‖a‖ * t) ^ 4 ∂gaussianReal 0 1 :=
      (hs.integral_comp (by fun_prop : AEStronglyMeasurable (fun t : ℝ ↦ t ^ 4)
        (gaussianReal 0 (‖a‖₊ ^ 2)))).symm
    _ = 3 * ‖a‖ ^ 4 := by
      simp only [mul_pow, integral_const_mul, integral_standard_real_fourth]
      ring

theorem memLp_realField_mul (a b : E) :
    MemLp (fun x ↦ realField a x * realField b x) 2 (stdGaussian E) := by
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  exact (memLp_realField a 4 (by norm_num)).fun_mul
    (memLp_realField b 4 (by norm_num))

theorem integrable_realField_four (a b c d : E) :
    Integrable (fun x ↦ realField a x * realField b x *
      (realField c x * realField d x)) (stdGaussian E) :=
  (memLp_realField_mul a b).integrable_mul (memLp_realField_mul c d)

/-- Fourth polarization of a real product, used in Isserlis' formula. -/
theorem real_fourth_polarization (a b c d : ℝ) :
    192 * (a * b * (c * d)) =
      (a + b + c + d) ^ 4 - (a + b + c - d) ^ 4 -
      (a + b - c + d) ^ 4 + (a + b - c - d) ^ 4 -
      (a - b + c + d) ^ 4 + (a - b + c - d) ^ 4 +
      (a - b - c + d) ^ 4 - (a - b - c - d) ^ 4 := by ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Fourth power of the real Hilbert-space norm in terms of its quadratic form. -/
theorem norm_four_eq_inner_self_sq (v : E) : ‖v‖ ^ 4 = ⟪v, v⟫ ^ 2 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, real_inner_self_eq_norm_sq]

/-- Real Isserlis formula. It applies to coincident coordinates as well as distinct ones.
Adapted from `OAI.ClassicalGaussian.field_wick_four` at the commit in the file notice. -/
theorem integral_realField_four_eq_pairings (a b c d : E) :
    (∫ x, realField a x * realField b x * (realField c x * realField d x)
      ∂stdGaussian E) =
    ⟪a, b⟫ * ⟪c, d⟫ + ⟪a, c⟫ * ⟪b, d⟫ + ⟪a, d⟫ * ⟪b, c⟫ := by
  have he : (fun x ↦ 192 * (realField a x * realField b x *
      (realField c x * realField d x))) =
      (fun x ↦ realField (a + b + c + d) x ^ 4 -
        realField (a + b + c - d) x ^ 4 - realField (a + b - c + d) x ^ 4 +
        realField (a + b - c - d) x ^ 4 - realField (a - b + c + d) x ^ 4 +
        realField (a - b + c - d) x ^ 4 + realField (a - b - c + d) x ^ 4 -
        realField (a - b - c - d) x ^ 4) := by
    funext x
    simp only [realField, inner_add_left, inner_sub_left]
    exact real_fourth_polarization _ _ _ _
  have h := congrArg (fun f : E → ℝ ↦ ∫ x, f x ∂stdGaussian E) he
  rw [integral_const_mul] at h
  have h2 := (integrable_realField_pow (a + b + c + d) 4).sub
    (integrable_realField_pow (a + b + c - d) 4)
  have h3 := h2.sub (integrable_realField_pow (a + b - c + d) 4)
  have h4 := h3.add (integrable_realField_pow (a + b - c - d) 4)
  have h5 := h4.sub (integrable_realField_pow (a - b + c + d) 4)
  have h6 := h5.add (integrable_realField_pow (a - b + c - d) 4)
  have h7 := h6.add (integrable_realField_pow (a - b - c + d) 4)
  have hs8 := integral_sub h7 (integrable_realField_pow (a - b - c - d) 4)
  have hs7 := integral_add h6 (integrable_realField_pow (a - b - c + d) 4)
  have hs6 := integral_add h5 (integrable_realField_pow (a - b + c - d) 4)
  have hs5 := integral_sub h4 (integrable_realField_pow (a - b + c + d) 4)
  have hs4 := integral_add h3 (integrable_realField_pow (a + b - c - d) 4)
  have hs3 := integral_sub h2 (integrable_realField_pow (a + b - c + d) 4)
  have hs2 := integral_sub (integrable_realField_pow (a + b + c + d) 4)
    (integrable_realField_pow (a + b + c - d) 4)
  simp only [Pi.sub_apply, Pi.add_apply] at hs8 hs7 hs6 hs5 hs4 hs3 hs2
  rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2] at h
  simp only [integral_realField_fourth, norm_four_eq_inner_self_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right] at h
  simp only [real_inner_comm] at h ⊢
  linear_combination h / 192

end RealFields

section ComplexFields

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A complex linear combination of two real Gaussian coordinates. -/
def linearField (v : Fin 2 → E) (c : Fin 2 → ℂ) (x : E) : ℂ :=
  ∑ i, c i * (realField (v i) x : ℂ)

/-- The bilinear (without conjugation) second moment of two complex Gaussian fields. -/
def pairing (v w : Fin 2 → E) (c d : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, c i * d j * (⟪v i, w j⟫ : ℂ)

theorem memLp_linearField (v : Fin 2 → E) (c : Fin 2 → ℂ)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (linearField v c) p (stdGaussian E) := by
  unfold linearField
  exact memLp_finsetSum _ fun i _ ↦ (memLp_realField (v i) p hp).ofReal.const_mul (c i)

theorem memLp_linearField_mul (v w : Fin 2 → E) (c d : Fin 2 → ℂ) :
    MemLp (fun x ↦ linearField v c x * linearField w d x) 2 (stdGaussian E) := by
  let : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]⟩
  exact (memLp_linearField v c 4 (by norm_num)).fun_mul
    (memLp_linearField w d 4 (by norm_num))

private theorem integrable_complex_realField_mul (a b : E) :
    Integrable (fun x ↦ ((realField a x * realField b x : ℝ) : ℂ))
      (stdGaussian E) :=
  ((memLp_realField_mul a b).ofReal).integrable (by norm_num)

private theorem integrable_complex_realField_four (a b c d : E) :
    Integrable (fun x ↦ ((realField a x * realField b x *
      (realField c x * realField d x) : ℝ) : ℂ)) (stdGaussian E) := by
  exact Complex.ofRealCLM.integrable_comp (integrable_realField_four a b c d)

theorem integral_linearField_mul (v w : Fin 2 → E) (c d : Fin 2 → ℂ) :
    (∫ x, linearField v c x * linearField w d x ∂stdGaussian E) = pairing v w c d := by
  have he (x : E) : linearField v c x * linearField w d x =
      ∑ i, ∑ j, (c i * d j) *
        ((realField (v i) x * realField (w j) x : ℝ) : ℂ) := by
    simp only [linearField, Fin.sum_univ_two]
    push_cast
    ring
  have hi (i j : Fin 2) : Integrable (fun x ↦ (c i * d j) *
      ((realField (v i) x * realField (w j) x : ℝ) : ℂ)) (stdGaussian E) :=
    (integrable_complex_realField_mul _ _).const_mul _
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j)]
  simp_rw [integral_const_mul, integral_complex_ofReal, integral_realField_mul]
  rfl

/-- The fourth-moment pairing formula for complex linear Gaussian fields.
This is the real Isserlis identity extended by complex multilinearity. -/
theorem integral_linearField_four (v w u z : Fin 2 → E) (c d e f : Fin 2 → ℂ) :
    (∫ x, linearField v c x * linearField w d x *
      (linearField u e x * linearField z f x) ∂stdGaussian E) =
    pairing v w c d * pairing u z e f + pairing v u c e * pairing w z d f +
      pairing v z c f * pairing w u d e := by
  have he (x : E) : linearField v c x * linearField w d x *
      (linearField u e x * linearField z f x) =
      ∑ i, ∑ j, ∑ k, ∑ l, (c i * d j * e k * f l) *
        ((realField (v i) x * realField (w j) x *
          (realField (u k) x * realField (z l) x) : ℝ) : ℂ) := by
    simp only [linearField, Fin.sum_univ_two]
    push_cast
    ring
  have hi (i j k l : Fin 2) : Integrable (fun x ↦ (c i * d j * e k * f l) *
      ((realField (v i) x * realField (w j) x *
        (realField (u k) x * realField (z l) x) : ℝ) : ℂ)) (stdGaussian E) :=
    (integrable_complex_realField_four _ _ _ _).const_mul _
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    integrable_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hi i j k l)]
  simp_rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ fun k _ ↦
    integrable_finsetSum _ fun l _ ↦ hi _ j k l)]
  simp_rw [integral_finsetSum _ (fun k _ ↦ integrable_finsetSum _ fun l _ ↦ hi _ _ k l)]
  simp_rw [integral_finsetSum _ (fun l _ ↦ hi _ _ _ l)]
  simp_rw [integral_const_mul, integral_complex_ofReal, integral_realField_four_eq_pairings]
  simp only [pairing, Fin.sum_univ_two]
  push_cast
  ring

end ComplexFields

section Coordinates

variable {ι : Type*} [Fintype ι]

/-- Sample space for a finite family of circular complex Gaussians. -/
abbrev Sample (ι : Type*) [Fintype ι] := EuclideanSpace ℝ (ι × Fin 2)

/-- Joint law of the independent real coordinates forming the complex Gaussians. -/
def law (ι : Type*) [Fintype ι] : Measure (Sample ι) := stdGaussian (Sample ι)

instance : IsProbabilityMeasure (law ι) := inferInstanceAs (IsProbabilityMeasure (stdGaussian _))

/-- The real coordinate vectors of the `i`-th complex Gaussian. -/
def coordinateVectors (i : ι) (j : Fin 2) : Sample ι :=
  EuclideanSpace.basisFun (ι × Fin 2) ℝ (i, j)

/-- Coefficients for unit-variance circular complex coordinates. -/
def coordinateCoefficients (j : Fin 2) : ℂ :=
  if j = 0 then (Real.sqrt 2 : ℂ)⁻¹ else Complex.I * (Real.sqrt 2 : ℂ)⁻¹

/-- A standard circular complex Gaussian coordinate, normalized by `E |g|² = 1`.
Source: `04-compression.tex:291–297`. -/
def coordinate (i : ι) : Sample ι → ℂ :=
  linearField (coordinateVectors i) coordinateCoefficients

theorem coordinate_apply (i : ι) (x : Sample ι) :
    coordinate i x = ((x (i, 0) : ℂ) + Complex.I * (x (i, 1) : ℂ)) /
      (Real.sqrt 2 : ℂ) := by
  simp [coordinate, linearField, Fin.sum_univ_two, coordinateVectors,
    realField, coordinateCoefficients, div_eq_mul_inv]
  ring

/-- All finite moments of the canonical circular complex coordinates exist. -/
theorem memLp_coordinate (i : ι) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (coordinate i) p (law ι) := memLp_linearField _ _ p hp

theorem conj_coordinate (i : ι) (x : Sample ι) :
    conj (coordinate i x) =
      linearField (coordinateVectors i) (fun j ↦ conj (coordinateCoefficients j)) x := by
  simp [coordinate, linearField, map_mul]

theorem memLp_conj_coordinate (i : ι) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x ↦ conj (coordinate i x)) p (law ι) := by
  simp_rw [conj_coordinate]
  exact memLp_linearField _ _ p hp

end Coordinates

end

end QICLean.ComplexGaussian
