/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Poissonized finite words

For a finite alphabet of cardinality `N` and nonnegative time `t`, each word of
length `m` has mass `exp (-N * t) * t ^ m / m!`. The length has Poisson law of
rate `N * t`. Finite sums bounded by `a ^ m * C` give an integrable observable
with expectation at most `exp ((a - N) * t) * C`.

This is the finite-word probability calculation used for the excited-state
estimate in the amplification source, lines 235–249. No identification with a
chronological construction from independent clocks is asserted here.
-/

open MeasureTheory
open scoped BigOperators NNReal Nat

namespace PoissonWord

/-- Finite words, retaining the length as part of the value. -/
def Word (ι : Type*) := Σ m : ℕ, (Fin m → ι)

instance {ι : Type*} : MeasurableSpace (Word ι) := ⊤

instance {ι : Type*} : MeasurableSingletonClass (Word ι) :=
  ⟨fun _ ↦ MeasurableSet.of_discrete⟩

instance {ι : Type*} [Fintype ι] : Countable (Word ι) :=
  inferInstanceAs (Countable (Σ m : ℕ, (Fin m → ι)))

/-- The unique word of length zero. -/
def nil {ι : Type*} : Word ι := ⟨0, Fin.elim0⟩

variable {ι : Type*} [Fintype ι]

/-- The real mass of each individual word of the specified length. -/
noncomputable def weight (ι : Type*) [Fintype ι] (t : ℝ≥0) (m : ℕ) : ℝ :=
  Real.exp (-(Fintype.card ι : ℝ) * t) * (t : ℝ) ^ m / (m ! : ℝ)

lemma weight_nonneg (t : ℝ≥0) (m : ℕ) : 0 ≤ weight ι t m := by
  unfold weight
  positivity

/-- The total mass of one length is the corresponding Poisson mass. -/
lemma sum_weight (t : ℝ≥0) (m : ℕ) :
    (∑ _w : Fin m → ι, weight ι t m) =
      Real.exp (-(Fintype.card ι : ℝ) * t) *
        ((Fintype.card ι : ℝ) * t) ^ m / (m ! : ℝ) := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, weight, mul_pow]
  ring

private lemma summable_word_iff (f : Word ι → ℝ) (hf : ∀ w, 0 ≤ f w) :
    Summable f ↔ Summable (fun m ↦ ∑ w : Fin m → ι, f ⟨m, w⟩) := by
  change Summable (fun w : Σ m : ℕ, (Fin m → ι) ↦ f w) ↔ _
  rw [summable_sigma_of_nonneg hf]
  simp only [summable_fintype, forall_const, true_and, tsum_fintype]

/-- The individual word masses sum to one, including for an empty alphabet. -/
lemma hasSum_one_weight (t : ℝ≥0) :
    HasSum (fun w : Word ι ↦ weight ι t w.1) 1 := by
  have h : HasSum (fun m ↦ ∑ _w : Fin m → ι, weight ι t m) 1 := by
    simpa only [sum_weight, NNReal.coe_mul, NNReal.coe_natCast, neg_mul] using
      ProbabilityTheory.hasSum_one_poissonMeasure ((Fintype.card ι : ℝ≥0) * t)
  exact h.sigma_of_hasSum (fun _ ↦ hasSum_fintype _)
    ((summable_word_iff _ (fun w ↦ weight_nonneg t w.1)).2 h.summable)

/-- The atomic Poissonized-word measure. -/
noncomputable def measure (ι : Type*) [Fintype ι] (t : ℝ≥0) : Measure (Word ι) :=
  Measure.sum fun w ↦ ENNReal.ofReal (weight ι t w.1) • Measure.dirac w

instance isProbabilityMeasure (t : ℝ≥0) : IsProbabilityMeasure (measure ι t) :=
  (hasSum_one_weight (ι := ι) t).isProbabilityMeasure_sum_dirac
    (fun w ↦ weight_nonneg t w.1)

@[simp] lemma measure_singleton (t : ℝ≥0) (w : Word ι) :
    measure ι t {w} = ENNReal.ofReal (weight ι t w.1) :=
  Measure.sum_smul_dirac_singleton

/-- The mass of all words of a fixed length. -/
lemma measure_length (t : ℝ≥0) (m : ℕ) :
    measure ι t {w | w.1 = m} =
      ENNReal.ofReal (Real.exp (-(Fintype.card ι : ℝ) * t) *
        ((Fintype.card ι : ℝ) * t) ^ m / (m ! : ℝ)) := by
  classical
  rw [measure, Measure.sum_apply _ MeasurableSet.of_discrete]
  change (∑' w : Σ k : ℕ, (Fin k → ι), _) = _
  rw [ENNReal.tsum_sigma']
  simp only [Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.of_discrete,
    Set.mem_setOf_eq, smul_eq_mul]
  simp only [tsum_fintype]
  simp_rw [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [tsum_ite_eq, ← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ weight_nonneg t m), sum_weight]

/-- The length marginal is Mathlib's Poisson probability measure. -/
lemma map_length (t : ℝ≥0) :
    (measure ι t).map (fun w ↦ w.1) =
      ProbabilityTheory.poissonMeasure ((Fintype.card ι : ℝ≥0) * t) := by
  apply Measure.ext_of_singleton
  intro m
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton m)]
  simpa only [Set.preimage_singleton_eq, NNReal.coe_mul, NNReal.coe_natCast, neg_mul] using
    (measure_length (ι := ι) t m).trans
      (ProbabilityTheory.poissonMeasure_singleton ((Fintype.card ι : ℝ≥0) * t) m).symm

/-- At time zero the random word is empty. -/
@[simp] lemma measure_zero : measure ι 0 = Measure.dirac (nil : Word ι) := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨m, w⟩
  cases m with
  | zero =>
      have hw : (⟨0, w⟩ : Word ι) = nil := by
        congr
        exact Subsingleton.elim _ _
      simp [hw, measure_singleton, weight, nil]
  | succ m => simp [measure_singleton, weight, nil, Measure.dirac_apply']

/-- With no labels, the only possible word is empty at every time. -/
lemma measure_of_isEmpty [IsEmpty ι] (t : ℝ≥0) :
    measure ι t = Measure.dirac (nil : Word ι) := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨m, w⟩
  cases m with
  | zero =>
      have hw : (⟨0, w⟩ : Word ι) = nil := by
        congr
        exact Subsingleton.elim _ _
      simp [hw, measure_singleton, weight, nil, Fintype.card_eq_zero]
  | succ m => exact isEmptyElim (w 0)

/-- Integrability is absolute summability of the actual word weights. -/
lemma integrable_iff {E : Type*} [NormedAddCommGroup E] (t : ℝ≥0) (f : Word ι → E) :
    Integrable f (measure ι t) ↔ Summable (fun w ↦ weight ι t w.1 * ‖f w‖) := by
  rw [measure, integrable_sum_dirac_iff (by simp)]
  simp only [ENNReal.toReal_ofReal (weight_nonneg t _)]

/-- A nonnegative observable is integrable exactly when its finite length sums
are summable with the Poissonized-word weights. -/
lemma integrable_iff_sum (t : ℝ≥0) (f : Word ι → ℝ) (hf : ∀ w, 0 ≤ f w) :
    Integrable f (measure ι t) ↔
      Summable (fun m ↦ weight ι t m * ∑ w : Fin m → ι, f ⟨m, w⟩) := by
  rw [integrable_iff]
  simp only [Real.norm_eq_abs, abs_of_nonneg (hf _)]
  rw [summable_word_iff _ (fun w ↦ mul_nonneg (weight_nonneg t w.1) (hf w))]
  simp only [Finset.mul_sum]

/-- Expectation under the word measure is the weighted sum over lengths. -/
lemma integral_eq_tsum_sum (t : ℝ≥0) (f : Word ι → ℝ) (hf : ∀ w, 0 ≤ f w)
    (hfi : Integrable f (measure ι t)) :
    (∫ w, f w ∂measure ι t) =
      ∑' m, weight ι t m * ∑ w : Fin m → ι, f ⟨m, w⟩ := by
  have hs : Summable (fun w ↦ weight ι t w.1 * f w) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using (integrable_iff t f).1 hfi
  rw [measure, integral_sum_dirac (by simp)]
  simp only [ENNReal.toReal_ofReal (weight_nonneg t _), smul_eq_mul]
  rw [hs.tsum_sigma]
  simp only [tsum_fintype, Finset.mul_sum]

/-- Exact exponential summation for a geometric bound on each finite word sum. -/
lemma hasSum_weight_mul_pow (t : ℝ≥0) (a C : ℝ) :
    HasSum (fun m ↦ weight ι t m * (a ^ m * C))
      (Real.exp ((a - Fintype.card ι) * t) * C) := by
  convert ((NormedSpace.expSeries_div_hasSum_exp (a * (t : ℝ))).mul_left
    (Real.exp (-(Fintype.card ι : ℝ) * t))).mul_right C using 1
  · ext m
    simp only [weight, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 2
    ring

/-- Finite-word bounds imply both integrability and exponential decay of the
actual probability expectation; normalization and expected decay are conclusions. -/
theorem integrable_and_integral_le_of_sum_le_pow (t : ℝ≥0) (f : Word ι → ℝ)
    (hf : ∀ w, 0 ≤ f w) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hbound : ∀ m, (∑ w : Fin m → ι, f ⟨m, w⟩) ≤ a ^ m * C) :
    Integrable f (measure ι t) ∧
      (∫ w, f w ∂measure ι t) ≤ Real.exp ((a - Fintype.card ι) * t) * C := by
  have hnonneg (m : ℕ) : 0 ≤ weight ι t m * ∑ w : Fin m → ι, f ⟨m, w⟩ :=
    mul_nonneg (weight_nonneg t m) (Finset.sum_nonneg fun _ _ ↦ hf _)
  have hle (m : ℕ) : weight ι t m * (∑ w : Fin m → ι, f ⟨m, w⟩) ≤
      weight ι t m * (a ^ m * C) :=
    mul_le_mul_of_nonneg_left (hbound m) (weight_nonneg t m)
  have hs := hasSum_weight_mul_pow (ι := ι) t a C
  have hsum := Summable.of_nonneg_of_le hnonneg hle hs.summable
  have hfi := (integrable_iff_sum t f hf).2 hsum
  refine ⟨hfi, ?_⟩
  rw [integral_eq_tsum_sum t f hf hfi, ← hs.tsum_eq]
  exact hsum.tsum_le_tsum hle hs.summable

end PoissonWord
