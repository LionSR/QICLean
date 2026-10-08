/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordRealOccupation

/-!
# The bounded real Poisson word jump formula

Successive actual prefixes telescope a word observable into its chronological
one-letter increments. The signed marked-prefix occupation identity then gives
the time integral of the expected increment under the actual Poisson word law.
Uniform bounds supply all word and time integrability requirements.

This is the finite-alphabet probability input to the Poisson jump formula in
`09-amplification.tex`, lines 159–171 (source revision `adc7f124`). The integral
upper bound below permits a nonnegative increment majorant. It does not
construct a clock process or supply spatial propagation or a Gronwall estimate.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace PoissonWord

variable {ι : Type*}

/-- The next chronological prefix appends the actual next letter. -/
lemma take_succ_eq_append_singleton (w : Word ι) (j : Fin w.1) :
    take w (j + 1) = append (take w j) (singleton (w.2 j)) := by
  apply List.equivSigmaTuple.symm.injective
  change List.ofFn (take w (j + 1)).2 =
    List.ofFn (append (take w j) (singleton (w.2 j))).2
  simp only [ofFn_take, append, List.ofFn_fin_append, ofFn_singleton]
  rw [List.take_succ_eq_append_getElem (by simp), List.getElem_ofFn]

/-- The actual chronological one-letter increments telescope on every finite word. -/
theorem sum_prefix_increment (f : Word ι → ℝ) (w : Word ι) :
    (∑ j : Fin w.1, (f (append (take w j) (singleton (w.2 j))) - f (take w j))) =
      f w - f nil := by
  simp_rw [← take_succ_eq_append_singleton]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ f (take w (j + 1)) - f (take w j)),
    Finset.sum_range_sub (fun j : ℕ ↦ f (take w j))]
  have hlast : take w w.1 = w := by
    apply List.equivSigmaTuple.symm.injective
    change List.ofFn (take w w.1).2 = List.ofFn w.2
    rw [ofFn_take]
    simpa only [List.length_ofFn] using List.take_length (l := List.ofFn w.2)
  have hzero : take w 0 = nil := by
    apply List.equivSigmaTuple.symm.injective
    change List.ofFn (take w 0).2 = List.ofFn (nil : Word ι).2
    simp [nil]
  rw [hlast, hzero]

variable [Fintype ι]

/-- A uniformly bounded real observable is integrable under the word law. -/
lemma integrable_of_abs_le_const (t : ℝ≥0) (f : Word ι → ℝ) {C : ℝ}
    (hbound : ∀ w, |f w| ≤ C) : Integrable f (measure ι t) := by
  exact (integrable_const C).mono' Measurable.of_discrete.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w ↦ by simpa only [Real.norm_eq_abs] using hbound w)

/-- Signed bounded marked-prefix sums are dominated in norm by the integrable word length. -/
theorem integrable_sum_prefix_of_abs_le_const (T : ℝ≥0) (F : Word ι → ι → ℝ)
    {C : ℝ} (hbound : ∀ u i, |F u i| ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1, F (take w j) (w.2 j)) (measure ι T) := by
  apply ((integrable_length T).const_mul C).mono'
    Measurable.of_discrete.aestronglyMeasurable
  filter_upwards [] with w
  calc
    ‖∑ j : Fin w.1, F (take w j) (w.2 j)‖ ≤
        ∑ j : Fin w.1, ‖F (take w j) (w.2 j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin w.1, C := Finset.sum_le_sum fun j _ ↦ by
      simpa only [Real.norm_eq_abs] using hbound (take w j) (w.2 j)
    _ = C * (w.1 : ℝ) := by simp [mul_comm]

/-- Expectations of uniformly bounded real observables are measurable in time. -/
lemma measurable_integral_of_abs_le_const (f : Word ι → ℝ) {C : ℝ}
    (hbound : ∀ w, |f w| ≤ C) :
    Measurable (fun s : ℝ ↦ ∫ w, f w ∂measure ι (Real.toNNReal s)) := by
  have hp (w) : (f w)⁺ ≤ C :=
    sup_le ((le_abs_self _).trans (hbound w)) ((abs_nonneg _).trans (hbound w))
  have hn (w) : (f w)⁻ ≤ C :=
    sup_le ((neg_le_abs _).trans (hbound w)) ((abs_nonneg _).trans (hbound w))
  have he (s : ℝ) : (∫ w, f w ∂measure ι (Real.toNNReal s)) =
      (∫ w, (f w)⁺ ∂measure ι (Real.toNNReal s)) -
        ∫ w, (f w)⁻ ∂measure ι (Real.toNNReal s) := by
    rw [← integral_sub
      (integrable_of_nonneg_le_const _ _ (fun _ ↦ posPart_nonneg _) hp)
      (integrable_of_nonneg_le_const _ _ (fun _ ↦ negPart_nonneg _) hn)]
    simp
  simp_rw [he]
  exact (measurable_integral_of_nonneg_le_const _ (fun _ ↦ posPart_nonneg _) hp).sub
    (measurable_integral_of_nonneg_le_const _ (fun _ ↦ negPart_nonneg _) hn)

/-- A finite sum of bounded signed word expectations is integrable on the time interval. -/
theorem integrableOn_sum_word_integral_of_abs_le_const (T : ℝ≥0)
    (F : Word ι → ι → ℝ) {C : ℝ} (hbound : ∀ u i, |F u i| ≤ C) :
    IntegrableOn (fun s : ℝ ↦ ∑ i : ι, ∫ u, F u i ∂measure ι (Real.toNNReal s))
      (Set.Ioc 0 (T : ℝ)) := by
  apply integrable_finsetSum
  intro i _
  apply (integrable_const C).mono'
    (measurable_integral_of_abs_le_const (F · i) (hbound · i)).aestronglyMeasurable
  filter_upwards [] with s
  calc
    ‖∫ u, F u i ∂measure ι (Real.toNNReal s)‖ ≤
        ∫ u, ‖F u i‖ ∂measure ι (Real.toNNReal s) := norm_integral_le_integral_norm _
    _ ≤ ∫ _u : Word ι, C ∂measure ι (Real.toNNReal s) :=
      integral_mono (integrable_of_abs_le_const _ _ (hbound · i)).norm
        (integrable_const C) (fun u ↦ by simpa only [Real.norm_eq_abs] using hbound u i)
    _ = C := by simp

/-- The real marked-prefix occupation identity also holds for signed bounded kernels. -/
theorem integral_sum_prefix_of_abs_le_const (T : ℝ≥0) (F : Word ι → ι → ℝ)
    {C : ℝ} (hbound : ∀ u i, |F u i| ≤ C) :
    (∫ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure ι T) =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫ u, F u i ∂measure ι (Real.toNNReal s) := by
  have hp (u) (i) : (F u i)⁺ ≤ C :=
    sup_le ((le_abs_self _).trans (hbound u i)) ((abs_nonneg _).trans (hbound u i))
  have hn (u) (i) : (F u i)⁻ ≤ C :=
    sup_le ((neg_le_abs _).trans (hbound u i)) ((abs_nonneg _).trans (hbound u i))
  have hword (w : Word ι) : (∑ j : Fin w.1, F (take w j) (w.2 j)) =
      (∑ j : Fin w.1, (F (take w j) (w.2 j))⁺) -
        ∑ j : Fin w.1, (F (take w j) (w.2 j))⁻ := by
    rw [← Finset.sum_sub_distrib]
    simp
  have htime (s : ℝ) : (∑ i : ι, ∫ u, F u i ∂measure ι (Real.toNNReal s)) =
      (∑ i : ι, ∫ u, (F u i)⁺ ∂measure ι (Real.toNNReal s)) -
        ∑ i : ι, ∫ u, (F u i)⁻ ∂measure ι (Real.toNNReal s) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_sub
      (integrable_of_nonneg_le_const _ _ (fun _ ↦ posPart_nonneg _) (hp · i))
      (integrable_of_nonneg_le_const _ _ (fun _ ↦ negPart_nonneg _) (hn · i))]
    simp
  simp_rw [hword, htime]
  rw [integral_sub (integrable_sum_prefix T _ (fun _ _ ↦ posPart_nonneg _) hp)
      (integrable_sum_prefix T _ (fun _ _ ↦ negPart_nonneg _) hn),
    integral_sub
      (integrableOn_sum_word_integral T Finset.univ _ (fun _ _ ↦ posPart_nonneg _) hp)
      (integrableOn_sum_word_integral T Finset.univ _ (fun _ _ ↦ negPart_nonneg _) hn),
    integral_sum_prefix T _ (fun _ _ ↦ posPart_nonneg _) hp,
    integral_sum_prefix T _ (fun _ _ ↦ negPart_nonneg _) hn]

/-- The bounded real Poisson jump formula in integral form, using append-right chronology.
This supplies the finite-alphabet probability identity used in
`09-amplification.tex`, lines 159–171 (source revision `adc7f124`). -/
theorem integral_sub_eq_integral_sum_increment (T : ℝ≥0) (f : Word ι → ℝ)
    {C : ℝ} (hbound : ∀ w, |f w| ≤ C) :
    (∫ w, f w ∂measure ι T) - f nil =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫ u, (f (append u (singleton i)) - f u) ∂measure ι (Real.toNNReal s) := by
  have hinc (u : Word ι) (i : ι) : |f (append u (singleton i)) - f u| ≤ 2 * C :=
    (abs_sub _ _).trans (by linarith [hbound (append u (singleton i)), hbound u])
  have h := integral_sum_prefix_of_abs_le_const T
    (fun u i ↦ f (append u (singleton i)) - f u) hinc
  simp_rw [sum_prefix_increment] at h
  rw [integral_sub (integrable_of_abs_le_const T f hbound) (integrable_const _)] at h
  simpa using h

/-- A bounded nonnegative majorant for each actual one-letter increment bounds the
expected change by its time-integrated expectation. This is the finite-word upper-bound
step in `09-amplification.tex`, lines 159–171 (source revision `adc7f124`); spatial
summation and subsequent Gronwall estimates are separate hypotheses and arguments. -/
theorem integral_le_add_integral_sum_of_increment_le (T : ℝ≥0) (f : Word ι → ℝ)
    (G : Word ι → ι → ℝ) {C D : ℝ} (hbound : ∀ w, |f w| ≤ C)
    (hG : ∀ u i, 0 ≤ G u i) (hGbound : ∀ u i, G u i ≤ D)
    (hinc : ∀ u i, f (append u (singleton i)) - f u ≤ G u i) :
    (∫ w, f w ∂measure ι T) ≤ f nil +
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫ u, G u i ∂measure ι (Real.toNNReal s) := by
  have hpath (w : Word ι) : f w - f nil ≤ ∑ j : Fin w.1, G (take w j) (w.2 j) := by
    rw [← sum_prefix_increment f w]
    exact Finset.sum_le_sum fun j _ ↦ hinc (take w j) (w.2 j)
  have h := integral_mono ((integrable_of_abs_le_const T f hbound).sub (integrable_const _))
    (integrable_sum_prefix T G hG hGbound) hpath
  simp only [Pi.sub_apply] at h
  rw [integral_sub (integrable_of_abs_le_const T f hbound) (integrable_const _),
    integral_sum_prefix T G hG hGbound] at h
  simpa using (sub_le_iff_le_add'.mp h)

end PoissonWord
