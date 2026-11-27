/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWord.Occupation
import QICLean.Probability.PoissonWord.Partition

/-!
# Integrable real occupation of Poissonized prefixes

A bounded nonnegative real kernel gives an integrable sum over the actual
marked prefixes: the sum is bounded by the kernel bound times word length.
The finite first moment and measurable atomic time weights then justify the
real expectation/time-integral identities, including retained prefixes and
omitted labels. All integrability assertions precede the integral conversion.

This supplies the real probability identity for bounded defect kernels in
`09-amplification.tex`, lines 203–209. Operator telescoping, clock paths, and
spatial propagation are separate inputs.

It also contains the following results.

* `PoissonWord.integral_norm_sub_retained_le`: expected norm of omissions in chronological products.
-/

open MeasureTheory

section RealOccupation

open scoped BigOperators ENNReal NNReal

namespace PoissonWord

variable {ι : Type*} [Fintype ι]

/-- The actual word length has finite first moment and is integrable. -/
theorem integrable_length (T : ℝ≥0) :
    Integrable (fun w : Word ι ↦ (w.1 : ℝ)) (measure ι T) := by
  refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall fun w : Word ι ↦ Nat.cast_nonneg w.1)]
  simp only [ENNReal.ofReal_natCast, lintegral_length]
  exact ENNReal.mul_lt_top (by simp) (by simp)

/-- The real expected word length is the alphabet size times the duration. -/
theorem integral_length (T : ℝ≥0) :
    (∫ w : Word ι, (w.1 : ℝ) ∂measure ι T) = (Fintype.card ι : ℝ) * T := by
  have h := ofReal_integral_eq_lintegral_ofReal (integrable_length (ι := ι) T)
    (Filter.Eventually.of_forall fun w : Word ι ↦ Nat.cast_nonneg w.1)
  simp only [ENNReal.ofReal_natCast, lintegral_length] at h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun w : Word ι ↦ Nat.cast_nonneg w.1),
    ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal] using
    congrArg ENNReal.toReal h

/-- Every bounded nonnegative kernel is integrable under each actual word law. -/
lemma integrable_of_nonneg_le_const (t : ℝ≥0) (f : Word ι → ℝ) {C : ℝ}
    (hf : ∀ w, 0 ≤ f w) (hbound : ∀ w, f w ≤ C) : Integrable f (measure ι t) :=
  (integrable_const C).mono_nonneg Measurable.of_discrete.aestronglyMeasurable
    (Filter.Eventually.of_forall hf) (Filter.Eventually.of_forall hbound)

/-- Atomic time weights make the expectation of a bounded kernel measurable in time. -/
lemma measurable_integral_of_nonneg_le_const (f : Word ι → ℝ) {C : ℝ}
    (hf : ∀ w, 0 ≤ f w) (hbound : ∀ w, f w ≤ C) :
    Measurable (fun s : ℝ ↦ ∫ w, f w ∂measure ι (Real.toNNReal s)) := by
  have hm : Measurable (fun s : ℝ ↦
      ∑' w : Word ι, ENNReal.ofReal (weight ι (Real.toNNReal s) w.1) *
        ENNReal.ofReal (f w)) :=
    Measurable.tsum fun w ↦ (measurable_weight_ofReal w.1).ennreal_ofReal.mul_const _
  have he (s : ℝ) :
      (∑' w : Word ι, ENNReal.ofReal (weight ι (Real.toNNReal s) w.1) *
        ENNReal.ofReal (f w)).toReal = ∫ w, f w ∂measure ι (Real.toNNReal s) := by
    rw [← lintegral_eq_tsum, ← ofReal_integral_eq_lintegral_ofReal
      (integrable_of_nonneg_le_const _ f hf hbound) (Filter.Eventually.of_forall hf),
      ENNReal.toReal_ofReal (integral_nonneg hf)]
  simpa only [he] using hm.ennreal_toReal

/-- The marked-prefix sum is integrable by domination by `C` times word length. -/
theorem integrable_sum_prefix (T : ℝ≥0) (F : Word ι → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hbound : ∀ u i, F u i ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1, F (take w j) (w.2 j)) (measure ι T) := by
  refine ((integrable_length T).const_mul C).mono_nonneg
    Measurable.of_discrete.aestronglyMeasurable
    (Filter.Eventually.of_forall fun w ↦ Finset.sum_nonneg fun j _ ↦ hF _ _) ?_
  filter_upwards [] with w
  calc
    (∑ j : Fin w.1, F (take w j) (w.2 j)) ≤ ∑ _j : Fin w.1, C :=
      Finset.sum_le_sum fun j _ ↦ hbound _ _
    _ = C * (w.1 : ℝ) := by simp [mul_comm]

omit [Fintype ι] in
/-- Every finite sum of bounded word expectations is integrable on the time interval. -/
theorem integrableOn_sum_word_integral {κ : Type*} [Fintype κ] (T : ℝ≥0)
    (A : Finset ι) (F : Word κ → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hbound : ∀ u i, F u i ≤ C) :
    IntegrableOn (fun s : ℝ ↦ ∑ i ∈ A, ∫ u, F u i ∂measure κ (Real.toNNReal s))
      (Set.Ioc 0 (T : ℝ)) := by
  have hm : Measurable (fun s : ℝ ↦
      ∑ i ∈ A, ∫ u, F u i ∂measure κ (Real.toNNReal s)) :=
    Finset.measurable_sum _ fun i _ ↦
      measurable_integral_of_nonneg_le_const (F · i) (hF · i) (hbound · i)
  refine (integrable_const (A.card * C : ℝ)).mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s ↦ Finset.sum_nonneg fun i _ ↦ integral_nonneg (hF · i)) ?_
  filter_upwards [] with s
  calc
    (∑ i ∈ A, ∫ u, F u i ∂measure κ (Real.toNNReal s)) ≤ ∑ _i ∈ A, C := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ∫ _u : Word κ, C ∂measure κ (Real.toNNReal s) :=
          integral_mono (integrable_of_nonneg_le_const _ (F · i) (hF · i) (hbound · i))
            (integrable_const C) (hbound · i)
        _ = C := by simp
    _ = A.card * C := by simp

private lemma integral_eq_of_nonneg_lintegral_eq {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α → ℝ} {g : β → ℝ} (hf : Integrable f μ) (hg : Integrable g ν)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b)
    (h : (∫⁻ a, ENNReal.ofReal (f a) ∂μ) = ∫⁻ b, ENNReal.ofReal (g b) ∂ν) :
    (∫ a, f a ∂μ) = ∫ b, g b ∂ν := by
  apply (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hf0) (integral_nonneg hg0)).1
  rwa [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0),
    ofReal_integral_eq_lintegral_ofReal hg (Filter.Eventually.of_forall hg0)]

/-- The real marked-prefix identity, with integrability proved from the uniform bound. -/
theorem integral_sum_prefix (T : ℝ≥0) (F : Word ι → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hbound : ∀ u i, F u i ≤ C) :
    (∫ w, ∑ j : Fin w.1, F (take w j) (w.2 j) ∂measure ι T) =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫ u, F u i ∂measure ι (Real.toNNReal s) := by
  apply integral_eq_of_nonneg_lintegral_eq (integrable_sum_prefix T F hF hbound)
    (integrableOn_sum_word_integral T Finset.univ F hF hbound)
    (fun w ↦ Finset.sum_nonneg fun j _ ↦ hF _ _)
    (fun s ↦ Finset.sum_nonneg fun i _ ↦ integral_nonneg (hF · i))
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ hF _ _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ integral_nonneg (hF · _)),
    ofReal_integral_eq_lintegral_ofReal
      (integrable_of_nonneg_le_const _ _ (hF · _) (hbound · _))
      (Filter.Eventually.of_forall (hF · _))]
  exact lintegral_sum_prefix T (fun u i ↦ ENNReal.ofReal (F u i))

/-- Filtering each actual prefix preserves integrability of a bounded marked sum. -/
theorem integrable_sum_partition_prefix (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hbound : ∀ u i, F u i ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1,
      F (partitionWords p (take w j)).1 (w.2 j)) (measure ι T) :=
  integrable_sum_prefix T (fun u i ↦ F (partitionWords p u).1 i)
    (fun _ _ ↦ hF _ _) (fun _ _ ↦ hbound _ _)

/-- The real retained-prefix identity consumes the actual prefix/thinning law. -/
theorem integral_sum_partition_prefix (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hbound : ∀ u i, F u i ≤ C) :
    (∫ w, ∑ j : Fin w.1,
      F (partitionWords p (take w j)).1 (w.2 j) ∂measure ι T) =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ), ∑ i : ι,
        ∫ u, F u i ∂measure {i // p i} (Real.toNNReal s) := by
  apply integral_eq_of_nonneg_lintegral_eq (integrable_sum_partition_prefix p T F hF hbound)
    (integrableOn_sum_word_integral T Finset.univ F hF hbound)
    (fun w ↦ Finset.sum_nonneg fun j _ ↦ hF _ _)
    (fun s ↦ Finset.sum_nonneg fun i _ ↦ integral_nonneg (hF · i))
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ hF _ _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ integral_nonneg (hF · _)),
    ofReal_integral_eq_lintegral_ofReal
      (integrable_of_nonneg_le_const _ _ (hF · _) (hbound · _))
      (Filter.Eventually.of_forall (hF · _))]
  exact lintegral_sum_partition_prefix p T (fun u i ↦ ENNReal.ofReal (F u i))

/-- The actual occupation sum at omitted labels is integrable. -/
theorem integrable_sum_omitted_partition_prefix (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hbound : ∀ u i, F u i ≤ C) :
    Integrable (fun w ↦ ∑ j : Fin w.1,
      if p (w.2 j) then 0 else F (partitionWords p (take w j)).1 (w.2 j))
      (measure ι T) := by
  apply integrable_sum_partition_prefix p T (fun u i ↦ if p i then 0 else F u i)
    (C := max C 0)
  · intro u i
    split_ifs
    · exact le_rfl
    · exact hF u i
  · intro u i
    split_ifs
    · exact le_max_right _ _
    · exact (hbound u i).trans (le_max_left _ _)

/-- Real occupation at omitted letters is the time integral of retained-prefix expectations. -/
theorem integral_sum_omitted_partition_prefix (p : ι → Prop) [DecidablePred p] (T : ℝ≥0)
    (F : Word {i // p i} → ι → ℝ) {C : ℝ}
    (hF : ∀ u i, 0 ≤ F u i) (hbound : ∀ u i, F u i ≤ C) :
    (∫ w, ∑ j : Fin w.1,
      if p (w.2 j) then 0 else F (partitionWords p (take w j)).1 (w.2 j)
        ∂measure ι T) =
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ),
        ∑ i ∈ Finset.univ.filter (fun i ↦ ¬p i),
          ∫ u, F u i ∂measure {i // p i} (Real.toNNReal s) := by
  classical
  have hG (u) (i) : 0 ≤ if p i then 0 else F u i := by
    split_ifs
    · exact le_rfl
    · exact hF u i
  have hb (u) (i) : (if p i then 0 else F u i) ≤ max C 0 := by
    split_ifs
    · exact le_max_right _ _
    · exact (hbound u i).trans (le_max_left _ _)
  rw [integral_sum_partition_prefix p T (fun u i ↦ if p i then 0 else F u i) hG hb]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s _
  dsimp only
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i <;> simp [hi]

end PoissonWord

end RealOccupation

section ExpectedOmission

/-!
## Expected norm of omissions in chronological products

The maps are applied in the original order of each Poissonized word. Removing
the letters outside a fixed retained alphabet changes the output by at most
the sum of the corresponding defects on the earlier retained prefixes. The
expected sum is the time integral of those defects under the actual retained
word law. Each defect is bounded by twice the norm of the initial vector.

This is the algebraic and probabilistic comparison used before the spatial
estimate in OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `09-amplification.tex`, lines 203–209, source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators NNReal

namespace PoissonWord

variable {ι 𝕜 V : Type*} [Fintype ι] [Semiring 𝕜]
  [SeminormedAddCommGroup V] [Module 𝕜 V]

/-- The expected discrepancy is bounded by the time integral of omitted-map
defects on the actual retained word. No normalization of the initial vector,
nonempty alphabet, or independence hypothesis is required. Auxiliary to the
area-law manuscript, `09-amplification.tex`, lines 203–209. -/
theorem integral_norm_sub_retained_le
    (E : ι → V →ₗ[𝕜] V) (hE : ∀ i y, ‖E i y‖ ≤ ‖y‖)
    (p : ι → Prop) [DecidablePred p] (T : ℝ≥0) (x : V) :
    let act : List ι → V → V :=
      fun xs y ↦ xs.foldl (fun z i ↦ E i z) y
    let retained : Word {i // p i} → V :=
      fun u ↦ act ((List.ofFn u.2).map Subtype.val) x
    (∫ w : Word ι,
        ‖act (List.ofFn w.2) x - retained (partitionWords p w).1‖
        ∂measure ι T) ≤
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ),
        ∑ i ∈ Finset.univ.filter (fun i ↦ ¬p i),
          ∫ u : Word {i // p i}, ‖E i (retained u) - retained u‖
            ∂measure {i // p i} (Real.toNNReal s) := by
  dsimp only
  have hact (xs : List ι) (y : V) :
      ‖xs.foldl (fun z i ↦ E i z) y‖ ≤ ‖y‖ :=
    List.foldlRecOn (motive := fun z : V ↦ ‖z‖ ≤ ‖y‖) xs
      (fun z i ↦ E i z) le_rfl (fun z hz i _ ↦ (hE i z).trans hz)
  let R (u : Word {i // p i}) : V :=
    ((List.ofFn u.2).map Subtype.val).foldl (fun z i ↦ E i z) x
  let F (u : Word {i // p i}) (i : ι) : ℝ := ‖E i (R u) - R u‖
  have hF (u : Word {i // p i}) (i : ι) : F u i ≤ ‖x‖ + ‖x‖ :=
    (norm_sub_le (E i (R u)) (R u)).trans
      (add_le_add ((hE i (R u)).trans (hact _ x)) (hact _ x))
  let L (w : Word ι) : ℝ :=
    ‖(List.ofFn w.2).foldl (fun z i ↦ E i z) x - R (partitionWords p w).1‖
  have hL (w : Word ι) : L w ≤ ‖x‖ + ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add (hact _ x) (hact _ x))
  have hleft : Integrable L (measure ι T) :=
    integrable_of_nonneg_le_const T L (fun _ ↦ norm_nonneg _) hL
  have hsum := integrable_sum_omitted_partition_prefix p T F
    (fun _ _ ↦ norm_nonneg _) hF
  have hpoint (w : Word ι) : L w ≤
      ∑ j : Fin w.1, if p (w.2 j) then 0 else
        F (partitionWords p (take w j)).1 (w.2 j) :=
    norm_foldl_sub_partitionWords_fst_le_sum E hE p w x
  exact (integral_mono hleft hsum hpoint).trans_eq
    (integral_sum_omitted_partition_prefix p T F (fun _ _ ↦ norm_nonneg _) hF)

end PoissonWord

end ExpectedOmission
