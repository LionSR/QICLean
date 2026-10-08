/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TaggedInterleavings
import QICLean.Probability.PoissonWord
import Mathlib.Data.List.OfFn
import Mathlib.Probability.Independence.Basic

/-!
# Independent thinning of Poissonized finite words

Filtering a word over a disjoint union of finite alphabets gives independent
Poissonized words over the two alphabets. The joint law follows by enumerating
the actual tagged interleavings of each prescribed pair and summing their
equal atomic masses. Repeated letters, empty alphabets, and time zero are
included.

This is a supporting discrete characterization for the amplification source,
`09-amplification.tex`, lines 49–54 and 237–253: a retained/omitted word coupling
at one fixed time. It does not construct event times, independent increments,
or a process indexed by time.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal Nat

namespace PoissonWord

variable {ι κ : Type*}

/-- The left-tagged letters of a word, in their original order. -/
def leftWord (w : Word (ι ⊕ κ)) : Word ι :=
  List.equivSigmaTuple ((List.equivSigmaTuple.symm w).filterMap Sum.getLeft?)

/-- The right-tagged letters of a word, in their original order. -/
def rightWord (w : Word (ι ⊕ κ)) : Word κ :=
  List.equivSigmaTuple ((List.equivSigmaTuple.symm w).filterMap Sum.getRight?)

@[simp] lemma leftWord_nil : leftWord (nil : Word (ι ⊕ κ)) = nil := by
  apply List.equivSigmaTuple.symm.injective
  simp [leftWord, nil, List.equivSigmaTuple]

@[simp] lemma rightWord_nil : rightWord (nil : Word (ι ⊕ κ)) = nil := by
  apply List.equivSigmaTuple.symm.injective
  simp [rightWord, nil, List.equivSigmaTuple]

/-- The two filters partition the positions of the original word. -/
lemma leftWord_length_add_rightWord_length (w : Word (ι ⊕ κ)) :
    (leftWord w).1 + (rightWord w).1 = w.1 := by
  simpa [leftWord, rightWord, List.equivSigmaTuple] using
    TaggedInterleavings.length_filterMap_add (List.equivSigmaTuple.symm w)

/-- The event that both filtered words have prescribed values. -/
def thinningEvent (u : Word ι) (v : Word κ) : Set (Word (ι ⊕ κ)) :=
  {w | leftWord w = u ∧ rightWord w = v}

/-- The actual words having a prescribed pair of filtered words. -/
abbrev thinningFiber (u : Word ι) (v : Word κ) := ↥(thinningEvent u v)

private noncomputable def thinningWords (u : Word ι) (v : Word κ) :
    Finset (Word (ι ⊕ κ)) := by
  classical
  exact (TaggedInterleavings.taggedInterleavings
    (List.equivSigmaTuple.symm u) (List.equivSigmaTuple.symm v)).toFinset.map
      List.equivSigmaTuple.toEmbedding

private lemma mem_thinningWords (u : Word ι) (v : Word κ) (w : Word (ι ⊕ κ)) :
    w ∈ thinningWords u v ↔ w ∈ thinningEvent u v := by
  classical
  simp only [thinningWords, Finset.mem_map_equiv, List.mem_toFinset,
    TaggedInterleavings.mem_taggedInterleavings_iff, thinningEvent, Set.mem_ofPred_eq,
    leftWord, rightWord, ← Equiv.eq_symm_apply]

noncomputable instance instFintypeThinningFiber (u : Word ι) (v : Word κ) :
    Fintype (thinningFiber u v) :=
  Fintype.ofFinset (thinningWords u v) (mem_thinningWords u v)

/-- A pair of finite filtered words has finitely many interleavings, even over
infinite alphabets. -/
lemma finite_thinningEvent (u : Word ι) (v : Word κ) : (thinningEvent u v).Finite :=
  Set.toFinite _

/-- Every word in the joint fiber has the sum of the prescribed lengths. -/
lemma length_eq_add_of_mem_thinningEvent {u : Word ι} {v : Word κ}
    {w : Word (ι ⊕ κ)} (h : w ∈ thinningEvent u v) : w.1 = u.1 + v.1 := by
  rw [← leftWord_length_add_rightWord_length w, h.1, h.2]

/-- The binomial coefficient counts the actual words in each joint fiber. -/
lemma card_thinningFiber (u : Word ι) (v : Word κ) :
    Fintype.card (thinningFiber u v) = Nat.choose (u.1 + v.1) u.1 := by
  classical
  rw [Fintype.card_of_finset' (thinningWords u v) (mem_thinningWords u v),
    thinningWords, Finset.card_map,
    List.toFinset_card_of_nodup (TaggedInterleavings.nodup_taggedInterleavings _ _),
    TaggedInterleavings.length_taggedInterleavings]
  simp [List.equivSigmaTuple]

variable [Fintype ι] [Fintype κ]

/-- The joint event mass is its finite cardinality times the common word mass. -/
lemma measure_thinningEvent (t : ℝ≥0) (u : Word ι) (v : Word κ) :
    measure (ι ⊕ κ) t (thinningEvent u v) =
      (Fintype.card (thinningFiber u v) : ℝ≥0∞) *
        ENNReal.ofReal (weight (ι ⊕ κ) t (u.1 + v.1)) := by
  classical
  have hsum : (∑' w : thinningFiber u v, measure (ι ⊕ κ) t {w.1}) =
      measure (ι ⊕ κ) t (thinningEvent u v) := by
    simpa using tsum_measure_preimage_singleton (μ := measure (ι ⊕ κ) t)
      (s := thinningEvent u v) (f := id) (Set.to_countable _)
      (fun w _ ↦ measurableSet_singleton w)
  rw [← hsum, tsum_fintype]
  simp_rw [measure_singleton, length_eq_add_of_mem_thinningEvent (Subtype.property _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The binomial multiplicity cancels the factorial of the total length.
Only positive factorials are divided out, so the identity includes time zero. -/
lemma choose_mul_weight_sum (t : ℝ≥0) (m n : ℕ) :
    (Nat.choose (m + n) m : ℝ) * weight (ι ⊕ κ) t (m + n) =
      weight ι t m * weight κ t n := by
  have hfactorial : (Nat.choose (m + n) m : ℝ) * (m ! : ℝ) * (n ! : ℝ) =
      ((m + n)! : ℝ) := by
    exact_mod_cast (by
      rw [Nat.choose_symm_add]
      exact Nat.add_choose_mul_factorial_mul_factorial m n :
      Nat.choose (m + n) m * m ! * n ! = (m + n)!)
  have hm : (m ! : ℝ) ≠ 0 := by positivity
  have hn : (n ! : ℝ) ≠ 0 := by positivity
  have hmn : ((m + n)! : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp (-(Fintype.card (ι ⊕ κ) : ℝ) * t) =
      Real.exp (-(Fintype.card ι : ℝ) * t) *
        Real.exp (-(Fintype.card κ : ℝ) * t) := by
    rw [Fintype.card_sum, Nat.cast_add, neg_add, add_mul, Real.exp_add]
  rw [weight, weight, weight, hexp, pow_add, div_mul_div_comm]
  apply (eq_div_iff (mul_ne_zero hm hn)).2
  calc
    _ = (Real.exp (-(Fintype.card ι : ℝ) * t) *
          Real.exp (-(Fintype.card κ : ℝ) * t) * ((t : ℝ) ^ m * (t : ℝ) ^ n)) *
        ((Nat.choose (m + n) m : ℝ) * (m ! : ℝ) * (n ! : ℝ) /
          ((m + n)! : ℝ)) := by ring
    _ = _ := by rw [hfactorial, div_self hmn, mul_one]; ring

/-- Prescribing both filtered words has the product of their individual masses. -/
lemma measure_thinningEvent_eq_mul (t : ℝ≥0) (u : Word ι) (v : Word κ) :
    measure (ι ⊕ κ) t (thinningEvent u v) = measure ι t {u} * measure κ t {v} := by
  rw [measure_thinningEvent, card_thinningFiber, measure_singleton, measure_singleton,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    choose_mul_weight_sum, ENNReal.ofReal_mul (weight_nonneg t _)]

/-- The two ordered subwords of the same Poissonized word have the product law.
Supporting discrete characterization for amplification, lines 49–54 and 237–253. -/
theorem map_leftWord_rightWord (t : ℝ≥0) :
    (measure (ι ⊕ κ) t).map (fun w ↦ (leftWord w, rightWord w)) =
      (measure ι t).prod (measure κ t) := by
  apply Measure.ext_of_singleton
  rintro ⟨u, v⟩
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _)]
  conv_rhs => rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq,
    thinningEvent] using
    measure_thinningEvent_eq_mul t u v

/-- Retaining the left alphabet preserves its Poissonized ordered-word law. -/
lemma map_leftWord (t : ℝ≥0) :
    (measure (ι ⊕ κ) t).map leftWord = measure ι t := by
  change (measure (ι ⊕ κ) t).map
    (Prod.fst ∘ fun w ↦ (leftWord w, rightWord w)) = _
  rw [← Measure.map_map measurable_fst Measurable.of_discrete,
    map_leftWord_rightWord, Measure.map_fst_prod, measure_univ, one_smul]

/-- Retaining the right alphabet preserves its Poissonized ordered-word law. -/
lemma map_rightWord (t : ℝ≥0) :
    (measure (ι ⊕ κ) t).map rightWord = measure κ t := by
  change (measure (ι ⊕ κ) t).map
    (Prod.snd ∘ fun w ↦ (leftWord w, rightWord w)) = _
  rw [← Measure.map_map measurable_snd Measurable.of_discrete,
    map_leftWord_rightWord, Measure.map_snd_prod, measure_univ, one_smul]

/-- The retained and omitted ordered words from one full sample are independent. -/
theorem indepFun_leftWord_rightWord (t : ℝ≥0) :
    ProbabilityTheory.IndepFun (leftWord (ι := ι) (κ := κ)) rightWord
      (measure (ι ⊕ κ) t) := by
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable).2
  rw [map_leftWord_rightWord, map_leftWord, map_rightWord]

end PoissonWord
