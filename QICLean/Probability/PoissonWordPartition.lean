/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordRelabel
import QICLean.Probability.PoissonWordThinning
import Mathlib.Logic.Equiv.Sum

/-!
# Splitting actual Poisson words by a predicate

Classify every original letter by a decidable predicate, then preserve its
order within the selected or complementary word. The two words have the
independent Poissonized laws on the corresponding subtype alphabets. The
construction uses the same full-word sample; no coupling law is assumed.
-/

open MeasureTheory
open scoped NNReal

namespace PoissonWord

variable {ι : Type*}

/-- Split a word into its selected and complementary letters, preserving order. -/
def partitionWords (p : ι → Prop) [DecidablePred p] (w : Word ι) :
    Word {i // p i} × Word {i // ¬p i} :=
  (leftWord (relabel (Equiv.sumCompl p).symm w),
    rightWord (relabel (Equiv.sumCompl p).symm w))

@[simp] theorem partitionWords_nil (p : ι → Prop) [DecidablePred p] :
    partitionWords p nil = (nil, nil) := by
  simp [partitionWords]

/-- The split preserves all positions, including the empty word. -/
theorem partitionWords_length (p : ι → Prop) [DecidablePred p] (w : Word ι) :
    (partitionWords p w).1.1 + (partitionWords p w).2.1 = w.1 := by
  exact leftWord_length_add_rightWord_length (relabel (Equiv.sumCompl p).symm w)

/-- Forgetting subtype proofs gives exactly the predicate-filtered original letters. -/
theorem ofFn_partitionWords_fst (p : ι → Prop) [DecidablePred p] (w : Word ι) :
    (List.ofFn (partitionWords p w).1.2).map Subtype.val =
      (List.ofFn w.2).filter (fun i => decide (p i)) := by
  have h (xs : List ι) :
      ((xs.map (Equiv.sumCompl p).symm).filterMap Sum.getLeft?).map Subtype.val =
        xs.filter (fun i => decide (p i)) := by
    rw [List.map_filterMap, List.filterMap_map, ← List.filterMap_eq_filter]
    congr 1
    funext i
    by_cases hi : p i <;> simp [Equiv.sumCompl, Option.guard, hi]
  change (List.equivSigmaTuple.symm (List.equivSigmaTuple
    ((List.equivSigmaTuple.symm (relabel (Equiv.sumCompl p).symm w)).filterMap
      Sum.getLeft?))).map Subtype.val = _
  rw [Equiv.symm_apply_apply]
  change ((List.ofFn (fun j => (Equiv.sumCompl p).symm (w.2 j))).filterMap
    Sum.getLeft?).map Subtype.val = _
  rw [List.ofFn_comp']
  exact h (List.ofFn w.2)

/-- The complementary word likewise retains the original order of omitted letters. -/
theorem ofFn_partitionWords_snd (p : ι → Prop) [DecidablePred p] (w : Word ι) :
    (List.ofFn (partitionWords p w).2.2).map Subtype.val =
      (List.ofFn w.2).filter (fun i => decide (¬p i)) := by
  have h (xs : List ι) :
      ((xs.map (Equiv.sumCompl p).symm).filterMap Sum.getRight?).map Subtype.val =
        xs.filter (fun i => decide (¬p i)) := by
    rw [List.map_filterMap, List.filterMap_map, ← List.filterMap_eq_filter]
    congr 1
    funext i
    by_cases hi : p i <;> simp [Equiv.sumCompl, Option.guard, hi]
  change (List.equivSigmaTuple.symm (List.equivSigmaTuple
    ((List.equivSigmaTuple.symm (relabel (Equiv.sumCompl p).symm w)).filterMap
      Sum.getRight?))).map Subtype.val = _
  rw [Equiv.symm_apply_apply]
  change ((List.ofFn (fun j => (Equiv.sumCompl p).symm (w.2 j))).filterMap
    Sum.getRight?).map Subtype.val = _
  rw [List.ofFn_comp']
  exact h (List.ofFn w.2)

/-- An arbitrary predicate split has the product law of its actual subtype alphabets. -/
theorem map_partitionWords [Fintype ι] (p : ι → Prop) [DecidablePred p] (t : ℝ≥0) :
    (measure ι t).map (partitionWords p) =
      (measure {i // p i} t).prod (measure {i // ¬p i} t) := by
  change (measure ι t).map
    ((fun w : Word ({i // p i} ⊕ {i // ¬p i}) => (leftWord w, rightWord w)) ∘
      relabel (Equiv.sumCompl p).symm) = _
  rw [← Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    map_relabel, map_leftWord_rightWord]

/-- The selected ordered word has the concrete selected-alphabet law. -/
theorem map_partitionWords_fst [Fintype ι] (p : ι → Prop) [DecidablePred p] (t : ℝ≥0) :
    (measure ι t).map (fun w => (partitionWords p w).1) = measure {i // p i} t := by
  change (measure ι t).map (Prod.fst ∘ partitionWords p) = _
  rw [← Measure.map_map measurable_fst Measurable.of_discrete,
    map_partitionWords, Measure.map_fst_prod, measure_univ, one_smul]

/-- The omitted ordered word has the concrete complementary-alphabet law. -/
theorem map_partitionWords_snd [Fintype ι] (p : ι → Prop) [DecidablePred p] (t : ℝ≥0) :
    (measure ι t).map (fun w => (partitionWords p w).2) = measure {i // ¬p i} t := by
  change (measure ι t).map (Prod.snd ∘ partitionWords p) = _
  rw [← Measure.map_map measurable_snd Measurable.of_discrete,
    map_partitionWords, Measure.map_snd_prod, measure_univ, one_smul]

/-- The two ordered words obtained from the same full sample are independent. -/
theorem indepFun_partitionWords [Fintype ι] (p : ι → Prop) [DecidablePred p] (t : ℝ≥0) :
    ProbabilityTheory.IndepFun (fun w => (partitionWords p w).1)
      (fun w => (partitionWords p w).2) (measure ι t) := by
  apply (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    Measurable.of_discrete.aemeasurable Measurable.of_discrete.aemeasurable).2
  change (measure ι t).map (partitionWords p) = _
  rw [map_partitionWords, map_partitionWords_fst, map_partitionWords_snd]

end PoissonWord
