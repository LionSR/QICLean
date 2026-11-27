/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWord.Relabel
import QICLean.Probability.PoissonWord.Thinning
import Mathlib.Logic.Equiv.Sum
import QICLean.Probability.PoissonWord.PoissonWordAppend
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Splitting actual Poisson words by a predicate

Classify every original letter by a decidable predicate, then preserve its
order within the selected or complementary word. The two words have the
independent Poissonized laws on the corresponding subtype alphabets. The
construction uses the same full-word sample; no coupling law is assumed.

It also contains the following results.

* `PoissonWord.foldl_sub_partitionWords_fst_eq_sum`: a deterministic comparison of full and retained
  chronological products.

## Main results

* `PoissonWord.norm_foldl_sub_partitionWords_fst_le_sum`: A norm bound for omitted chronological
  maps.
-/

section Partition

section Partition

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

end Partition

section PoissonWordTelescope

/-!
## A deterministic comparison of full and retained chronological products

For an ordered list of letters, its chronological action applies the first
map first and the last map last. A retention predicate selects a subsequence
without changing its order. The difference between the full and retained
actions is a sum over omitted occurrences. At each such occurrence, its
single-map defect acts on the earlier retained action, and every later map
then acts on that defect.

The retained prefix and the full suffix are taken from the same original
word. The identity is algebraic and holds for arbitrary linear maps.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `09-amplification.tex`, lines 203–209, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The identity is the deterministic telescope preceding the expected-norm
omission estimate; it does not assert the spatial estimate or a clock law.
-/

open scoped BigOperators

namespace PoissonWord

variable {ι 𝕜 V : Type*} [Semiring 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The full chronological action minus the action of the retained subsequence
is the sum of omitted-letter defects. Each defect acts on the actual retained
prefix and is followed by the actual full suffix. The maps and the initial
vector are arbitrary; no contraction or independence assumption is imposed.
Auxiliary to `09-amplification.tex`, lines 203–209. -/
theorem foldl_sub_partitionWords_fst_eq_sum
    (E : ι → V →ₗ[𝕜] V) (p : ι → Prop) [DecidablePred p]
    (w : Word ι) (x : V) :
    let act : List ι → V → V :=
      fun xs z ↦ xs.foldl (fun v i ↦ E i v) z
    let retained : Word ι → V :=
      fun u ↦ act ((List.ofFn (partitionWords p u).1.2).map Subtype.val) x
    act (List.ofFn w.2) x - retained w =
      ∑ j : Fin w.1,
        if p (w.2 j) then 0 else
          act (List.ofFn (drop w (j + 1)).2)
            (E (w.2 j) (retained (take w j)) - retained (take w j)) := by
  rcases w with ⟨m, w⟩
  have hsub (xs : List ι) (a b : V) :
      xs.foldl (fun v i ↦ E i v) (a - b) =
        xs.foldl (fun v i ↦ E i v) a - xs.foldl (fun v i ↦ E i v) b :=
    List.foldl_hom₂ xs (fun a b : V ↦ a - b)
      (fun v i ↦ E i v) (fun v i ↦ E i v) (fun v i ↦ E i v)
      a b (fun a b i ↦ ((E i).map_sub a b).symm)
  let act : List ι → V → V := fun xs z ↦ xs.foldl (fun v i ↦ E i v) z
  let retained : Word ι → V :=
    fun u ↦ act ((List.ofFn (partitionWords p u).1.2).map Subtype.val) x
  let H : ℕ → V := fun j ↦
    act (List.ofFn (drop (⟨m, w⟩ : Word ι) j).2)
      (retained (take (⟨m, w⟩ : Word ι) j))
  have ht : (∑ j : Fin m, (H j - H ((j : ℕ) + 1))) = H 0 - H m := by
    simpa only [Finset.sum_range] using (Finset.sum_range_sub' H m)
  have hstep (j : Fin m) :
      H j - H ((j : ℕ) + 1) =
        if p (w j) then 0 else
          act (List.ofFn (drop (⟨m, w⟩ : Word ι) ((j : ℕ) + 1)).2)
            (E (w j) (retained (take (⟨m, w⟩ : Word ι) j)) -
              retained (take (⟨m, w⟩ : Word ι) j)) := by
    have hj : (j : ℕ) < (List.ofFn w).length := by
      simpa only [List.length_ofFn] using j.isLt
    simp only [H, retained, ofFn_partitionWords_fst, ofFn_take, ofFn_drop]
    rw [List.drop_eq_getElem_cons hj, List.take_succ_eq_append_getElem hj]
    simp only [act, List.getElem_ofFn, List.filter_append, List.filter_singleton,
      List.foldl_cons, List.foldl_append]
    by_cases hp : p (w j) <;> simp [hp, hsub]
  have h0 : H 0 = act (List.ofFn w) x := by
    simp only [H, retained, ofFn_partitionWords_fst, ofFn_take, ofFn_drop]
    simp [act]
  have hm : H m = retained (⟨m, w⟩ : Word ι) := by
    simp only [H, retained, ofFn_partitionWords_fst, ofFn_take, ofFn_drop]
    simp [act, List.drop_of_length_le, List.take_of_length_le]
  change act (List.ofFn w) x - retained (⟨m, w⟩ : Word ι) = _
  rw [← h0, ← hm, ← ht]
  exact Finset.sum_congr rfl (fun j _ ↦ hstep j)

end PoissonWord

end PoissonWordTelescope

end Partition

section PoissonWordOmissionBound

/-!
## A norm bound for omitted chronological maps

Contractive linear maps preserve the norm bound through every full suffix.
The chronological omission identity therefore bounds the discrepancy by the
sum of one-map defects on the actual retained prefixes. The sum counts each
original omitted occurrence separately.

This is the pointwise comparison preceding the expectation estimate in
OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, `09-amplification.tex`, lines 203–209, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace PoissonWord

variable {ι 𝕜 V : Type*} [Semiring 𝕜]
  [SeminormedAddCommGroup V] [Module 𝕜 V]

/-- The discrepancy of full and retained chronological actions is bounded
by the sum of omitted-map defects on the retained prefixes. Auxiliary to
`09-amplification.tex`, lines 203–209. -/
theorem norm_foldl_sub_partitionWords_fst_le_sum
    (E : ι → V →ₗ[𝕜] V) (hE : ∀ i y, ‖E i y‖ ≤ ‖y‖)
    (p : ι → Prop) [DecidablePred p] (w : Word ι) (x : V) :
    let act : List ι → V → V :=
      fun xs y ↦ xs.foldl (fun z i ↦ E i z) y
    let retained : Word ι → V :=
      fun u ↦ act ((List.ofFn (partitionWords p u).1.2).map Subtype.val) x
    ‖act (List.ofFn w.2) x - retained w‖ ≤
      ∑ j : Fin w.1, if p (w.2 j) then 0 else
        ‖E (w.2 j) (retained (take w j)) - retained (take w j)‖ := by
  dsimp only
  have hact (xs : List ι) (y : V) :
      ‖xs.foldl (fun z i ↦ E i z) y‖ ≤ ‖y‖ := by
    exact List.foldlRecOn (motive := fun z : V ↦ ‖z‖ ≤ ‖y‖) xs
      (fun z i ↦ E i z) le_rfl (fun z hz i _ ↦ (hE i z).trans hz)
  rw [foldl_sub_partitionWords_fst_eq_sum E p w x]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro j _
  by_cases hp : p (w.2 j)
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    exact hact _ _

end PoissonWord

end PoissonWordOmissionBound
