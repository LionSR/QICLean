/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordPartition
import QICLean.Probability.PoissonWordAppend
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop

/-!
# A deterministic comparison of full and retained chronological products

For an ordered list of letters, its chronological action applies the first
map first and the last map last. A retention predicate selects a subsequence
without changing its order. The difference between the full and retained
actions is a sum over omitted occurrences. At each such occurrence, its
single-map defect acts on the earlier retained action, and every later map
then acts on that defect.

The retained prefix and the full suffix are taken from the same original
word. The identity is algebraic and holds for arbitrary linear maps.

## References

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
