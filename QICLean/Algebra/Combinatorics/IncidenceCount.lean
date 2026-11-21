/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

/-!
# Sets of bounded degree meeting a given set

If the weights `w i ≥ 0` of the sets `D i`, `i ∈ s`, containing any given point sum to at most
`g`, then the weights of the sets meeting a set `S` sum to at most `g |S|`: each such set
contains a point of `S`, and the sets through each point of `S` have total weight at most `g`.

Moved from TNLean, `TNLean/Lattice/BoundedDegreeImaginaryTime.lean` at commit `e41c3b63`, where
the weights are all `1`; here with arbitrary nonnegative weights, as in the norm-weighted
degree of Arad, Kuwahara and Landau.

## Main results

* `Finset.sum_filter_not_disjoint_le` — the total weight of the sets meeting `S`.

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, proof of Lemma `lem:Hadamard-bound`,
  `low70.tex`, lines 860–868.
-/

namespace Finset

variable {ι V : Type*} [DecidableEq V]

/-- If the weights `w i ≥ 0` of the sets `D i`, `i ∈ s`, through every point sum to at most
`g`, then the weights of the sets meeting `S` sum to at most `g |S|`. AKL14, arXiv:1406.3898,
proof of `lem:Hadamard-bound`, `low70.tex`, lines 860–868. -/
theorem sum_filter_not_disjoint_le {s : Finset ι} (D : ι → Finset V) {w : ι → ℝ}
    (hw : ∀ i, 0 ≤ w i) {g : ℝ} (hg : ∀ x : V, ∑ i ∈ s with x ∈ D i, w i ≤ g)
    (S : Finset V) :
    ∑ i ∈ s with ¬Disjoint (D i) S, w i ≤ g * S.card := by
  classical
  calc
    ∑ i ∈ s with ¬Disjoint (D i) S, w i ≤
        ∑ i ∈ s with ¬Disjoint (D i) S, ∑ x ∈ S, if x ∈ D i then w i else 0 := by
      refine Finset.sum_le_sum fun i hi ↦ ?_
      obtain ⟨x, hxD, hxS⟩ := Finset.not_disjoint_iff.mp (Finset.mem_filter.mp hi).2
      calc
        w i = if x ∈ D i then w i else 0 := (ite_eq_left hxD).symm
        _ ≤ _ := Finset.single_le_sum (f := fun x ↦ if x ∈ D i then w i else 0)
          (fun y _ ↦ by split_ifs <;> simp [hw i]) hxS
    _ = ∑ x ∈ S, ∑ i ∈ s with ¬Disjoint (D i) S, if x ∈ D i then w i else 0 :=
      Finset.sum_comm
    _ ≤ ∑ x ∈ S, ∑ i ∈ s, if x ∈ D i then w i else 0 := by
      refine Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) fun i _ _ ↦ ?_
      split_ifs <;> simp [hw i]
    _ ≤ ∑ _x ∈ S, g := Finset.sum_le_sum fun x _ ↦ by rw [← Finset.sum_filter]; exact hg x
    _ = g * S.card := by simp [mul_comm]

end Finset
