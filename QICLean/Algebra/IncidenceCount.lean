/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sets of bounded degree meeting a given set

If every point lies in at most `g` of the sets `D i`, `i ∈ s`, then at most `g |S|` of them
meet a set `S`: each such set contains a point of `S`, and each point of `S` lies in at most
`g` of them.

Moved from TNLean, `TNLean/Lattice/BoundedDegreeImaginaryTime.lean` at commit `e41c3b63`.

## Main results

* `Finset.card_filter_not_disjoint_le` — the count of the sets meeting `S`.

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, proof of Lemma `lem:Hadamard-bound`,
  `low70.tex`, lines 860–868.
-/

namespace Finset

variable {ι V : Type*} [DecidableEq V]

/-- If every point lies in at most `g` of the sets `D i`, `i ∈ s`, then at most `g |S|` of
these sets meet `S`. AKL14, arXiv:1406.3898, proof of `lem:Hadamard-bound`, `low70.tex`,
lines 860–868. -/
theorem card_filter_not_disjoint_le {s : Finset ι} (D : ι → Finset V) {g : ℕ}
    (hg : ∀ x : V, (s.filter fun i ↦ x ∈ D i).card ≤ g) (S : Finset V) :
    (s.filter fun i ↦ ¬Disjoint (D i) S).card ≤ g * S.card := by
  classical
  calc
    (s.filter fun i ↦ ¬Disjoint (D i) S).card ≤
        (S.biUnion fun x ↦ s.filter fun i ↦ x ∈ D i).card := by
      apply Finset.card_le_card
      intro i hi
      obtain ⟨his, hd⟩ := Finset.mem_filter.mp hi
      obtain ⟨x, hxD, hxS⟩ := Finset.not_disjoint_iff.mp hd
      exact Finset.mem_biUnion.mpr ⟨x, hxS, Finset.mem_filter.mpr ⟨his, hxD⟩⟩
    _ ≤ ∑ x ∈ S, (s.filter fun i ↦ x ∈ D i).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ S, g := Finset.sum_le_sum fun x _ ↦ hg x
    _ = g * S.card := by simp [mul_comm]

end Finset
