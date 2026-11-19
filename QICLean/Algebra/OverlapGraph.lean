/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Lattice.Basic

/-!
# The overlap graph of a family of supports

For a family `T : κ → Finset S` of supports, two distinct indices are adjacent in
`SimpleGraph.overlapGraph T` when their supports meet. The graph carries no structure of the
sites: it is used both by the cluster expansion, where the clusters of a word of terms are its
connected components in this graph (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1096–1101), and by product-formula circuits, whose layers are the colour classes of a
colouring of it.

## Main definitions and results

* `SimpleGraph.overlapGraph T` — distinct indices are adjacent when their supports meet.
* `SimpleGraph.overlapGraph_adj`, `SimpleGraph.overlapGraph_adj_iff_not_disjoint`.
* `SimpleGraph.Coloring.disjoint_of_overlapGraph` — distinct indices of one colour have disjoint
  supports.
-/

namespace SimpleGraph

open Finset

variable {κ S : Type*} [DecidableEq S]

/-- The overlap graph of a family of supports: two distinct indices are adjacent when their
supports meet. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1096–1101. -/
def overlapGraph (T : κ → Finset S) : SimpleGraph κ where
  Adj i j := i ≠ j ∧ (T i ∩ T j).Nonempty
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, by rw [inter_comm]; exact h.2⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

instance [DecidableEq κ] (T : κ → Finset S) : DecidableRel (overlapGraph T).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

variable {T : κ → Finset S} {k l : κ}

theorem overlapGraph_adj : (overlapGraph T).Adj k l ↔ k ≠ l ∧ (T k ∩ T l).Nonempty :=
  Iff.rfl

theorem overlapGraph_adj_iff_not_disjoint :
    (overlapGraph T).Adj k l ↔ k ≠ l ∧ ¬Disjoint (T k) (T l) := by
  rw [overlapGraph_adj, not_disjoint_iff_nonempty_inter]

/-- Distinct indices of one colour of a colouring of the overlap graph have disjoint
supports. -/
theorem Coloring.disjoint_of_overlapGraph {α : Type*} (c : (overlapGraph T).Coloring α)
    (hkl : k ≠ l) (h : c k = c l) : Disjoint (T k) (T l) := by
  by_contra hd
  exact c.valid (overlapGraph_adj_iff_not_disjoint.mpr ⟨hkl, hd⟩) h

end SimpleGraph
