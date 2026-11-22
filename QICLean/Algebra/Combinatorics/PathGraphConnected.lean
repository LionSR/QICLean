/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.SuccPred.Archimedean

/-!
# Connected vertex sets of the path graph

A vertex set of the path graph on `Fin N` induces a connected subgraph exactly when it is a
nonempty order interval, and a nonempty interval is determined by its endpoints. These are the
one-dimensional geometry of the cluster expansion on a chain, where the clusters of terms
on consecutive bonds are intervals of labels (ALVV, arXiv:1602.08828v2, `thm:cluster-approx`).

## Main results

* `SimpleGraph.ordConnected_of_pathGraph_connected`.
* `SimpleGraph.pathGraph_connected_of_ordConnected`.
* `SimpleGraph.eq_Icc_of_ordConnected`.

Moved from `QICLean/Analysis/ClusterExpansion/Path.lean`, namespace `ClusterExpansion`, and
from TNLean (`e113e005`) `TNLean/Lattice/ClusterExpansion/PathIntervals.lean` before that.
Changes: namespace `SimpleGraph`.
-/

open Finset

namespace SimpleGraph

variable {N : ℕ}

/-- A connected vertex set of the path graph contains every vertex between two of its
vertices. This is the one-dimensional geometry used in the corrected interaction-label
version of ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem ordConnected_of_pathGraph_connected {C : Finset (Fin N)}
    (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected) :
    (C : Set (Fin N)).OrdConnected := by
  refine ⟨fun a ha b hb k hk ↦ ?_⟩
  by_contra hkC
  have key : ∀ (u v : (C : Set (Fin N))), ((pathGraph N).induce (C : Set (Fin N))).Walk u v →
      (u : Fin N).val < k.val → (v : Fin N).val < k.val := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u w v hadj p ih =>
      intro hu
      apply ih
      have hw : (w : Fin N).val ≠ k.val := fun heq ↦ hkC (Fin.ext heq ▸ w.property)
      have hadj' : (u : Fin N).val + 1 = (w : Fin N).val ∨
          (w : Fin N).val + 1 = (u : Fin N).val := pathGraph_adj.mp hadj
      omega
  have ha_ne : a.val ≠ k.val := fun heq ↦ hkC (Fin.ext heq ▸ ha)
  obtain ⟨p⟩ := hC.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  exact (not_lt_of_ge hk.2) (key _ _ p (lt_of_le_of_ne hk.1 ha_ne))

/-- Every nonempty interval of vertices is connected in the path graph.
Auxiliary to ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem pathGraph_connected_of_ordConnected {C : Finset (Fin N)}
    (hC : (C : Set (Fin N)).OrdConnected) (hne : C.Nonempty) :
    ((pathGraph N).induce (C : Set (Fin N))).Connected := by
  let := hC
  have hcov : (Set.range (OrderEmbedding.subtype (· ∈ (C : Set (Fin N))))).OrdConnected := by
    simpa using hC
  have heq : (pathGraph N).induce (C : Set (Fin N)) = hasse (C : Set (Fin N)) := by
    ext u v
    change ((u : Fin N) ⋖ (v : Fin N) ∨ (v : Fin N) ⋖ (u : Fin N)) ↔ (u ⋖ v ∨ v ⋖ u)
    exact or_congr
      (Set.OrdConnected.apply_covBy_apply_iff
        (OrderEmbedding.subtype (· ∈ (C : Set (Fin N)))) hcov)
      (Set.OrdConnected.apply_covBy_apply_iff
        (OrderEmbedding.subtype (· ∈ (C : Set (Fin N)))) hcov)
  rw [heq]
  have : Nonempty (C : Set (Fin N)) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  exact ⟨preconnected_hasse_of_succOrder _⟩

/-- A nonempty interval is determined by its endpoints. Auxiliary to the interaction-label
geometry in ALVV, arXiv:1602.08828v2, `thm:cluster-approx`. -/
theorem eq_Icc_of_ordConnected {C : Finset (Fin N)}
    (hC : (C : Set (Fin N)).OrdConnected) (hne : C.Nonempty) :
    C = Icc (C.min' hne) (C.max' hne) := by
  ext k
  exact ⟨fun hk ↦ mem_Icc.mpr ⟨C.min'_le k hk, C.le_max' k hk⟩,
    fun hk ↦ hC.out' (C.min'_mem hne) (C.max'_mem hne) (mem_Icc.mp hk)⟩

end SimpleGraph
