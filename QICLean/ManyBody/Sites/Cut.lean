/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Fintype.Basic

/-!
# Supports crossing a cut

A region `B` cuts the sites into `B` and its complement. Given a family of supports
`D : ι → Finset V`, the terms crossing the cut are the indices whose support meets both sides.
Only the supports enter: for an interaction with supports `T`, its crossing terms at `B` are
`crossingTerms T B`.

Moved from `QICLean/Entropy/SupportedMarginalTails.lean`, where it was
`ManyBody.crossingTerms`.

The crossing terms are unchanged by exchanging the region and its complement, and no support
crosses the empty region or the region of all sites.

## Main definitions

* `ManyBody.crossingTerms` — the indices whose support meets a region and its complement.

## Main results

* `ManyBody.mem_crossingTerms` — membership in the crossing terms.
* `ManyBody.crossingTerms_compl` — complementary regions have the same crossing terms.
-/

namespace ManyBody

variable {V ι : Type*} [Fintype ι]

/-- The terms whose support meets both sides of the cut at `B`: the indices `i` such that
`D i` contains a site of `B` and a site outside `B`.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, lines 47–48. -/
noncomputable def crossingTerms (D : ι → Finset V) (B : Finset V) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ (∃ v ∈ D i, v ∈ B) ∧ ∃ v ∈ D i, v ∉ B

variable {D : ι → Finset V} {B : Finset V} {i : ι}

theorem mem_crossingTerms : i ∈ crossingTerms D B ↔ (∃ v ∈ D i, v ∈ B) ∧ ∃ v ∈ D i, v ∉ B := by
  classical
  simp only [crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A support inside the region does not cross it. -/
theorem notMem_crossingTerms_of_subset (h : D i ⊆ B) : i ∉ crossingTerms D B := fun hi ↦ by
  obtain ⟨-, _, hv, hvB⟩ := mem_crossingTerms.mp hi
  exact hvB (h hv)

/-- A support disjoint from the region does not cross it. -/
theorem notMem_crossingTerms_of_disjoint (h : Disjoint (D i) B) : i ∉ crossingTerms D B :=
  fun hi ↦ by
    obtain ⟨⟨_, hv, hvB⟩, -⟩ := mem_crossingTerms.mp hi
    exact Finset.disjoint_left.mp h hv hvB

@[simp] theorem crossingTerms_empty : crossingTerms D ∅ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hi ↦ by simp [mem_crossingTerms] at hi

/-- Exchanging a region and its complement preserves the crossing terms. -/
@[simp] theorem crossingTerms_compl [Fintype V] [DecidableEq V] :
    crossingTerms D Bᶜ = crossingTerms D B := by
  ext i
  simp only [mem_crossingTerms, Finset.mem_compl, not_not]
  exact and_comm

@[simp] theorem crossingTerms_univ [Fintype V] : crossingTerms D Finset.univ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hi ↦ by simp [mem_crossingTerms] at hi

end ManyBody
