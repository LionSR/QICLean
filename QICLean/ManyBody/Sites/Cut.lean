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
`Entropy.crossingTerms`; that name is exported from `Entropy` until step 4.0 of the many-body
plan, so its callers resolve to this definition unchanged.

## Main definitions

* `ManyBody.crossingTerms` — the indices whose support meets a region and its complement.
-/

namespace ManyBody

variable {V ι : Type*} [Fintype ι]

/-- The terms whose support meets both sides of the cut at `B`: the indices `i` such that
`D i` contains a site of `B` and a site outside `B`.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, lines 47–48. -/
noncomputable def crossingTerms (D : ι → Finset V) (B : Finset V) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ (∃ v ∈ D i, v ∈ B) ∧ ∃ v ∈ D i, v ∉ B

end ManyBody
