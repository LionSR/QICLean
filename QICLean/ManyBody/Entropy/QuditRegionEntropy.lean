/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.ManyBody.Sites.RegionState
import QICLean.Entropy.VonNeumann.Entropy

/-!
# Regional entropies with one local dimension

A fact about a system of sites `V` with the same local dimension `q` at every site, which the
regional entropy inequalities of `QICLean.ManyBody.Entropy.RegionEntropyInequalities` do not
contain: for `q = 1` every region of a unit vector has zero entropy. The statement uses no
geometry of `V`.

Moved from TNLean, `TNLean/Lattice/RegionEntropyInequalities.lean`. Changes: namespace
`ManyBody` in place of `TNLean.Lattice`.

## Main results

* `ManyBody.regionEntropy_eq_zero_of_localDimension_one`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 2 (`sec:prelim`), `01-preliminaries.tex`, line 116.
-/

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every region of a unit vector on one-dimensional local spaces has zero entropy: the
regional state has trace one on a one-dimensional configuration space, so its rank is at
most one. Area law, `01-preliminaries.tex`, line 116. -/
theorem regionEntropy_eq_zero_of_localDimension_one
    {Ω : EuclideanSpace ℂ (V → Fin 1)} (hΩ : ‖Ω‖ = 1) (A : Finset V) :
    regionEntropy (X := fun _ ↦ Fin 1) Ω A = 0 := by
  apply vonNeumannEntropy_eq_zero_of_rank_le_one (regionState_posSemidef A Ω)
    (trace_regionState_eq_one hΩ)
  exact (Matrix.rank_le_card_width _).trans_eq (by simp [RegionConfig])

end ManyBody
