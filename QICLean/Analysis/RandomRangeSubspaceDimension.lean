/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.VariableRankSampleProjection

/-!
# The exact dimension of the canonical range sample

The existing canonical range sampler retains exactly min(s,rank P)
independent orthonormal coordinates. Any linear image of that actual
sample has dimension at most s, for every seed, including rank zero.
This is the deterministic dimension assertion in ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558.
-/

namespace Matrix

/-- The actual canonical sample has exactly the retained coordinate count. -/
theorem finrank_randomRangeSubspace {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (s : ℕ) (U : rankUnitaryProduct d) :
    Module.finrank ℂ (randomRangeSubspace P s U) = min s P.rank := by
  change Module.finrank ℂ (Submodule.randomSubspace (rangeOrthonormalBasis ⟨P, rfl⟩)
    (Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s P.rank)))
      (U ⟨P.rank, Nat.lt_succ_of_le P.rank_le_width⟩)) = _
  rw [Submodule.finrank_randomSubspace]
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Every linear image of the actual canonical sample has dimension at
most the nominal sample bound, without any viability condition. -/
theorem finrank_map_randomRangeSubspace_le {d : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] (P : Matrix (Fin d) (Fin d) ℂ)
    (s : ℕ) (U : rankUnitaryProduct d) (f : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E) :
    Module.finrank ℂ ((randomRangeSubspace P s U).map f) ≤ s :=
  (Submodule.finrank_map_le _ _).trans ((finrank_randomRangeSubspace P s U).le.trans
    (Nat.min_le_left s P.rank))

end Matrix
