/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.VonNeumann.PureMarginalRank
import QICLean.Channel.PartialTrace.MarginalRank
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Sites.RegionState

/-!
# Ranks of reduced matrices on complementary and disjoint regions

Complementary regions of a pure state have equal rank. On a disjoint union,
the rank is at most the product of the ranks of the two regional reductions.
These facts require no normalization or nonempty-region assumptions.
-/

open scoped ComplexOrder

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)]

/-- Complementary reductions of a pure state have equal rank. -/
theorem rank_regionState_compl (ψ : EuclideanSpace ℂ ((v : V) → β v)) (R : Finset V) :
    (regionState ψ Rᶜ).rank = (regionState ψ R).rank := by
  rw [regionState_compl_eq_partialTraceLeft, Matrix.rank_reindex,
    regionState_eq_partialTraceRight_cutVector]
  exact (Matrix.rank_partialTraceRight_vecMulVec_eq_rank_partialTraceLeft _).symm

/-- The rank on a disjoint union is bounded by the product of the regional ranks. -/
theorem rank_regionMatrix_union_le
    {ρ : Matrix ((v : V) → β v) ((v : V) → β v) ℂ} (hρ : ρ.PosSemidef)
    (R T : Finset V) (h : Disjoint R T) :
    (regionMatrix ρ (R ∪ T)).rank ≤
      (regionMatrix ρ R).rank * (regionMatrix ρ T).rank := by
  classical
  have hb := ((regionMatrix_posSemidef β hρ (R ∪ T)).submatrix
    (regionUnionEquiv (β := β) h).symm).rank_le_rank_partialTraceRight_mul_rank_partialTraceLeft
  simpa only [Matrix.rank_submatrix, partialTraceRight_regionMatrix_union,
    partialTraceLeft_regionMatrix_union] using hb

end ManyBody

namespace Entropy

/-- The rank on a disjoint union is at most the product of the regional ranks. -/
theorem rank_regionState_union_le {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) (R T : Finset V)
    (h : Disjoint R T) :
    (ManyBody.regionState ψ (R ∪ T)).rank ≤ (ManyBody.regionState ψ R).rank *
        (ManyBody.regionState ψ T).rank := by
  simp only [ManyBody.regionState]
  exact ManyBody.rank_regionMatrix_union_le _
    (Matrix.posSemidef_vecMulVec_self_star _) R T h

/-- A region between two nested cuts has rank bounded by the product of the cut ranks. -/
theorem rank_regionState_sdiff_le {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) {R T : Finset V}
    (h : R ⊆ T) :
    (ManyBody.regionState ψ (T \ R)).rank ≤ (ManyBody.regionState ψ R).rank *
        (ManyBody.regionState ψ T).rank := by
  have heq : (T \ R)ᶜ = R ∪ Tᶜ := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [← ManyBody.rank_regionState_compl _ ψ (T \ R), heq]
  simpa only [ManyBody.rank_regionState_compl] using
    rank_regionState_union_le ψ R Tᶜ (disjoint_compl_right_iff.mpr h)

end Entropy
