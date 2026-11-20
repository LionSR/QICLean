/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PureMarginalRank
import QICLean.Channel.MarginalRank
import QICLean.Entropy.RegionEntropy
import QICLean.Entropy.SupportedMarginalTails
import QICLean.Entropy.FilterMoment
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
    (ManyBody.regionState ψ Rᶜ).rank = (ManyBody.regionState ψ R).rank := by
  rw [ManyBody.regionState_compl_eq_partialTraceLeft, ManyBody.regionState_eq_partialTrace]
  exact (Matrix.rank_partialTraceRight_vecMulVec_eq_rank_partialTraceLeft _).symm

/-- The rank on a disjoint union is bounded by the product of the regional ranks. -/
theorem rank_regionMatrix_union_le
    {ρ : Matrix ((v : V) → β v) ((v : V) → β v) ℂ} (hρ : ρ.PosSemidef)
    (R T : Finset V) (h : Disjoint R T) :
    (ManyBody.regionMatrix ρ (R ∪ T)).rank ≤
      (ManyBody.regionMatrix ρ R).rank * (ManyBody.regionMatrix ρ T).rank := by
  classical
  have hb := ((ManyBody.regionMatrix_posSemidef β hρ (R ∪ T)).submatrix
    (ManyBody.unionEquiv β R T h).symm).rank_le_rank_partialTraceRight_mul_rank_partialTraceLeft
  simpa only [Matrix.rank_submatrix, ManyBody.partialTraceRight_regionMatrix_union,
    ManyBody.partialTraceLeft_regionMatrix_union] using hb

end ManyBody

namespace Entropy

/-- Complementary regions of a pure state have equal reduced-matrix ranks. -/
theorem rank_regionState_compl {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) (R : Finset V) :
    (ManyBody.regionState ψ Rᶜ).rank = (ManyBody.regionState ψ R).rank := by
  simp only [ManyBody.rank_regionState_compl]

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
  rw [← rank_regionState_compl ψ (T \ R), heq]
  simpa only [rank_regionState_compl] using
    rank_regionState_union_le ψ R Tᶜ (disjoint_compl_right_iff.mpr h)

end Entropy
