/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PureMarginalRank
import QICLean.Channel.MarginalRank
import QICLean.Entropy.FiniteProduct
import QICLean.Entropy.LocalLift

/-!
# Ranks of reduced matrices on complementary and disjoint regions

Complementary regions of a pure state have equal rank. On a disjoint union,
the rank is at most the product of the ranks of the two regional reductions.
These facts require no normalization or nonempty-region assumptions.
-/

open scoped ComplexOrder

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)]

/-- Complementary reductions of a pure state have equal rank. -/
theorem rank_reducedPure_compl (ψ : EuclideanSpace ℂ ((v : V) → β v)) (R : Finset V) :
    (reducedPure β ψ Rᶜ).rank = (reducedPure β ψ R).rank := by
  rw [reducedPure_compl_eq_partialTraceLeft, reducedPure_eq_partialTrace]
  exact (Matrix.rank_partialTraceRight_vecMulVec_eq_rank_partialTraceLeft _).symm

/-- The rank on a disjoint union is bounded by the product of the regional ranks. -/
theorem rank_reducedMatrix_union_le
    {ρ : Matrix ((v : V) → β v) ((v : V) → β v) ℂ} (hρ : ρ.PosSemidef)
    (R T : Finset V) (h : Disjoint R T) :
    (reducedMatrix β ρ (R ∪ T)).rank ≤
      (reducedMatrix β ρ R).rank * (reducedMatrix β ρ T).rank := by
  classical
  have hb := ((reducedMatrix_posSemidef β hρ (R ∪ T)).submatrix
    (unionEquiv β R T h).symm).rank_le_rank_partialTraceRight_mul_rank_partialTraceLeft
  simpa only [Matrix.rank_submatrix, partialTraceRight_reducedMatrix_union,
    partialTraceLeft_reducedMatrix_union] using hb

end FiniteProduct

namespace Entropy

/-- The regional pure-state matrix agrees with finite-product reduction. -/
theorem regionState_eq_reducedPure {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ : EuclideanSpace ℂ (SiteConfig n)) (R : Finset V) :
    regionState R ψ = FiniteProduct.reducedPure (fun v ↦ Fin (n v)) ψ R := by
  ext a b
  exact (FiniteProduct.complementEquiv (fun v ↦ Fin (n v)) R).sum_comp
    (fun c ↦ ψ ((FiniteProduct.splitEquiv (fun v ↦ Fin (n v)) R).symm (a, c)) *
      star (ψ ((FiniteProduct.splitEquiv (fun v ↦ Fin (n v)) R).symm (b, c))))

/-- Complementary regions of a pure state have equal reduced-matrix ranks. -/
theorem rank_regionState_compl {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ : EuclideanSpace ℂ (SiteConfig n)) (R : Finset V) :
    (regionState Rᶜ ψ).rank = (regionState R ψ).rank := by
  simp only [regionState_eq_reducedPure, FiniteProduct.rank_reducedPure_compl]

/-- The rank on a disjoint union is at most the product of the regional ranks. -/
theorem rank_regionState_union_le {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ : EuclideanSpace ℂ (SiteConfig n)) (R T : Finset V)
    (h : Disjoint R T) :
    (regionState (R ∪ T) ψ).rank ≤ (regionState R ψ).rank * (regionState T ψ).rank := by
  simp only [regionState_eq_reducedPure, FiniteProduct.reducedPure]
  exact FiniteProduct.rank_reducedMatrix_union_le _
    (Matrix.posSemidef_vecMulVec_self_star _) R T h

/-- A region between two nested cuts has rank bounded by the product of the cut ranks. -/
theorem rank_regionState_sdiff_le {V : Type*} [Fintype V] [DecidableEq V]
    {n : V → ℕ} (ψ : EuclideanSpace ℂ (SiteConfig n)) {R T : Finset V}
    (h : R ⊆ T) :
    (regionState (T \ R) ψ).rank ≤ (regionState R ψ).rank * (regionState T ψ).rank := by
  have heq : (T \ R)ᶜ = R ∪ Tᶜ := by
    ext v
    simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [← rank_regionState_compl ψ (T \ R), heq]
  simpa only [rank_regionState_compl] using
    rank_regionState_union_le ψ R Tᶜ (disjoint_compl_right_iff.mpr h)

end Entropy
