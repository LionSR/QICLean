/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.AGSPFavorableEntropy
import QICLean.Entropy.FilterPrefix

/-!
# Regional entropy under a favorable approximate-projection tradeoff

Let an operator on a finite tensor product fix a unit vector and contract its
orthogonal complement, with squared-norm shrinking factor δ. If its
operator-Schmidt rank across a region is at most D and Dδ ≤ 1/2, then the
entropy of the original vector on that region is at most 4 log D.

The operator and vector are given in the original site coordinates. Their
fixed-vector equation, orthogonality and shrinking estimate are transported
through the canonical configuration splitting. The reduced state is the
partial trace of that same vector, without a separate matching hypothesis.

## References

AKLV, arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`), Corollary 2.4
(`col:half`, `eq:AL`), lines 296–361. This is the invariant-line consequence
of the favorable-tradeoff theorem; no Hamiltonian or geometric assumption
is needed for the coordinate transport.
-/

open scoped Matrix InnerProductSpace ComplexOrder

namespace Entropy

/-- The regional entropy of a fixed unit vector is at most four times the
logarithm of an operator-Schmidt-rank bound across the region, provided the
rank bound times the squared-norm shrinking factor is at most one half.
All fixed-vector and orthogonal-complement hypotheses refer to the original
site coordinates. Source: AKLV, arXiv:1301.1162v1, `def:AGSP`, `col:half`,
lines 296–361, in the invariant-line setting. -/
theorem regionEntropy_le_four_log_of_cutOperatorSchmidtRank
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (A : Finset V)
    (K : Matrix (Entropy.SiteConfig n) (Entropy.SiteConfig n) ℂ)
    (Ω : EuclideanSpace ℂ (Entropy.SiteConfig n))
    (hΩ : ‖Ω‖ = 1)
    (hfix : Matrix.toEuclideanLin K Ω = Ω)
    {D : ℕ} {δ : ℝ}
    (hperp : ∀ ψ : EuclideanSpace ℂ (Entropy.SiteConfig n),
      ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
        ⟪Ω, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank (Entropy.cutOperator A K) ≤ D)
    (htradeoff : (D : ℝ) * δ ≤ 1 / 2) :
    Entropy.regionEntropy A Ω ≤ 4 * Real.log (D : ℝ) := by
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Entropy.cutEquiv n A)
  have hU (x : EuclideanSpace ℂ (Entropy.SiteConfig n)) :
      U x = Entropy.cutVector A x := by
    ext z
    rfl
  have hintertwine (x : EuclideanSpace ℂ (Entropy.SiteConfig n)) :
      Matrix.toEuclideanLin (Entropy.cutOperator A K) (U x) =
        U (Matrix.toEuclideanLin K x) := by
    simpa only [hU] using (Entropy.cutVector_toEuclideanLin A K x).symm
  have hbound := Matrix.vonNeumannEntropy_reduced_le_four_log_of_operatorSchmidtRank
    (Entropy.cutOperator A K) (U Ω) ((U.norm_map Ω).trans hΩ)
    ((hintertwine Ω).trans (congrArg U hfix))
    (fun ψ hψ horth ↦ by
      obtain ⟨horthK, hnormK⟩ := hperp (U.symm ψ)
        ((U.symm.norm_map ψ).trans hψ)
        ((U.inner_map_eq_flip Ω ψ).symm.trans horth)
      have hKψ : Matrix.toEuclideanLin (Entropy.cutOperator A K) ψ =
          U (Matrix.toEuclideanLin K (U.symm ψ)) := by
        simpa only [U.apply_symm_apply] using hintertwine (U.symm ψ)
      constructor
      · simpa only [hKψ, U.inner_map_map] using horthK
      · simpa only [hKψ, U.norm_map] using hnormK)
    hrank htradeoff
  rw [Subsingleton.elim
    (fun a b : Entropy.RegionConfig n A ↦ Classical.propDecidable (a = b))
    (inferInstance : DecidableEq (Entropy.RegionConfig n A))] at hbound
  let C := Matrix.schmidtCoeffMatrix (WithLp.ofLp (U Ω))
  have hρ : Entropy.regionState A Ω = C * Cᴴ := by
    simpa only [Entropy.regionState, C, hU] using
      Matrix.partialTraceRight_vecMulVec_eq (WithLp.ofLp (Entropy.cutVector A Ω))
  have hS : Entropy.regionEntropy A Ω =
      vonNeumannEntropy (C * Cᴴ) (Matrix.posSemidef_self_mul_conjTranspose C).isHermitian :=
    vonNeumannEntropy_congr hρ _ _
  exact hS.le.trans hbound

end Entropy
