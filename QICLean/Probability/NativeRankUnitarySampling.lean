/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.RankUnitaryUniformSampling
import QICLean.Analysis.ViableSubspaceTensorProjectionMeasurable
import QICLean.Analysis.ViableSubspaceTensorTransport

/-!
# Uniform Haar sampling in prescribed physical coordinates

The actual orthogonal projection of a native input subspace is relabeled
in a fixed finite coordinate chart. Sampling its canonical range and
transporting back preserves the uniform failure estimate, with the full
exterior target transported by the same tensor isometry. No assertion
about a varying arbitrary choice of orthonormal basis is used.

This is an auxiliary to ALVV, arXiv:1602.08828v2, Definition `d:vs`,
lines 433–440, Lemma `l:rs`, lines 530–558, and the merge analysis,
lines 1777–1817. **Local fix (complex sphere net count):** The estimate
retains the corrected complex sphere-net exponent documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

open MeasureTheory
open scoped TensorProduct Matrix.Norms.L2Operator

namespace Submodule

variable {σ F : Type*} [Fintype σ] [DecidableEq σ]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {d : ℕ}

private theorem range_projectionMatrix_reindex (e : Fin d ≃ σ)
    (W : Submodule ℂ (EuclideanSpace ℂ σ)) :
    LinearMap.range (Matrix.toEuclideanLin
      (((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm W.starProjection).reindex
        e.symm e.symm)) =
      W.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.toLinearMap := by
  have hprojection := projectionMatrix_map_piLpCongrLeft e.symm W
  rw [← hprojection]
  let Wfin := W.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).toLinearMap
  let C := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
  change LinearMap.range (C (C.symm Wfin.starProjection)).toLinearMap = _
  rw [StarAlgEquiv.apply_symm_apply, range_starProjection,
    LinearIsometryEquiv.piLpCongrLeft_symm]

/-- The literal native canonical sample has the common overlap and failure
bound, with one sample size chosen before the actual native input and full
exterior target. The input's finite-dimensional bound and viability are
mathematical hypotheses, not probability or measurability assumptions.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558,
and the merge analysis, lines 1777–1817. -/
theorem rankUnitaryHaar_not_isViable_native_randomRangeSubspace_uniform_le
    (e : Fin d ≃ σ) {D r : ℕ} (hD : 2 ≤ D) (hr : 1 ≤ r)
    {beta : ℝ} (hbeta : 0 < beta) (hbeta1 : beta ≤ 1) :
    let A := 1 + Real.log (r : ℝ) + Real.log (D : ℝ) + Real.log (1 / beta)
    let s := Nat.ceil (4096 * (r : ℝ) * A)
    1 ≤ s ∧ (s : ℝ) ≤ 4097 * (r : ℝ) * A ∧
      ∀ W : Submodule ℂ (EuclideanSpace ℂ σ),
        Module.finrank ℂ W ≤ D ^ 12 * s ^ 6 →
        ∀ T : Submodule ℂ (EuclideanSpace ℂ σ ⊗[ℂ] F),
          Module.finrank ℂ T ≤ r → IsViable (1 / 4) W T →
          Matrix.rankUnitaryHaar d
            {U | ¬IsViable (1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
              ((Matrix.randomRangeSubspace
                (((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm W.starProjection).reindex
                  e.symm e.symm) s U).map
                    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearMap) T} ≤
              ENNReal.ofReal beta := by
  intro A s
  obtain ⟨hs, hsize, hprob⟩ :=
    Matrix.rankUnitaryHaar_not_isViable_randomRangeSubspace_uniform_le
      (F := F) hD hr hbeta hbeta1
  refine ⟨hs, hsize, ?_⟩
  intro W hW T hTdim hT
  let I := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  let J := TensorProduct.congrIsometry I.symm (LinearIsometryEquiv.refl ℂ F)
  let P := ((Matrix.toEuclideanCLM (n := σ) (𝕜 := ℂ)).symm W.starProjection).reindex
    e.symm e.symm
  have hrange : LinearMap.range (Matrix.toEuclideanLin P) = W.map I.symm.toLinearMap :=
    range_projectionMatrix_reindex e W
  have hPrank : P.rank = Module.finrank ℂ W := by
    have hdim := Module.finrank_eq_card_basis (Matrix.rangeOrthonormalBasis ⟨P, rfl⟩).toBasis
    rw [hrange, I.symm.toLinearEquiv.finrank_map_eq] at hdim
    simpa only [Fintype.card_fin] using hdim.symm
  have hTfin : IsViable (1 / 4) (LinearMap.range (Matrix.toEuclideanLin P))
      (T.map J.toLinearMap) := by
    rw [hrange]
    exact (isViable_map_congrIsometry_iff I.symm (LinearIsometryEquiv.refl ℂ F) W T).mpr hT
  have htargetdim : Module.finrank ℂ (T.map J.toLinearMap) ≤ r := by
    rw [J.toLinearEquiv.finrank_map_eq]
    exact hTdim
  have hfailure := hprob d P (hPrank.symm ▸ hW) (T.map J.toLinearMap) htargetdim hTfin
  have hsample (U : Matrix.rankUnitaryProduct d) :
      IsViable (1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
        ((Matrix.randomRangeSubspace P s U).map I.toLinearMap) T ↔
      IsViable (1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
        (Matrix.randomRangeSubspace P s U) (T.map J.toLinearMap) := by
    have h := isViable_map_congrIsometry_iff I.symm (LinearIsometryEquiv.refl ℂ F)
      (delta := 1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
      ((Matrix.randomRangeSubspace P s U).map I.toLinearMap) T
    simpa only [← map_comp, LinearIsometryEquiv.toLinearEquiv_symm,
      LinearEquiv.symm_comp, map_id] using h.symm
  calc
    _ ≤ Matrix.rankUnitaryHaar d
        {U | ¬IsViable (1 - 3 / (32 * ((D : ℝ) ^ 12 * (s : ℝ) ^ 5)))
          (Matrix.randomRangeSubspace P s U) (T.map J.toLinearMap)} := by
      apply measure_mono
      intro U hbad hgood
      exact hbad ((hsample U).mpr hgood)
    _ ≤ _ := hfailure

end Submodule
