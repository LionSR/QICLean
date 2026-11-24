/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.Law
import QICLean.Circuit.Party.Compression.PhysicalReadout.Separated
import QICLean.Probability.Concentration.WeightedSourceError

/-!
# Expected physical errors of separated sampled sources

Two allowed words `v`, `w` on the affected side, read through a contraction `K` and fed by
contractive frames `F`, `F'`, have a Gram matrix `O` of norm at most one; two allowed exterior
words `v'`, `w'`, read through a contraction `K'` and fed by contractive frames `G`, `G'`,
contract the trace norm. If the complex coefficients `z` have diagonal covariance with scale
`κ` and probability weights, the expected trace norm of the exterior image of the weighted
block combination of `O` is at most `√κ`
(`Word.integral_rectangularTraceNorm_weightedPhysicalSource_le`).
For the products of correction entries of the sampled sources over a set `S` of positions,
`κ = k ^ (-|S|)`, which gives the bound `k ^ (-|S|/2)`
(`SourceCircuit.integral_rectangularTraceNorm_gaussianPhysicalSource_le`); summing over the
affected physical indices gives the bound `d² k ^ (-|S|/2)` on the separated physical density,
`d` the number of affected physical indices
(`SourceCircuit.integrable_gaussianSeparatedPhysicalDensity_and_integral_le`). No input,
private or discarded dimension enters.

This module takes integrals, and is one of the modules of
`Circuit/Party/Compression/SourceSampling` allowed to import `QICLean.Probability`.

## Main results

* `QuantumCircuit.Party.Word.integral_rectangularTraceNorm_weightedPhysicalSource_le`.
* `QuantumCircuit.Party.SourceCircuit.integral_rectangularTraceNorm_gaussianPhysicalSource_le`.
* `QuantumCircuit.Party.SourceCircuit.integrable_gaussianSeparatedPhysicalDensity_and_integral_le`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 435–520 (equations `eq:compression-exterior-input`, `eq:compression-one-choice`).

Adapted from TNLean, `TNLean/Lattice/Compression/WeightedPhysicalSource.lean` (the integral
theorem), `GaussianPhysicalSource.lean` and `GaussianSeparatedPhysicalDensity.lean`
(Apache-2.0). Changes: the isometric identifications `J`, `J'` of the outputs become readout
matrices `K`, `K'` with `‖K‖ ≤ 1`, `‖K'‖ ≤ 1`, the isometric frames become matrices with norm at
most one. The estimate therefore applies to arbitrary contractions. For each isometric frame
`F`, the hypothesis `‖F‖ ≤ 1` follows by applying
`Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one` to `Fᴴ * F = 1`.
See `04-compression.tex`, lines 454–470.
-/

open MeasureTheory Matrix ManyBody ProductSource QICLean.ComplexGaussian
open scoped ComplexConjugate Matrix.Norms.L2Operator

/-- The exterior image of a weighted block combination, after the partial trace, is the
combination of the exterior images of the blocks. -/
private theorem partialTraceRight_halfWeightedBlockCombination {I L T U M N : Type} [Fintype I]
    [Fintype L] [Fintype T] [Fintype U] [DecidableEq T] [DecidableEq U] [Fintype N]
    (K₁ : Matrix (M × N) T ℂ) (K₂ : Matrix (M × N) U ℂ) (tau : T → ℝ) (tau' : U → ℝ)
    (O : Matrix (L × U) (I × T) ℂ)
    (z : I × L → ℂ) :
    partialTraceRight (K₁ * halfWeightedBlockCombination tau tau' O z * K₂ᴴ) =
      ∑ q, z q • partialTraceRight
        (K₁ * halfWeighted tau tau' ((Matrix.comp _ _ _ _ ℂ).symm O q.2 q.1)ᵀ * K₂ᴴ) := by
  simp only [halfWeightedBlockCombination, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  change partialTraceRightLM (∑ q, z q • _) = _
  simp only [map_sum, map_smul]
  rfl

namespace QuantumCircuit.Party

variable {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {X X' Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (X' p)]
  [∀ p, DecidableEq (X' p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  {Z Z' W : Q → Type} [∀ q, Fintype (Z q)] [∀ q, DecidableEq (Z q)] [∀ q, Fintype (Z' q)]
  [∀ q, DecidableEq (Z' q)] [∀ q, Fintype (W q)] [∀ q, DecidableEq (W q)]
  {Phys Env Phys' Env' I L T U : Type} [Fintype Phys] [DecidableEq Phys] [Fintype Env]
  [DecidableEq Env] [Fintype Phys'] [DecidableEq Phys'] [Fintype Env']
  [Fintype I] [Fintype L] [Fintype T] [Fintype U] [DecidableEq T] [DecidableEq U]

namespace Word

/-- **Diagonal covariance bounds the expected exterior error of separated words** by `√κ`; the
contraction bounds come from allowedness and the norms of the readouts and frames, and no input,
private or discarded dimension enters. Source: Theorem 5.2, `eq:compression-exterior-input` and
`eq:compression-one-choice`, `04-compression.tex`, lines 454–520. -/
theorem integral_rectangularTraceNorm_weightedPhysicalSource_le [DecidableEq I] [DecidableEq L]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys) (v : Word X Y) (w : Word X' Y)
    (F : Matrix (Config X) (I × T) ℂ) (F' : Matrix (Config X') (L × U) ℂ)
    (hK : ‖K‖ ≤ 1) (hv : v.IsAllowed) (hw : w.IsAllowed) (hF : ‖F‖ ≤ 1) (hF' : ‖F'‖ ≤ 1)
    (K' : Matrix (Phys' × Env') (Config W) ℂ) (v' : Word Z W) (w' : Word Z' W)
    (G : Matrix (Config Z) T ℂ) (G' : Matrix (Config Z') U ℂ)
    (hK' : ‖K'‖ ≤ 1) (hv' : v'.IsAllowed) (hw' : w'.IsAllowed) (hG : ‖G‖ ≤ 1) (hG' : ‖G'‖ ≤ 1)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : I → ℝ) (p' : L → ℝ) (tau : T → ℝ) (tau' : U → ℝ) (z : I × L → Ω → ℂ) (kappa : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp' : ∀ l, 0 ≤ p' l) (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (hpsum : ∑ i, p i = 1) (hp'sum : ∑ l, p' l = 1)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) (hkappa : 0 ≤ kappa)
    (hz : ∀ q r, Integrable (fun ω ↦ z q ω * conj (z r ω)) μ)
    (hcov : ∀ q r, (∫ ω, z q ω * conj (z r ω) ∂μ) =
      if q = r then ((kappa * Real.sqrt (p q.1 * p' q.2) : ℝ) : ℂ) else 0) :
    (∫ ω, rectangularTraceNorm (partialTraceRight (K' * v'.op * G *
      halfWeightedBlockCombination tau tau' (Word.physicalFrameGramMatrix K x y v w F F')
        (fun q ↦ z q ω) * (K' * w'.op * G')ᴴ)) ∂μ) ≤ Real.sqrt kappa := by
  set O := physicalFrameGramMatrix K x y v w F F'
  have hpoint (ω : Ω) : rectangularTraceNorm (partialTraceRight (K' * v'.op * G *
      halfWeightedBlockCombination tau tau' O (fun q ↦ z q ω) * (K' * w'.op * G')ᴴ)) ≤
      rectangularTraceNorm (halfWeightedBlockCombination tau tau' O (fun q ↦ z q ω)) :=
    rectangularTraceNorm_partialTraceRight_mul_op_mul_le K' v' w' G G' hK' hv' hw' hG hG' _
  have hint := ProbabilityTheory.integrable_rectangularTraceNorm_halfWeightedBlockCombination
    tau tau' O z hz htau htau' htausum htau'sum
  have hmeas : AEStronglyMeasurable (fun ω ↦ rectangularTraceNorm (partialTraceRight
      (K' * v'.op * G * halfWeightedBlockCombination tau tau' O (fun q ↦ z q ω) *
        (K' * w'.op * G')ᴴ))) μ := by
    simp_rw [partialTraceRight_halfWeightedBlockCombination]
    exact ProbabilityTheory.aestronglyMeasurable_rectangularTraceNorm_sum z hz _
  have hint' := hint.mono' hmeas (Filter.Eventually.of_forall fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (rectangularTraceNorm_nonneg _)]
    exact hpoint ω)
  exact (integral_mono hint' hint hpoint).trans
    (ProbabilityTheory.integral_rectangularTraceNorm_halfWeightedBlockCombination_le
      p p' tau tau' O z kappa hp hp' htau htau' hpsum hp'sum htausum htau'sum
      (norm_physicalFrameGramMatrix_le_one K x y v w F F' hK hv hw hF hF') hkappa hz hcov)

end Word

namespace SourceCircuit

variable {P₀ : Type} [DecidableEq P₀] {X₀ Y₀ : P₀ → Type}

open Classical in
/-- **The expected exterior error of separated sampled sources is at most `k ^ (-|S|/2)`**, for
the products of correction entries over a set `S` of positions at fixed labels. Source:
Theorem 5.2, `eq:compression-one-choice`, `04-compression.tex`, lines 454–520. -/
theorem integral_rectangularTraceNorm_gaussianPhysicalSource_le (circuit : SourceCircuit X₀ Y₀)
    (k : ℕ) (hk : 0 < k) (S : Finset circuit.sourceLocations)
    (ξ ζ : ∀ e : S, circuit.branchLabels e.1.1)
    (lam : ∀ e : circuit.sourceLocations, circuit.branchLabels e.1 →
      Fin (min (circuit.sourceDims e).1 (circuit.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j) (hmass : ∀ e ξ, ∑ j, lam e ξ j = 1)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (x y : Phys) (v : Word X Y) (w : Word X' Y)
    (F : Matrix (Config X) (CorrectedSchmidtCoordinates circuit S × T) ℂ)
    (F' : Matrix (Config X') (CorrectedSchmidtCoordinates circuit S × U) ℂ)
    (hK : ‖K‖ ≤ 1) (hv : v.IsAllowed) (hw : w.IsAllowed) (hF : ‖F‖ ≤ 1) (hF' : ‖F'‖ ≤ 1)
    (K' : Matrix (Phys' × Env') (Config W) ℂ) (v' : Word Z W) (w' : Word Z' W)
    (G : Matrix (Config Z) T ℂ) (G' : Matrix (Config Z') U ℂ)
    (hK' : ‖K'‖ ≤ 1) (hv' : v'.IsAllowed) (hw' : w'.IsAllowed) (hG : ‖G‖ ≤ 1) (hG' : ‖G'‖ ≤ 1)
    (tau : T → ℝ) (tau' : U → ℝ) (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    (∫ ω, rectangularTraceNorm (partialTraceRight (K' * v'.op * G *
      halfWeightedBlockCombination tau tau' (Word.physicalFrameGramMatrix K x y v w F F')
        (fun q ↦ ∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
          (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)) * (K' * w'.op * G')ᴴ))
      ∂sourceGaussianLaw circuit k) ≤ (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  classical
  let p := pairedProductProbability (fun e : S ↦ lam e.1 (ξ e))
  let p' := pairedProductProbability (fun e : S ↦ lam e.1 (ζ e))
  have hp : ∀ i, 0 ≤ p i := pairedProductProbability_nonneg _ (fun e ↦ hnonneg e.1 (ξ e))
  have hp' : ∀ i, 0 ≤ p' i := pairedProductProbability_nonneg _ (fun e ↦ hnonneg e.1 (ζ e))
  have hpsum : ∑ i : CorrectedSchmidtCoordinates circuit S, p i = 1 := by
    convert sum_pairedProductProbability_eq_one (fun e : S ↦ lam e.1 (ξ e))
      (fun e ↦ hmass e.1 (ξ e)) using 1
    exact Finset.sum_congr (by ext; simp only [Finset.mem_univ]) fun _ _ ↦ rfl
  have hp'sum : ∑ i : CorrectedSchmidtCoordinates circuit S, p' i = 1 := by
    convert sum_pairedProductProbability_eq_one (fun e : S ↦ lam e.1 (ζ e))
      (fun e ↦ hmass e.1 (ζ e)) using 1
    exact Finset.sum_congr (by ext; simp only [Finset.mem_univ]) fun _ _ ↦ rfl
  have hcov (q r : CorrectedSchmidtCoordinates circuit S × CorrectedSchmidtCoordinates circuit S) :
      (∫ ω, (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
          (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)) *
        conj (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
          (ω e.1 (ξ e, ζ e)) (r.1 e) (r.2 e)) ∂sourceGaussianLaw circuit k) =
        if q = r then (((k : ℝ) ^ (-(S.card : ℝ)) * Real.sqrt (p q.1 * p' q.2) : ℝ) : ℂ)
        else 0 := by
    have hc := integral_sourceCorrection_product_mul_conj circuit k hk S ξ ζ lam hnonneg
      q.1 r.1 q.2 r.2
    by_cases hqr : q = r <;> simpa only [← Prod.ext_iff, hqr, and_self, ↓reduceIte] using hc
  have h := Word.integral_rectangularTraceNorm_weightedPhysicalSource_le K x y v w F F' hK hv hw
    hF hF' K' v' w' G G' hK' hv' hw' hG hG' (sourceGaussianLaw circuit k) p p' tau tau'
    (fun q ω ↦ ∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
      (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)) ((k : ℝ) ^ (-(S.card : ℝ)))
    hp hp' htau htau' hpsum hp'sum htausum htau'sum (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    (fun q r ↦ integrable_sourceCorrection_product_mul_conj circuit k hk S ξ ζ lam hnonneg
      q.1 r.1 q.2 r.2) hcov
  have hpow : Real.sqrt ((k : ℝ) ^ (-(S.card : ℝ))) = (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg k)]
    congr 1
    ring
  exact h.trans_eq hpow

open Classical in
/-- **The separated physical density of sampled sources has integrable trace norm with mean at
most `d² k ^ (-|S|/2)`**, `d` the number of affected physical indices. Source: Theorem 5.2,
`eq:compression-one-choice`, `04-compression.tex`, lines 454–520. -/
theorem integrable_gaussianSeparatedPhysicalDensity_and_integral_le
    (circuit : SourceCircuit X₀ Y₀) (k : ℕ) (hk : 0 < k) (S : Finset circuit.sourceLocations)
    (ξ ζ : ∀ e : S, circuit.branchLabels e.1.1)
    (lam : ∀ e : circuit.sourceLocations, circuit.branchLabels e.1 →
      Fin (min (circuit.sourceDims e).1 (circuit.sourceDims e).2) → ℝ)
    (hnonneg : ∀ e ξ j, 0 ≤ lam e ξ j) (hmass : ∀ e ξ, ∑ j, lam e ξ j = 1)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (v : Word X Y) (w : Word X' Y)
    (F : Matrix (Config X) (CorrectedSchmidtCoordinates circuit S × T) ℂ)
    (F' : Matrix (Config X') (CorrectedSchmidtCoordinates circuit S × U) ℂ)
    (hK : ‖K‖ ≤ 1) (hv : v.IsAllowed) (hw : w.IsAllowed) (hF : ‖F‖ ≤ 1) (hF' : ‖F'‖ ≤ 1)
    (K' : Matrix (Phys' × Env') (Config W) ℂ) (v' : Word Z W) (w' : Word Z' W)
    (G : Matrix (Config Z) T ℂ) (G' : Matrix (Config Z') U ℂ)
    (hK' : ‖K'‖ ≤ 1) (hv' : v'.IsAllowed) (hw' : w'.IsAllowed) (hG : ‖G‖ ≤ 1) (hG' : ‖G'‖ ≤ 1)
    (tau : T → ℝ) (tau' : U → ℝ) (htau : ∀ t, 0 ≤ tau t) (htau' : ∀ u, 0 ≤ tau' u)
    (htausum : ∑ t, tau t = 1) (htau'sum : ∑ u, tau' u = 1) :
    let M := fun ω : SourceGaussianSamples circuit k ↦ Word.separatedPhysicalDensity K v w F F'
      tau tau' K' v' w' G G' (fun q ↦ ∏ e : S, sourceCorrection k (lam e.1 (ξ e))
        (lam e.1 (ζ e)) (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e))
    Integrable (fun ω ↦ rectangularTraceNorm (M ω)) (sourceGaussianLaw circuit k) ∧
      (∫ ω, rectangularTraceNorm (M ω) ∂sourceGaussianLaw circuit k) ≤
        (Fintype.card Phys : ℝ) ^ 2 * (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  intro M
  classical
  let R := fun q : CorrectedSchmidtCoordinates circuit S × CorrectedSchmidtCoordinates circuit S ↦
    partialTraceRight (vecMulVec (Word.separatedPhysicalCoordinates K v F tau K' v' G q.1)
      (fun h ↦ conj (Word.separatedPhysicalCoordinates K w F' tau' K' w' G' q.2 h)))
  have hM (ω : SourceGaussianSamples circuit k) :
      M ω = ∑ q, (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
        (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)) • R q := by
    change partialTraceRightLM (∑ q, _ • vecMulVec _ _) = _
    simp only [map_sum, map_smul]
    rfl
  have hm : Integrable (fun ω ↦ rectangularTraceNorm (M ω)) (sourceGaussianLaw circuit k) := by
    simp_rw [hM]
    exact integrable_rectangularTraceNorm_sourceCorrectionSum circuit k hk S ξ ζ lam hnonneg R
  have hb (x y : Phys) : Integrable (fun ω ↦ rectangularTraceNorm
      ((M ω).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)))) (sourceGaussianLaw circuit k) := by
    have he (ω : SourceGaussianSamples circuit k) :
        (M ω).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)) =
          ∑ q, (∏ e : S, sourceCorrection k (lam e.1 (ξ e)) (lam e.1 (ζ e))
            (ω e.1 (ξ e, ζ e)) (q.1 e) (q.2 e)) •
            (R q).submatrix (fun i ↦ (x, i)) (fun j ↦ (y, j)) := by
      rw [hM]
      ext i j
      simp only [submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
    simp_rw [he]
    exact integrable_rectangularTraceNorm_sourceCorrectionSum circuit k hk S ξ ζ lam hnonneg _
  refine ⟨hm, (integral_rectangularTraceNorm_le_sum_submatrix M hb).trans ?_⟩
  calc
    _ ≤ ∑ _x : Phys, ∑ _y : Phys, (k : ℝ) ^ (-(S.card : ℝ) / 2) :=
      Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun y _ ↦ by
        simp only [M, Word.separatedPhysicalDensity_submatrix]
        convert integral_rectangularTraceNorm_gaussianPhysicalSource_le circuit k hk S ξ ζ lam
            hnonneg hmass K x y v w F F' hK hv hw hF hF' K' v' w' G G' hK' hv' hw' hG hG' tau tau'
            htau htau' htausum htau'sum
    _ = _ := by simp [pow_two, mul_assoc]

end SourceCircuit

end QuantumCircuit.Party
