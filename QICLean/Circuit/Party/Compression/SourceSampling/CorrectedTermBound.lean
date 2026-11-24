/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.BranchEstimate
import QICLean.Circuit.Party.Compression.SourceSampling.Integrability

/-!
# Expected norm of the corrected source terms

For a source circuit with contractive local operations and a set `S` of source positions, the
physical corrected term of the Gaussian corrections on `S`, on an input prepared by an allowed
source-free word, has expected trace norm at most the ket–bra coefficient sum of the partial
expansion along the endpoints of `S` times the squared physical dimension of these endpoints
times `k ^ (-|S| / 2)` (`integral_actualCorrectedSourceTerm_le`). With participation counts at
most `b`, coefficient sums at most `B ≥ 1` and physical dimensions at most `D ≥ 1`, this is at
most `(B ^ (4 b) D ^ 4) ^ |S| k ^ (-|S| / 2)` (`integral_actualCorrectedSourceTerm_le_lifetime`).

The output register of every party is read as a physical register of dimension `d p` and a
private register through `e p : Y p ≃ Fin (d p) × G p`, and then in arbitrary orthonormal
coordinates of the physical and of the discarded factor: the readout is
`(U ⊗ₖ V) * partyReadout e` for isometries `U`, `V`. The estimate is proved in the coordinates
adapted to the endpoints of `S` and transferred by
`SourceCircuit.rectangularTraceNorm_physicalCorrectedSourceTerm_kronecker_isometry_mul`.

The Schmidt frames `E s ξ`, `F s ξ` of the sources are matrices whose rows are indexed by the
bases `w.leftBasis s`, `w.rightBasis s` of the two registers of the source slot `s` and whose
columns are indexed by the Schmidt index; `(E s ξ)ᴴ * E s ξ = 1` and `(F s ξ)ᴴ * F s ξ = 1`
say that their columns are orthonormal, as the source's vectors `u_a`, `v_a` in the two
registers (`04-compression.tex`, lines 279–289).

## Main results

* `QuantumCircuit.Party.SourceCircuit.integral_actualCorrectedSourceTerm_le`.
* `QuantumCircuit.Party.SourceCircuit.integral_actualCorrectedSourceTerm_le_lifetime`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `eq:compression-choice-cost`,
  `eq:compression-one-choice`, `04-compression.tex`, lines 137–151, 279–289, 356–381 and
  409–549.

The input is in configuration coordinates; arbitrary orthonormal coordinates of the physical
and of the discarded registers are the isometries `U`, `V` applied after the party readout.
-/

open MeasureTheory Matrix ManyBody QICLean.ComplexGaussian
open scoped ComplexConjugate Kronecker NNReal Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.SourceCircuit

open GateIncidence

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  {G : P → Type} [∀ p, Fintype (G p)] [∀ p, DecidableEq (G p)] {d : P → ℕ}
  {Phys Env : Type} [Fintype Phys] [DecidableEq Phys] [Fintype Env]

/-- The physical readout `M ↦ Tr_Env (K M Kᴴ)` as a linear map. -/
private noncomputable def readoutTraceLinearMap {Phys Env : Type} [Fintype Env]
    (K : Matrix (Phys × Env) (Config Y) ℂ) :
    Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix Phys Phys ℂ where
  toFun M := partialTraceRightLM (α := Phys) (β := Env) (K * M * Kᴴ)
  map_add' M N := by simp only [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c M := by simp [Matrix.mul_smul, Matrix.smul_mul]

open Classical in
/-- **The corrected term of the Gaussian corrections has expected trace norm at most the
ket–bra coefficient sum times `(∏_{p ∈ A} d p)² k ^ (-|S| / 2)`**, `A` the endpoints of the
positions of `S`, in arbitrary orthonormal coordinates `U`, `V` of the physical and of the
discarded factor. The frames `E s ξ`, `F s ξ` have rows indexed by the bases of the two
registers of the source slot `s`, columns indexed by the Schmidt index, and orthonormal columns
(the source's vectors `u_a`, `v_a`). The local words and input frames are constructed from the
circuit and the preparation of the input. Source: Theorem 5.2, `eq:compression-one-choice`,
`04-compression.tex`, lines 409–549. -/
theorem integral_actualCorrectedSourceTerm_le (w : SourceCircuit X Y)
    (hw : w.IsLocalContractive) (S : Finset w.sourceLocations) (k : ℕ) (hk : 0 < k)
    (lam : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Fin (min (w.sourceDims s).1 (w.sourceDims s).2) → ℝ)
    (E : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Matrix (w.leftBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ)
    (F : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Matrix (w.rightBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ)
    (hnonneg : ∀ s ξ j, 0 ≤ lam s ξ j) (hmass : ∀ s ξ, ∑ j, lam s ξ j = 1)
    (hE : ∀ s ξ, (E s ξ)ᴴ * E s ξ = 1) (hF : ∀ s ξ, (F s ξ)ᴴ * F s ξ = 1)
    (hsource : ∀ s ξ, schmidtFrameVector (lam s ξ) (E s ξ) (F s ξ) = (w.sourceVectorAt s ξ).ofLp)
    (p₀ : Word (fun _ ↦ Unit) X) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (e : ∀ p, Y p ≃ Fin (d p) × G p) (U : Matrix Phys (Config fun p ↦ Fin (d p)) ℂ)
    (V : Matrix Env (Config G) ℂ) (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    let A := correctedMask w S
    let ψ : EuclideanSpace ℂ (Config X) := Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1)
    (∫ ω, rectangularTraceNorm (physicalCorrectedSourceTerm w S
      (sourceGaussianCorrection w k lam E F ω) ((U ⊗ₖ V) * partyReadout e)
        (euclideanOuterProduct ψ ψ)) ∂sourceGaussianLaw w k) ≤
      ((∑ ξ : Choices A w, ∑ ζ : Choices A w,
        ‖coefficient A w ξ * conj (coefficient A w ζ)‖) *
        (Fintype.card (RegionConfig (fun p ↦ Fin (d p)) (correctedParties w.endpoints S)) : ℝ)
          ^ 2) * (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  intro A ψ
  set K := regionalPartyReadout (correctedParties w.endpoints S) e with hKdef
  have hinv (ω : SourceGaussianSamples w k) :
      rectangularTraceNorm (physicalCorrectedSourceTerm w S
        (sourceGaussianCorrection w k lam E F ω) ((U ⊗ₖ V) * partyReadout e)
          (euclideanOuterProduct ψ ψ)) =
      rectangularTraceNorm (readoutTraceLinearMap K (correctedSourceTerm w S
        (sourceGaussianCorrection w k lam E F ω) (euclideanOuterProduct ψ ψ))) :=
    (rectangularTraceNorm_physicalCorrectedSourceTerm_kronecker_isometry_mul w S _
      (partyReadout e) U V hU hV _).trans
      (rectangularTraceNorm_physicalCorrectedSourceTerm_kronecker_isometry_mul w S _
        (partyReadout e) _ _ (conjTranspose_cutMatrix_mul_self _ _)
        (conjTranspose_cutMatrix_mul_self _ _) _).symm
  simp_rw [hinv]
  have hS : ∀ s ∈ S, A (w.endpoints s).1 = true ∨ A (w.endpoints s).2 = true := fun s hs ↦
    Or.inl (decide_eq_true ((mem_correctedParties _ _ _).2 ⟨s, hs, Or.inl rfl⟩))
  refine (integral_rectangularTraceNorm_map_correctedSourceTerm_gaussian_le_sum A w S k hk lam
    E F hS hnonneg hsource ψ ψ (readoutTraceLinearMap K)).trans ?_
  calc
    _ ≤ ∑ ξ : Choices A w, ∑ ζ : Choices A w,
        ‖coefficient A w ξ * conj (coefficient A w ζ)‖ *
          ((Fintype.card (RegionConfig (fun p ↦ Fin (d p))
            (correctedParties w.endpoints S)) : ℝ) ^ 2 * (k : ℝ) ^ (-(S.card : ℝ) / 2)) :=
      Finset.sum_le_sum fun ξ _ ↦ Finset.sum_le_sum fun ζ _ ↦
        mul_le_mul_of_nonneg_left
          (integrable_actualGaussianBranch_and_integral_le w hw S k hk lam E F hnonneg hmass hE
            hF p₀ hp₀ hp₀s ξ ζ e).2 (norm_nonneg _)
    _ = _ := by simp only [← Finset.sum_mul, mul_assoc]

open Classical in
/-- **The corrected term obeys the lifetime and physical-dimension bound**
`(B ^ (4 b) D ^ 4) ^ |S| k ^ (-|S| / 2)`: every party takes part in at most `b` gates, every
gate has absolute coefficient sum at most `B ≥ 1`, and every physical dimension is at most
`D ≥ 1`. The frames `E s ξ`, `F s ξ` have rows indexed by the bases of the two registers of the
source slot `s`, columns indexed by the Schmidt index, and orthonormal columns. No private
dimension enters. Source: Theorem 5.2, `eq:compression-choice-cost`, `04-compression.tex`,
lines 137–151, 356–381 and 409–549. -/
theorem integral_actualCorrectedSourceTerm_le_lifetime (e : ∀ p, Y p ≃ Fin (d p) × G p)
    (w : SourceCircuit X Y) (hw : w.IsLocalContractive)
    (lifetime : ℕ) (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime)
    (hcoeff : ∀ j : w.gateLocations, ∑ ξ : w.branchLabels j, ‖w.branchCoefficient j ξ‖ ≤ B)
    (hphysical : ∀ p, (d p : ℝ≥0) ≤ D)
    (S : Finset w.sourceLocations) (k : ℕ) (hk : 0 < k)
    (lam : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Fin (min (w.sourceDims s).1 (w.sourceDims s).2) → ℝ)
    (E : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Matrix (w.leftBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ)
    (F : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Matrix (w.rightBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ)
    (hnonneg : ∀ s ξ j, 0 ≤ lam s ξ j) (hmass : ∀ s ξ, ∑ j, lam s ξ j = 1)
    (hE : ∀ s ξ, (E s ξ)ᴴ * E s ξ = 1) (hF : ∀ s ξ, (F s ξ)ᴴ * F s ξ = 1)
    (hsource : ∀ s ξ, schmidtFrameVector (lam s ξ) (E s ξ) (F s ξ) = (w.sourceVectorAt s ξ).ofLp)
    (p₀ : Word (fun _ ↦ Unit) X) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (U : Matrix Phys (Config fun p ↦ Fin (d p)) ℂ) (V : Matrix Env (Config G) ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) :
    let ψ : EuclideanSpace ℂ (Config X) := Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1)
    (∫ ω, rectangularTraceNorm (physicalCorrectedSourceTerm w S
      (sourceGaussianCorrection w k lam E F ω) ((U ⊗ₖ V) * partyReadout e)
        (euclideanOuterProduct ψ ψ)) ∂sourceGaussianLaw w k) ≤
      ((B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4) ^ S.card * (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  intro ψ
  have h := integral_actualCorrectedSourceTerm_le w hw S k hk lam E F hnonneg hmass hE hF hsource
    p₀ hp₀ hp₀s e U V hU hV
  have hdim : (Fintype.card (RegionConfig (fun p ↦ Fin (d p))
      (correctedParties w.endpoints S)) : ℝ) ^ 2 =
      ∏ p ∈ correctedParties w.endpoints S, (d p : ℝ) ^ 2 := by
    rw [card_regionConfig_fin, Nat.cast_prod, Finset.prod_pow]
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg k) _))
  rw [hdim]
  refine coefficient_physical_cost_le w S d lifetime B D hB hD (fun p _ ↦ ?_) (fun j _ ↦ ?_)
    fun p _ ↦ hphysical p
  · exact hlifetime p
  · apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum, coe_nnnorm] using hcoeff j

end QuantumCircuit.Party.SourceCircuit
