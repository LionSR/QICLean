/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.CorrectedTermBound
import QICLean.Circuit.Party.Compression.GateExpansion.DensityError
import QICLean.Circuit.Party.Compression.GateExpansion.ReplacementBounds

/-!
# Sampling the sources of a source circuit: the statements of Theorem 5.2

The sources of a source circuit are replaced by averages of `k` independent Gaussian samples
built from their Schmidt data. Three statements give the physical trace-norm error of one
sample, with `Q = B ^ (4 b) D ^ 4` and `k = binomialSampleCount (max 1 N) Q ε`, `N` the number
of source positions:

* `SourceCircuit.exists_sourceSample_lifetime_error_le` — for a source circuit with contractive
  local operations in which every party takes part in at most `b` gates, every gate has
  absolute coefficient sum at most `B ≥ 1` and every physical dimension is at most `D ≥ 1`,
  some sample has error at most `ε / 4`;
* `OriginalCircuit.exists_sourceSample_original_error_le` — for the source-only replacement of
  an original circuit on a product of unit vectors, some sample is within `3 ε / 4` of the
  physical density of the circuit;
* `EffectCircuit.exists_sourceSample_approximate_error_le` — for gate maps approximated by gate
  expansions within the gate budget, some sample of the replacement of the rescaled circuit is
  within `ε` of the physical density of the gate maps.

The Schmidt data are produced by the statements. The frames `E s ξ`, `F s ξ` are matrices whose
rows are indexed by the bases `w.leftBasis s`, `w.rightBasis s` of the two registers of the
source slot `s` and whose columns are indexed by the Schmidt index; the conditions
`(E s ξ)ᴴ * E s ξ = 1`, `(F s ξ)ᴴ * F s ξ = 1` say that the columns are orthonormal, so the
columns are the source's orthonormal vectors `u_a`, `v_a` in the two registers, and
`schmidtFrameVector (lam s ξ) (E s ξ) (F s ξ)` is the Schmidt decomposition
`∑_a √λ_a |u_a⟩|v_a⟩` of the source vector (`04-compression.tex`, lines 279–289).

The output register of every party is read as a physical register of dimension `d p` and a
private register through an equivalence `e p : Y p ≃ Fin (d p) × G p` (`partyReadout e`); for
the physical system `physicalSystem d G` and the identity equivalences this is
`physicalReadout d G`. No private dimension enters any bound.

This module takes Gaussian samples and is one of the modules of
`Circuit/Party/Compression/SourceSampling` allowed to import `QICLean.Probability`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.exists_sourceSample_lifetime_error_le`.
* `QuantumCircuit.Party.OriginalCircuit.exists_isMonomialBounded`,
  `QuantumCircuit.Party.OriginalCircuit.sum_norm_branchCoefficient_replacement_le`.
* `QuantumCircuit.Party.OriginalCircuit.exists_sourceSample_original_error_le`.
* `QuantumCircuit.Party.EffectCircuit.exists_sourceSample_approximate_error_le`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2 (`thm:compression`),
  `04-compression.tex`, statement lines 132–171, proof lines 279–565 and 590–600
  (`eq:compression-total-error`).

Inputs and outputs are in configuration coordinates; the physical and discarded registers of
each party are given by the equivalence `e` of its output register; the replacement is read
through `extendedReadout`.
-/

open MeasureTheory Matrix ManyBody QICLean.ComplexGaussian
open scoped ComplexConjugate Kronecker NNReal Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)]

section Sampling

variable [Fintype P] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

namespace SourceCircuit

variable {G : P → Type} [∀ p, Fintype (G p)] {d : P → ℕ}

open Classical in
/-- **Theorem 5.2, the sampling step.** A source circuit with contractive local operations, in
which every party takes part in at most `b = lifetime` gates, every gate has absolute
coefficient sum at most `B ≥ 1` and every physical dimension is at most `D ≥ 1`, has Schmidt
data of all its sources and one Gaussian sample at the count
`k = binomialSampleCount (max 1 N) (B ^ (4 b) D ^ 4) ε` (`N` the number of source positions)
whose source-replaced physical density is within `ε / 4` of the physical density of the
circuit, on every input prepared by an allowed source-free word.

The frames `E s ξ`, `F s ξ` are matrices with rows indexed by the bases `w.leftBasis s`,
`w.rightBasis s` of the two registers of the source slot `s` and columns indexed by the Schmidt
index; their columns are orthonormal (`(E s ξ)ᴴ * E s ξ = 1`, `(F s ξ)ᴴ * F s ξ = 1`), and they
are the source's orthonormal vectors `u_a`, `v_a` in the two registers: the source vector is
`∑_a √λ_a |u_a⟩|v_a⟩`. The output register of every party is read through `e` as a physical
register and a private register; the private dimensions are arbitrary. Source: Theorem 5.2,
`eq:compression-total-error`, `04-compression.tex`, lines 137–151, 279–289, 342–381 and
409–558. -/
theorem exists_sourceSample_lifetime_error_le (e : ∀ p, Y p ≃ Fin (d p) × G p)
    (w : SourceCircuit X Y) (hw : w.IsLocalContractive)
    (lifetime : ℕ) (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime)
    (hcoeff : ∀ j : w.gateLocations, ∑ ξ : w.branchLabels j, ‖w.branchCoefficient j ξ‖ ≤ B)
    (hphysical : ∀ p, (d p : ℝ≥0) ≤ D) (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (p₀ : Word (fun _ ↦ Unit) X) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = []) :
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := binomialSampleCount (max 1 (Fintype.card w.sourceLocations)) Q ε
    ∃ (lam : ∀ s : w.sourceLocations, w.branchLabels s.1 →
        Fin (min (w.sourceDims s).1 (w.sourceDims s).2) → ℝ)
      (E : ∀ s : w.sourceLocations, w.branchLabels s.1 →
        Matrix (w.leftBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ)
      (F : ∀ s : w.sourceLocations, w.branchLabels s.1 →
        Matrix (w.rightBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ),
      (∀ s ξ, (∀ j, 0 ≤ lam s ξ j) ∧ ∑ j, lam s ξ j = 1 ∧
        (E s ξ)ᴴ * E s ξ = 1 ∧ (F s ξ)ᴴ * F s ξ = 1 ∧
        schmidtFrameVector (lam s ξ) (E s ξ) (F s ξ) = (w.sourceVectorAt s ξ).ofLp) ∧
      ∃ ω : SourceGaussianSamples w k,
        let ψ : EuclideanSpace ℂ (Config X) :=
          Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1)
        rectangularTraceNorm
          (physicalSourceReplacedDensity w
              (fun s ξ ζ ↦ sampledSourceMatrix w k lam E F s ξ ζ ω) (partyReadout e)
              (euclideanOuterProduct ψ ψ) -
            physicalDensity w (partyReadout e) (euclideanOuterProduct ψ ψ)) ≤ ε / 4 := by
  intro Q k
  classical
  obtain ⟨lam, E, F, hframes, _⟩ := exists_local_schmidt_source_frames w
  refine ⟨lam, E, F, hframes, ?_⟩
  have hQ : 0 ≤ Q := by positivity
  have hk : 0 < k := (binomialSampleCount_bounds _ Q ε).1
  have key := exists_sampledSourceMatrix_error_le_of_integral_bound w Q ε hQ hε hεone lam
    (fun s ξ ↦ (hframes s ξ).1) E F (fun s ξ ↦ (hframes s ξ).2.2.2.2) (partyReadout e)
    (euclideanOuterProduct (Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1))
      (Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1)))
  obtain ⟨ω, hω⟩ := key fun S _ ↦ by
    have h := integral_actualCorrectedSourceTerm_le_lifetime e w hw lifetime B D hB hD hlifetime
      hcoeff hphysical S k hk lam E F
      (fun s ξ ↦ (hframes s ξ).1) (fun s ξ ↦ (hframes s ξ).2.1)
      (fun s ξ ↦ (hframes s ξ).2.2.1) (fun s ξ ↦ (hframes s ξ).2.2.2.1)
      (fun s ξ ↦ (hframes s ξ).2.2.2.2) p₀ hp₀ hp₀s
      (1 : Matrix (Config fun p ↦ Fin (d p)) (Config fun p ↦ Fin (d p)) ℂ)
      (1 : Matrix (Config G) (Config G) ℂ) (by rw [conjTranspose_one, Matrix.one_mul])
      (by rw [conjTranspose_one, Matrix.one_mul])
    rw [one_kronecker_one, Matrix.one_mul] at h
    exact h
  refine ⟨ω, ?_⟩
  intro ψ
  exact hω

end SourceCircuit

end Sampling

/-- The finite chronology of an effect circuit has some bound on its numbers of monomials. -/
private theorem EffectCircuit.exists_isMonomialBounded' : {X Y : P → Type} →
    (c : EffectCircuit X Y) → ∃ K, c.IsMonomialBounded K
  | _, _, PartyCircuit.done _ => ⟨0, trivial⟩
  | _, _, PartyCircuit.gate _ _ g => ⟨g.terms.length, le_rfl⟩
  | _, _, PartyCircuit.localOp _ _ _ => ⟨0, trivial⟩
  | _, _, PartyCircuit.localOps _ => ⟨0, trivial⟩
  | _, _, PartyCircuit.comp c c' => by
    obtain ⟨K, hK⟩ := EffectCircuit.exists_isMonomialBounded' c
    obtain ⟨J, hJ⟩ := EffectCircuit.exists_isMonomialBounded' c'
    exact ⟨K + J, hK.mono (Nat.le_add_right K J), hJ.mono (Nat.le_add_left J K)⟩

/-- Reading the discarded factor through an isometry does not change a partial trace. -/
private theorem partialTraceRight_one_kronecker_mul_conj {Phys Env Env' N : Type} [Fintype Phys]
    [DecidableEq Phys] [Fintype Env] [DecidableEq Env] [Fintype Env'] [Fintype N]
    (V : Matrix Env' Env ℂ) (hV : Vᴴ * V = 1) (K : Matrix (Phys × Env) N ℂ) (M : Matrix N N ℂ) :
    partialTraceRight (((1 : Matrix Phys Phys ℂ) ⊗ₖ V) * K * M *
        (((1 : Matrix Phys Phys ℂ) ⊗ₖ V) * K)ᴴ) = partialTraceRight (K * M * Kᴴ) := by
  have h := partialTraceRight_kronecker_conj_of_right_isometry (1 : Matrix Phys Phys ℂ) V hV
    (K * M * Kᴴ)
  rw [Matrix.one_mul, conjTranspose_one, Matrix.mul_one] at h
  rw [← h]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- The word preparing a vector at every party maps the one-dimensional input to the product
vector. Source: `04-compression.tex`, lines 137–139. -/
private theorem toEuclideanLin_op_localOps_prepMatrix [Fintype P]
    (φ : ∀ p, EuclideanSpace ℂ (X p)) :
    Matrix.toEuclideanLin (Word.op (PartyCircuit.localOps fun p ↦
        prepMatrix (Equiv.prodPUnit (X p)).symm (φ p)) : Matrix (Config X) _ ℂ)
      (WithLp.toLp 2 fun _ ↦ 1) = WithLp.toLp 2 (productVector fun p x ↦ φ p x) := by
  have hone : (fun _ : Config (fun _ : P ↦ Unit) ↦ (1 : ℂ)) = productVector fun _ _ ↦ 1 := by
    funext σ
    simp [productVector]
  have hop : (Word.op (PartyCircuit.localOps fun p ↦
      prepMatrix (Equiv.prodPUnit (X p)).symm (φ p)) : Matrix (Config X) _ ℂ) =
      piKronecker fun p ↦ prepMatrix (Equiv.prodPUnit (X p)).symm (φ p) :=
    PartyCircuit.op_localOps _ _
  rw [hop, Matrix.toLpLin_apply, WithLp.ofLp_toLp, hone, piKronecker_mulVec_productVector]
  refine congrArg (WithLp.toLp 2) (congrArg productVector (funext fun p ↦ funext fun x ↦ ?_))
  simp [mulVec, dotProduct]

/-- The extended readout reads a vector at fixed auxiliary registers. -/
private theorem extendedReadout_mulVec [Fintype P] {Y : P → Type} [∀ p, Fintype (Y p)]
    {Phys Env : Type} {A : P → Type} [∀ p, Fintype (A p)] [∀ p, DecidableEq (A p)]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (x : Config (fun p ↦ A p × Y p) → ℂ) (ph : Phys)
    (en : Env) (a : Config A) :
    (extendedReadout K *ᵥ x) (ph, (en, a)) = (K *ᵥ fun y ↦ x fun p ↦ (a p, y p)) (ph, en) := by
  simp only [mulVec, dotProduct]
  rw [← (Equiv.arrowProdEquivProdArrow P A Y).symm.sum_comp, Fintype.sum_prod_type]
  simp only [extendedReadout, reindex_apply, submatrix_apply, Equiv.symm_symm,
    Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Equiv.prodAssoc_symm_apply, kroneckerMap_apply, one_apply, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul]
  rw [Finset.sum_eq_single a (fun b _ hb ↦ by simp [Ne.symm hb])
    fun h ↦ absurd (Finset.mem_univ _) h]
  simp only [ite_true]
  rfl

namespace OriginalCircuit

/-- The finite chronology of an original circuit has some bound on the numbers of monomials of
its gates; no hypothesis is needed. Source: `04-compression.tex`, lines 137–151. -/
theorem exists_isMonomialBounded (w : OriginalCircuit X Y) : ∃ K, w.IsMonomialBounded K :=
  EffectCircuit.exists_isMonomialBounded' w.toEffectCircuit

variable [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- Every prepared gate of the source-only replacement has the coefficient-sum bound of the
original circuit. Source: `04-compression.tex`, lines 199–212 and 229. -/
theorem sum_norm_branchCoefficient_replacement_le {r : ℕ} {S δ : ℝ} (hδ : 0 < δ)
    (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S)
    (g : (w.replacement hδ hb).gateLocations) :
    (∑ ξ : (w.replacement hδ hb).branchLabels g,
      ‖(w.replacement hδ hb).branchCoefficient g ξ‖) ≤ S := by
  obtain ⟨K, hK⟩ := w.exists_isMonomialBounded
  exact ((w.isExpansionBounded_replacement hδ hb hK).at_gate g).2

variable [Fintype P]

open Classical in
/-- **Theorem 5.2, sampling the source-only replacement of an original circuit.** Every party
holds a unit vector `φ p` of its input register and a physical output register of dimension
`d p ≤ D` in front of a private register `V p` of arbitrary dimension. If every gate expansion
has at most `r` pair effects and coefficient sum at most `B ≥ 1`, there are at most `M`
nonprivate gates and every party takes part in at most `b = lifetime` of them, then the
source-only replacement `R` at the gate budget `sourceGateBudget ε M` has Schmidt data of
its sources and one Gaussian sample at the count
`k = binomialSampleCount (max 1 N) (B ^ (4 b) D ^ 4) ε` whose source-replaced physical density
is within `3 ε / 4` of the physical density of the original circuit. The replacement is read
through `extendedReadout`: its auxiliary registers are discarded with the private ones.

The frames `E s ξ`, `F s ξ` are matrices with rows indexed by the bases `R.leftBasis s`,
`R.rightBasis s` of the two registers of the source slot `s` and columns indexed by the Schmidt
index; their columns are orthonormal, and they are the source's orthonormal vectors `u_a`, `v_a`
in the two registers. Source: Theorem 5.2, `04-compression.tex`, lines 17–19, 137–151, 199–229,
279–289 and 342–381. -/
theorem exists_sourceSample_original_error_le
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (hφ : ∀ p, ‖φ p‖ = 1) (d : P → ℕ) (V : P → Type)
    [∀ p, Fintype (V p)] [∀ p, DecidableEq (V p)] (w : OriginalCircuit X (physicalSystem d V))
    {r M lifetime : ℕ} (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hb : w.IsExpansionBounded r (B : ℝ)) (hcount : w.nonprivateCount ≤ M)
    (hlifetime : ∀ p, w.participation p ≤ lifetime) (hphysical : ∀ p, (d p : ℝ≥0) ≤ D)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1) :
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    let R := w.replacement (sourceGateBudget_pos hε M) hb
    let K := extendedReadout
      (A := EffectCircuit.auxiliary (stackLength r (B : ℝ) (sourceGateBudget ε M))
        w.toEffectCircuit) (physicalReadout d V)
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := binomialSampleCount (max 1 (Fintype.card R.sourceLocations)) Q ε
    ∃ (lam : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Fin (min (R.sourceDims s).1 (R.sourceDims s).2) → ℝ)
      (E : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (R.leftBasis s) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
      (F : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (R.rightBasis s) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ),
      (∀ s ξ, (∀ j, 0 ≤ lam s ξ j) ∧ ∑ j, lam s ξ j = 1 ∧
        (E s ξ)ᴴ * E s ξ = 1 ∧ (F s ξ)ᴴ * F s ξ = 1 ∧
        schmidtFrameVector (lam s ξ) (E s ξ) (F s ξ) = (R.sourceVectorAt s ξ).ofLp) ∧
      ∃ ω : SourceCircuit.SourceGaussianSamples R k,
        rectangularTraceNorm
          (SourceCircuit.physicalSourceReplacedDensity R
              (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω) K
              (euclideanOuterProduct ψ ψ) -
            w.physicalDensity (physicalReadout d V) ψ) ≤ 3 * ε / 4 := by
  intro ψ R K Q k
  let aux := EffectCircuit.auxiliary (stackLength r (B : ℝ) (sourceGateBudget ε M))
    w.toEffectCircuit
  let e : ∀ p, aux p × (Fin (d p) × V p) ≃ Fin (d p) × (V p × aux p) :=
    fun p ↦ (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)
  let p₀ : Word (fun _ ↦ Unit) X :=
    PartyCircuit.localOps fun p ↦ prepMatrix (Equiv.prodPUnit (X p)).symm (φ p)
  have hp₀ : p₀.IsAllowed :=
    Word.isAllowed_localOps _ fun p ↦ (norm_prepMatrix_le _ _).trans (hφ p).le
  have hψ : Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1) = ψ :=
    toEuclideanLin_op_localOps_prepMatrix φ
  have hR : R.IsLocalContractive :=
    (EffectCircuit.isAllowed_replacement (sourceGateBudget_pos hε M) w.toEffectCircuit
      w.isAllowed_toEffectCircuit hb).isLocalContractive
  obtain ⟨lam, E, F, hframes, ω, hω⟩ := SourceCircuit.exists_sourceSample_lifetime_error_le e R hR
    lifetime B D hB hD
    (w.participationCount_replacement_le (sourceGateBudget_pos hε M) hb hlifetime)
    (w.sum_norm_branchCoefficient_replacement_le (sourceGateBudget_pos hε M) hb) hphysical ε hε
    hεone p₀ hp₀ rfl
  have hhalf := w.rectangularTraceNorm_sourceOnly_density_sub_le_half_of_count_le hε hb hcount
    (physicalReadout d V) (norm_physicalReadout_le_one d V) ψ
    (norm_toLp_productVector_eq_one φ hφ).le
  refine ⟨lam, E, F, hframes, ω, ?_⟩
  have hω' : rectangularTraceNorm
      (SourceCircuit.physicalSourceReplacedDensity R
          (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω) (partyReadout e)
          (euclideanOuterProduct ψ ψ) -
        SourceCircuit.physicalDensity R (partyReadout e) (euclideanOuterProduct ψ ψ)) ≤
      ε / 4 := by
    simpa only [hψ] using hω
  let Vp : Matrix (Config V × Config aux) (Config fun p ↦ V p × aux p) ℂ :=
    (Equiv.arrowProdEquivProdArrow P V aux).symm.toPEquiv.toMatrix
  have hVp : Vpᴴ * Vp = 1 := conjTranspose_toMatrix_toPEquiv_mul_self _
  have hK : K = ((1 : Matrix (Config fun p ↦ Fin (d p)) (Config fun p ↦ Fin (d p)) ℂ) ⊗ₖ Vp) *
      partyReadout e := by
    have h1 : (1 : Matrix (Config fun p ↦ Fin (d p)) (Config fun p ↦ Fin (d p)) ℂ) =
        (Equiv.refl _).toPEquiv.toMatrix := by
      rw [Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]
    refine Matrix.mulVec_injective (funext fun x ↦ funext fun a ↦ ?_)
    obtain ⟨s, g, a⟩ := a
    rw [h1, kronecker_toMatrix_mul_partyReadout_mulVec, extendedReadout_mulVec,
      ← partyReadout_refl, partyReadout_mulVec]
    rfl
  have h1 : SourceCircuit.physicalSourceReplacedDensity R
      (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω) K
      (euclideanOuterProduct ψ ψ) = SourceCircuit.physicalSourceReplacedDensity R
        (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω) (partyReadout e)
        (euclideanOuterProduct ψ ψ) := by
    rw [SourceCircuit.physicalSourceReplacedDensity, hK]
    exact partialTraceRight_one_kronecker_mul_conj Vp hVp _ _
  have h2 : w.replacementPhysicalDensity (sourceGateBudget_pos hε M) hb (physicalReadout d V) ψ =
      SourceCircuit.physicalDensity R (partyReadout e) (euclideanOuterProduct ψ ψ) := by
    have h := partialTraceRight_one_kronecker_mul_conj Vp hVp (partyReadout e * R.op)
      (euclideanOuterProduct ψ ψ)
    rw [← Matrix.mul_assoc, ← hK] at h
    rw [SourceCircuit.physicalDensity, ← h]
    exact (SourceCircuit.physicalDensity_pure_input R K ψ).symm
  rw [h1]
  calc
    _ = rectangularTraceNorm ((_ - SourceCircuit.physicalDensity R (partyReadout e)
          (euclideanOuterProduct ψ ψ)) + (w.replacementPhysicalDensity
            (sourceGateBudget_pos hε M) hb (physicalReadout d V) ψ - _)) := by
      rw [h2, sub_add_sub_cancel]
    _ ≤ _ := rectangularTraceNorm_add_le _ _
    _ ≤ ε / 4 + ε / 2 := add_le_add hω' hhalf
    _ = 3 * ε / 4 := by ring

end OriginalCircuit

namespace EffectCircuit

variable [Fintype P]

open Classical in
/-- **Theorem 5.2, approximate gate expansions.** Let the gate maps `G` of an effect circuit be
approximated by its gate expansions within the gate budget `sourceGateBudget (ε / 2) M`, with at
most `r` pair effects and coefficient sum at most `B ≥ 1` in every expansion, at most `M` gates
and at most `b = lifetime` gates at every party. Rescale the expansions to an original circuit
`W` and take its source-only replacement `R` at the gate budget `sourceGateBudget ε M`. Then `R`
has Schmidt data of its sources and one Gaussian sample at the count
`k = binomialSampleCount (max 1 N) (B ^ (4 b) D ^ 4) ε` whose source-replaced physical density
is within `ε` of the physical density of the gate maps, on every product of unit vectors. Only
the local approximation errors are assumed; no private dimension enters.

The frames `E s ξ`, `F s ξ` are matrices with rows indexed by the bases `R.leftBasis s`,
`R.rightBasis s` of the two registers of the source slot `s` and columns indexed by the Schmidt
index; their columns are orthonormal, and they are the source's orthonormal vectors `u_a`, `v_a`
in the two registers. Source: Theorem 5.2, `04-compression.tex`, lines 17–19, 137–175, 199–229,
279–289 and 590–600. -/
theorem exists_sourceSample_approximate_error_le
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (hφ : ∀ p, ‖φ p‖ = 1) (d : P → ℕ) (V : P → Type)
    [∀ p, Fintype (V p)] [∀ p, DecidableEq (V p)] (w : EffectCircuit X (physicalSystem d V))
    (G : w.GateMaps) {r M lifetime : ℕ} (B D : ℝ≥0) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hb : w.IsExpansionBounded r (B : ℝ)) (hcount : w.numGates ≤ M)
    (hlifetime : ∀ p, w.participationCount p ≤ lifetime) (hphysical : ∀ p, (d p : ℝ≥0) ≤ D)
    (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
    (happrox : w.IsGateApproximation (sourceGateBudget (ε / 2) M) G) :
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    let W := w.rescaledOriginal (sourceGateBudget_pos (half_pos hε) M).le G happrox
    let R := W.replacement (sourceGateBudget_pos hε M)
      (w.isExpansionBounded_rescaledOriginal (sourceGateBudget_pos (half_pos hε) M).le G
        happrox hb)
    let K := extendedReadout
      (A := EffectCircuit.auxiliary (stackLength r (B : ℝ) (sourceGateBudget ε M))
        W.toEffectCircuit) (physicalReadout d V)
    let Q := (B : ℝ) ^ (4 * lifetime) * (D : ℝ) ^ 4
    let k := binomialSampleCount (max 1 (Fintype.card R.sourceLocations)) Q ε
    ∃ (lam : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Fin (min (R.sourceDims s).1 (R.sourceDims s).2) → ℝ)
      (E : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (R.leftBasis s) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ)
      (F : ∀ s : R.sourceLocations, R.branchLabels s.1 →
        Matrix (R.rightBasis s) (Fin (min (R.sourceDims s).1 (R.sourceDims s).2)) ℂ),
      (∀ s ξ, (∀ j, 0 ≤ lam s ξ j) ∧ ∑ j, lam s ξ j = 1 ∧
        (E s ξ)ᴴ * E s ξ = 1 ∧ (F s ξ)ᴴ * F s ξ = 1 ∧
        schmidtFrameVector (lam s ξ) (E s ξ) (F s ξ) = (R.sourceVectorAt s ξ).ofLp) ∧
      ∃ ω : SourceCircuit.SourceGaussianSamples R k,
        rectangularTraceNorm
          (SourceCircuit.physicalSourceReplacedDensity R
              (fun s ξ ζ ↦ SourceCircuit.sampledSourceMatrix R k lam E F s ξ ζ ω) K
              (euclideanOuterProduct ψ ψ) -
            w.physicalDensityWithGateMaps G (physicalReadout d V) ψ) ≤ ε := by
  intro ψ W R K Q k
  have hcountW : W.nonprivateCount ≤ M :=
    (w.nonprivateCount_rescaledOriginal _ G happrox).trans_le hcount
  have hlifetimeW : ∀ p, W.participation p ≤ lifetime := fun p ↦
    ((w.participation_rescaledOriginal _ G happrox p).trans
      (PartyCircuit.natCard_participants_mem p w)).trans_le (hlifetime p)
  obtain ⟨lam, E, F, hframes, ω, hω⟩ := W.exists_sourceSample_original_error_le φ hφ d V B D hB
    hD (w.isExpansionBounded_rescaledOriginal _ G happrox hb) hcountW hlifetimeW hphysical ε hε
    hεone
  have hquarter := w.rectangularTraceNorm_rescaledOriginal_density_sub_le_budget G (half_pos hε)
    hcount happrox (physicalReadout d V) (norm_physicalReadout_le_one d V) ψ
    (norm_toLp_productVector_eq_one φ hφ).le
  refine ⟨lam, E, F, hframes, ω, ?_⟩
  calc
    _ = rectangularTraceNorm ((_ - W.physicalDensity (physicalReadout d V) ψ) +
          (W.physicalDensity (physicalReadout d V) ψ - _)) :=
      congrArg rectangularTraceNorm (sub_add_sub_cancel _ _ _).symm
    _ ≤ rectangularTraceNorm (_ - W.physicalDensity (physicalReadout d V) ψ) +
          rectangularTraceNorm (W.physicalDensity (physicalReadout d V) ψ - _) :=
      rectangularTraceNorm_add_le _ _
    _ ≤ 3 * ε / 4 + ε / 2 / 2 := add_le_add hω hquarter
    _ = ε := by ring

end EffectCircuit

end QuantumCircuit.Party
