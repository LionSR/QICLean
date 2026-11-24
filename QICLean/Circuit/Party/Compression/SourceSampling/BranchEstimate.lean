/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.SourceSampling.GaussianError
import QICLean.Circuit.Party.Compression.CorrectedSources.BranchOutput
import QICLean.Circuit.Party.Compression.PhysicalReadout.PartySplit

/-!
# Expected physical norm of one pair of branches

Fix a set `S` of source positions of a source circuit with contractive local operations, the
affected parties `A` of `S` (the endpoints of its positions), and a ket branch and a bra branch
of the partial expansion along `A`. The output register of every party is read as a physical
register of dimension `d p` and a private register through `e p : Y p ≃ Fin (d p) × G p`. For
Gaussian samples of the corrected sources, the physical part of the sampled density of the two
branches, the private registers traced out, has integrable trace norm with mean at most
`(∏_{p ∈ A} d p)² k ^ (-|S| / 2)`: no input, private or exterior dimension enters.

The local words and the input frames of the two sides are constructed from the circuit and from
the preparation of the input (`SourceCircuit.exists_correctedSchmidtOutput`); the estimate is
`SourceCircuit.integrable_gaussianSeparatedPhysicalDensity_and_integral_le`.

The Schmidt frames `E e ξ`, `F e ξ` of the sources are matrices whose rows are indexed by the
bases `w.leftBasis e`, `w.rightBasis e` of the two registers of the source slot `e` and whose
columns are indexed by the Schmidt index. The hypotheses `(E e ξ)ᴴ * E e ξ = 1`,
`(F e ξ)ᴴ * F e ξ = 1` say that their columns are orthonormal: they are the source's
orthonormal vectors `u_a`, `v_a` in the two registers (`04-compression.tex`, lines 279–289).

## Main results

* `QuantumCircuit.Party.SourceCircuit.integrable_actualGaussianBranch_and_integral_le`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `eq:compression-one-choice`,
  `04-compression.tex`, lines 279–289 and 409–549.

The estimate is stated in configuration coordinates; the regional coordinates are given by the
equivalences `e p` of the output registers.
-/

open MeasureTheory Matrix ManyBody ProductSource QICLean.ComplexGaussian
open scoped ComplexConjugate Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.SourceCircuit

open GateIncidence

variable {P : Type} [Fintype P] [DecidableEq P] {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
  {G : P → Type} [∀ p, Fintype (G p)] [∀ p, DecidableEq (G p)] {d : P → ℕ}

/-- The Kronecker product of the matrices of two bijections of coordinates reads a vector at
the pair of images. -/
private theorem toMatrix_kronecker_toMatrix_mulVec {m n m' n' : Type} [Fintype m'] [Fintype n']
    [DecidableEq m'] [DecidableEq n'] (f : m ≃ m') (g : n ≃ n') (v : m' × n' → ℂ) (a : m)
    (b : n) :
    (((f.toPEquiv.toMatrix : Matrix m m' ℂ) ⊗ₖ (g.toPEquiv.toMatrix : Matrix n n' ℂ)) *ᵥ v)
      (a, b) = v (f a, g b) := by
  rw [← toMatrix_toPEquiv_prodCongr, PEquiv.toMatrix_toPEquiv_mulVec]
  rfl

/-- **The regional party readout of a Schmidt sum through two side words is the separated
coordinate**, for the side readouts along `e`. -/
private theorem regionalPartyReadout_mulVec_eq_separatedPhysicalCoordinates (A : Finset P)
    (e : ∀ p, Y p ≃ Fin (d p) × G p) {Xa : {b : Bool // b ∈ ({true} : Finset Bool)} → Type}
    {Xe : {b : Bool // b ∉ ({true} : Finset Bool)} → Type} [∀ b, Fintype (Xa b)]
    [∀ b, DecidableEq (Xa b)] [∀ b, Fintype (Xe b)] [∀ b, DecidableEq (Xe b)] {I T : Type}
    [Fintype T]
    (c : Word Xa fun b ↦ affectedSides (fun p ↦ decide (p ∈ A)) Y b)
    (c' : Word Xe fun b ↦ affectedSides (fun p ↦ decide (p ∈ A)) Y b)
    (Fm : Matrix (Config Xa) (I × T) ℂ) (Gm : Matrix (Config Xe) T ℂ) (tau : T → ℝ) (i : I)
    (v : Config Y → ℂ)
    (hv : ∀ y : RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true} ×
        ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true},
      v (blockConfigEquiv (affectedOwner fun p ↦ decide (p ∈ A)) Y
        (blockConfigEquiv (fun o : Option {p // decide (p ∈ A) = true} ↦ o.isSome)
          (blockSystem (affectedOwner fun p ↦ decide (p ∈ A)) Y)
          ((cutEquiv (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}).symm y))) =
        ∑ t, (Real.sqrt (tau t) : ℂ) * ((c.op * Fm) y.1 (i, t) * (c'.op * Gm) y.2 t)) :
    regionalPartyReadout A e *ᵥ v =
      Word.separatedPhysicalCoordinates
        ((affectedSidePartyEquiv A e).symm.toPEquiv.toMatrix :
          Matrix _ (RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}) ℂ) c Fm tau
        ((exteriorSidePartyEquiv A e).symm.toPEquiv.toMatrix :
          Matrix _ (ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}) ℂ) c' Gm i := by
  funext h
  obtain ⟨⟨x, y⟩, g, g'⟩ := h
  have hc := partyReadoutEquiv_sideConfig A e ((affectedSidePartyEquiv A e).symm (x, g))
    ((exteriorSidePartyEquiv A e).symm (y, g'))
  simp only [Equiv.apply_symm_apply] at hc
  rw [regionalPartyReadout_mulVec, ← hc, Equiv.symm_apply_apply, hv,
    ← Word.kronecker_mulVec_eq_separatedPhysicalCoordinates]
  exact (toMatrix_kronecker_toMatrix_mulVec (affectedSidePartyEquiv A e).symm
    (exteriorSidePartyEquiv A e).symm (fun cc ↦ ∑ t, (Real.sqrt (tau t) : ℂ) *
      ((c.op * Fm) cc.1 (i, t) * (c'.op * Gm) cc.2 t)) (x, g) (y, g')).symm

open Classical in
/-- **The physical part of the sampled density of a pair of branches has integrable trace norm
with mean at most `(∏_{p ∈ A} d p)² k ^ (-|S| / 2)`**, `A` the endpoints of the positions of
`S`. The frames `E s ξ`, `F s ξ` have rows indexed by the bases of the two registers of the
source slot `s` and columns indexed by the Schmidt index, and orthonormal columns (the
source's vectors `u_a`, `v_a`). The two local contractions and their input frames are
constructed; no input, private or exterior dimension enters. Source: Theorem 5.2,
`eq:compression-one-choice`, `04-compression.tex`, lines 409–549. -/
theorem integrable_actualGaussianBranch_and_integral_le (w : SourceCircuit X Y)
    (hw : w.IsLocalContractive) (S : Finset w.sourceLocations) (k : ℕ) (hk : 0 < k)
    (lam : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Fin (min (w.sourceDims s).1 (w.sourceDims s).2) → ℝ)
    (E : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Matrix (w.leftBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ)
    (F : ∀ s : w.sourceLocations, w.branchLabels s.1 →
      Matrix (w.rightBasis s) (Fin (min (w.sourceDims s).1 (w.sourceDims s).2)) ℂ)
    (hnonneg : ∀ s ξ j, 0 ≤ lam s ξ j) (hmass : ∀ s ξ, ∑ j, lam s ξ j = 1)
    (hE : ∀ s ξ, (E s ξ)ᴴ * E s ξ = 1) (hF : ∀ s ξ, (F s ξ)ᴴ * F s ξ = 1)
    (p₀ : Word (fun _ ↦ Unit) X) (hp₀ : p₀.IsAllowed) (hp₀s : p₀.sources = [])
    (ξ ζ : Choices (correctedMask w S) w) (e : ∀ p, Y p ≃ Fin (d p) × G p) :
    let A := correctedParties w.endpoints S
    let K := regionalPartyReadout A e
    let ψ : EuclideanSpace ℂ (Config X) := Matrix.toEuclideanLin p₀.op (WithLp.toLp 2 fun _ ↦ 1)
    let M := fun ω : SourceGaussianSamples w k ↦ partialTraceRight
      (K * gaussianSchmidtBranchDensity (correctedMask w S) w S k lam E F ω ψ ψ ξ ζ * Kᴴ)
    Integrable (fun ω ↦ rectangularTraceNorm (M ω)) (sourceGaussianLaw w k) ∧
      (∫ ω, rectangularTraceNorm (M ω) ∂sourceGaussianLaw w k) ≤
        (Fintype.card (RegionConfig (fun p ↦ Fin (d p)) A) : ℝ) ^ 2 *
          (k : ℝ) ^ (-(S.card : ℝ) / 2) := by
  intro A K ψ M
  classical
  obtain ⟨c, d', hc, hd, n, tau, Fr, Gr, htau, htausum, hFr, hGr, hξ⟩ :=
    w.exists_correctedSchmidtOutput S E F hw hE hF p₀ hp₀ hp₀s ξ
  obtain ⟨c', d'', hc', hd', n', tau', Fr', Gr', htau', htau'sum, hFr', hGr', hζ⟩ :=
    w.exists_correctedSchmidtOutput S E F hw hE hF p₀ hp₀ hp₀s ζ
  have hS := w.correctedMask_meets S
  let eqv := partialSchmidtCoordinateEquiv (correctedMask w S) w S hS
  let KA : Matrix (RegionConfig (fun p ↦ Fin (d p)) A × RegionConfig G A)
      (RegionConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}) ℂ :=
    (affectedSidePartyEquiv A e).symm.toPEquiv.toMatrix
  let KE : Matrix (ComplConfig (fun p ↦ Fin (d p)) A × ComplConfig G A)
      (ComplConfig (affectedSides (fun p ↦ decide (p ∈ A)) Y) {true}) ℂ :=
    (exteriorSidePartyEquiv A e).symm.toPEquiv.toMatrix
  let FI := reindex (Equiv.refl _) (eqv.prodCongr (Equiv.refl (Fin n))) Fr
  let FI' := reindex (Equiv.refl _) (eqv.prodCongr (Equiv.refl (Fin n'))) Fr'
  have hFI : ‖FI‖ ≤ 1 := (l2_opNorm_reindex_le _ _ _).trans hFr
  have hFI' : ‖FI'‖ ≤ 1 := (l2_opNorm_reindex_le _ _ _).trans hFr'
  let ξ₀ := fun s : S ↦ choiceAt (correctedMask w S) w ξ s.1.1
    (isTouched_of_source_endpoint (correctedMask w S) w s.1 (hS s.1 s.2))
  let ζ₀ := fun s : S ↦ choiceAt (correctedMask w S) w ζ s.1.1
    (isTouched_of_source_endpoint (correctedMask w S) w s.1 (hS s.1 s.2))
  let coeff := fun (u : CorrectedSchmidtCoordinates w S × CorrectedSchmidtCoordinates w S)
      (ω : SourceGaussianSamples w k) ↦
    ∏ s : S, sourceCorrection k (lam s.1 (ξ₀ s)) (lam s.1 (ζ₀ s))
      (ω s.1 (ξ₀ s, ζ₀ s)) (u.1 s) (u.2 s)
  let N := fun ω ↦ Word.separatedPhysicalDensity KA c c' FI FI' tau tau' KE d' d'' Gr Gr'
    (fun u ↦ coeff u ω)
  have hN : Integrable (fun ω ↦ rectangularTraceNorm (N ω)) (sourceGaussianLaw w k) ∧
      (∫ ω, rectangularTraceNorm (N ω) ∂sourceGaussianLaw w k) ≤
        (Fintype.card (RegionConfig (fun p ↦ Fin (d p)) A) : ℝ) ^ 2 *
          (k : ℝ) ^ (-(S.card : ℝ) / 2) :=
    integrable_gaussianSeparatedPhysicalDensity_and_integral_le w k hk S ξ₀ ζ₀ lam hnonneg hmass
      KA c c' FI FI' (l2_opNorm_toMatrix_toPEquiv_le _) hc hc' hFI hFI' KE d' d'' Gr Gr'
      (l2_opNorm_toMatrix_toPEquiv_le _) hd hd' hGr hGr' tau tau' htau htau' htausum htau'sum
  have hξcoord (i : CorrectedSchmidtCoordinates w S) :
      K *ᵥ (partialSchmidtOutput (correctedMask w S) w S E F ξ (eqv.symm i) ψ).ofLp =
        Word.separatedPhysicalCoordinates KA c FI tau KE d' Gr i :=
    regionalPartyReadout_mulVec_eq_separatedPhysicalCoordinates A e c d' FI Gr tau i _
      fun y ↦ hξ (eqv.symm i) y
  have hζcoord (i : CorrectedSchmidtCoordinates w S) :
      K *ᵥ (partialSchmidtOutput (correctedMask w S) w S E F ζ (eqv.symm i) ψ).ofLp =
        Word.separatedPhysicalCoordinates KA c' FI' tau' KE d'' Gr' i :=
    regionalPartyReadout_mulVec_eq_separatedPhysicalCoordinates A e c' d'' FI' Gr' tau' i _
      fun y ↦ hζ (eqv.symm i) y
  have houter : ∀ a b : EuclideanSpace ℂ (Config Y), K * euclideanOuterProduct a b * Kᴴ =
      vecMulVec (K *ᵥ a.ofLp) (star (K *ᵥ b.ofLp)) := fun a b ↦ by
    simp only [euclideanOuterProduct, mul_vecMulVec, vecMulVec_mul, star_mulVec]
  have he (ω : SourceGaussianSamples w k) : M ω = N ω := by
    change partialTraceRight (K * gaussianSchmidtBranchDensity (correctedMask w S) w S k lam E F
      ω ψ ψ ξ ζ * Kᴴ) = partialTraceRight (∑ q, coeff q ω • vecMulVec
        (Word.separatedPhysicalCoordinates KA c FI tau KE d' Gr q.1)
        (fun h ↦ conj (Word.separatedPhysicalCoordinates KA c' FI' tau' KE d'' Gr' q.2 h)))
    rw [gaussianSchmidtBranchDensity_eq_sum_original (correctedMask w S) w S hS]
    congr 1
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, houter,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
    rw [hξcoord u, hζcoord v]
    rfl
  simp only [he]
  exact hN

end QuantumCircuit.Party.SourceCircuit
