/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.Stationary.StationarySupportRestriction
import QICLean.Algebra.Unitary.MatrixGramUnitary
import QICLean.Algebra.Matrix.DependentBlockDiagonal
import QICLean.Channel.FixedPoint.DensityBlock.FullSupportBlockRetraction

/-!
# Density blocks after restriction to maximal stationary support

Let $T$ be positive and trace preserving, and suppose that its trace adjoint
satisfies the Schwarz inequality.  Restriction to the support of the maximal
stationary point gives a positive trace-preserving map with a positive-definite
fixed point.  The trace adjoint of this compression again satisfies the
Schwarz inequality, so the full-support density-block classification applies.

It also contains the following results.

* `IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero`: fixed points of positive
  trace-preserving maps.
* `IsPositiveMap.exists_block_densities_of_meanErgodicProjection_with_adjoint`,
  `IsPositiveMap.exists_block_densities_of_meanErgodicProjection`: density-block form of the
  full-support fixed points.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Lemma 6.5 and
  Theorem 6.14; local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1345--1386 and
  1483--1494.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder Kronecker

section TraceAdjointDensityBlocks

/-!
## Density-block form of the full-support fixed points

Suppose that a positive trace-preserving map has a positive-definite fixed
point and that its trace adjoint satisfies the Schwarz inequality.  The
adjoint Cesàro projection has the weighted partial-trace form supplied by the
preceding full-support fixed-point decomposition.  Taking its adjoint with
respect to the trace pairing gives the density-block formula for the original
Cesàro projection and identifies its range with the fixed points of the
original map.

Each summand is indexed by the product of the multiplicity index and the
matrix-factor index.  Thus the left partial trace is over the multiplicity
factor, and the Schrödinger-picture summand has the form
$\sigma_k\otimes M_{d_k}(\mathbb C)$.

### Main results

* `IsPositiveMap.exists_block_densities_of_meanErgodicProjection_with_adjoint`:
  the full-support density-block form in the same coordinates as the
  trace-adjoint fixed-point algebra.
* `IsPositiveMap.exists_block_densities_of_meanErgodicProjection`: the
  corresponding Schrödinger-picture statement.

### References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.5,
  Equation (1.40), Theorem 6.14, and Equation (6.63); local sources
  `Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 536--570,
  and `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1483--1494.
-/

open Matrix Finset BigOperators

noncomputable section

namespace Matrix

private theorem trace_density_blockMap_mul_eq
    {K : ℕ} {m d : Fin K → ℕ}
    (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (A B : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
      ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ) :
    Matrix.trace
        ((Matrix.blockDiagonal' fun k ↦
          σ k ⊗ₖ Matrix.partialTraceLeft
            (Matrix.directSumBlockCompression (m := m) (d := d) k B)) * A) =
      Matrix.trace
        (B * (Matrix.blockDiagonal' fun k ↦
          (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
            Matrix.partialTraceLeft
              (((σ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
                Matrix.directSumBlockCompression (m := m) (d := d) k A))) := by
  classical
  rw [Matrix.trace_blockDiagonal'_mul]
  rw [Matrix.trace_mul_comm, Matrix.trace_blockDiagonal'_mul]
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = Matrix.trace
        (Matrix.directSumBlockCompression (m := m) (d := d) k B *
          ((1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
            Matrix.partialTraceLeft
              (((σ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
                Matrix.directSumBlockCompression (m := m) (d := d) k A))) :=
      trace_kronecker_partialTraceLeft_mul_eq (σ k)
        (Matrix.directSumBlockCompression (m := m) (d := d) k A)
        (Matrix.directSumBlockCompression (m := m) (d := d) k B)
    _ = _ := Matrix.trace_mul_comm _ _

end Matrix

variable {D : ℕ}

/-- **Density-block form of the Cesàro projection on full support.**

Let $T:M_D(\mathbb C)\to M_D(\mathbb C)$ be positive and trace preserving,
suppose that $T^*$ satisfies the Schwarz inequality, and let $\rho>0$ satisfy
$T(\rho)=\rho$.  Then the mean-ergodic projection has the block form
\[
  P_T(B)=U\left(\bigoplus_k
    \sigma_k\otimes\operatorname{tr}_{m_k}((U^*BU)_{kk})\right)U^*,
\]
and its range, which equals $\operatorname{Fix}(T)$, is
$U(\bigoplus_k \sigma_k\otimes M_{d_k}(\mathbb C))U^*$.

This is the trace-adjoint calculation in Wolf, Equation (1.40), used in the
proof of Theorem 6.14 and Equation (6.63); local sources
`Notes/WolfNoteTexSource/ch01_deconstructing_quantum.tex`, lines 536--570,
and `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1483--1494.

**Scope restriction (full support):** The fixed point is positive definite on
the ambient space.  The subsequent maximal-support reduction and the
complementary zero summand are completed in the section on fixed-point density blocks
below; their construction is recorded in
`docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`.

**Convention (factor order):** Wolf writes the algebra and density factors in
the opposite order.  Each summand is indexed by
`Fin (m k) × Fin (d k)`, so `Matrix.partialTraceLeft` traces the multiplicity
factor and the density block is $\sigma_k\otimes M_{d_k}(\mathbb C)$. -/
theorem IsPositiveMap.exists_block_densities_of_meanErgodicProjection_with_adjoint
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : T ρ = ρ) :
    let P := LinearMap.meanErgodicProjection (𝕜 := ℂ)
      (E := Matrix (Fin D) (Fin D) ℂ) T
      (hT.hasBoundedOrbits_of_tracePreserving hTP)
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ A : Matrix (Fin D) (Fin D) ℂ,
          Matrix.traceAdjointMap T A = A ↔
            ∃ Y : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
              star U * A * U = Matrix.reindex e e
                (Matrix.blockDiagonal' fun k ↦
                  (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ Y k)) ∧
        (∀ k, (σ k).PosSemidef) ∧ (∀ k, (σ k).trace = 1) ∧
        (∀ B, P B = U * Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦
            σ k ⊗ₖ Matrix.partialTraceLeft
              (Matrix.directSumBlockCompression (m := m) (d := d) k
                (Matrix.reindex e.symm e.symm (star U * B * U)))) * star U) ∧
        ∀ B, T B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
  dsimp only
  let P := LinearMap.meanErgodicProjection (𝕜 := ℂ)
    (E := Matrix (Fin D) (Fin D) ℂ) T
    (hT.hasBoundedOrbits_of_tracePreserving hTP)
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, hBlock, hσpos, hσtrace, hFormula⟩ :=
    hT.exists_block_densities_of_adjoint_meanErgodicProjection hTP hSchwarz hρ hρfix
  have hPFormula : ∀ B, P B = U * Matrix.reindex e e
      (Matrix.blockDiagonal' fun k ↦
        σ k ⊗ₖ Matrix.partialTraceLeft
          (Matrix.directSumBlockCompression (m := m) (d := d) k
            (Matrix.reindex e.symm e.symm (star U * B * U)))) * star U := by
    intro B
    let Φ := Matrix.unitaryReindexLinearEquiv e U hU
    let F : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ →
        Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ :=
      fun A ↦ Matrix.blockDiagonal' fun k ↦
        (1 : Matrix (Fin (m k)) (Fin (m k)) ℂ) ⊗ₖ
          Matrix.partialTraceLeft
            (((σ k) ⊗ₖ (1 : Matrix (Fin (d k)) (Fin (d k)) ℂ)) *
              Matrix.directSumBlockCompression (m := m) (d := d) k A)
    let G : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ →
        Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
          ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ :=
      fun B ↦ Matrix.blockDiagonal' fun k ↦
        σ k ⊗ₖ Matrix.partialTraceLeft
          (Matrix.directSumBlockCompression (m := m) (d := d) k B)
    change P B = _
    rw [show U * Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦
            σ k ⊗ₖ Matrix.partialTraceLeft
              (Matrix.directSumBlockCompression (m := m) (d := d) k
                (Matrix.reindex e.symm e.symm (star U * B * U)))) * star U =
        Φ.symm (G (Φ B)) by
      simp only [Φ, G, Matrix.unitaryReindexLinearEquiv_apply,
        Matrix.unitaryReindexLinearEquiv_symm_apply]]
    refine sub_eq_zero.mp ((Matrix.trace_mul_right_eq_zero_iff
      (M := P B - Φ.symm (G (Φ B)))).1 ?_)
    intro A
    rw [Matrix.sub_mul, Matrix.trace_sub]
    apply sub_eq_zero.mpr
    have hPdouble : Matrix.traceAdjointMap (Matrix.traceAdjointMap P) B = P B :=
      LinearMap.congr_fun (Matrix.traceAdjointMap_traceAdjointMap P) B
    calc
      Matrix.trace (P B * A) =
          Matrix.trace (Matrix.traceAdjointMap (Matrix.traceAdjointMap P) B * A) := by
        rw [hPdouble]
      _ = Matrix.trace (B * Matrix.traceAdjointMap P A) :=
        Matrix.trace_traceAdjointMap_mul (Matrix.traceAdjointMap P) B A
      _ = Matrix.trace (B * Φ.symm (F (Φ A))) := by
        rw [hFormula A]
        simp only [Φ, F, Matrix.unitaryReindexLinearEquiv_apply,
          Matrix.unitaryReindexLinearEquiv_symm_apply]
      _ = Matrix.trace (Φ.symm (F (Φ A)) * B) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (F (Φ A) * Φ B) :=
        Matrix.trace_unitaryReindexLinearEquiv_symm_mul e U hU _ _
      _ = Matrix.trace (Φ B * F (Φ A)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (G (Φ B) * Φ A) := by
        exact (Matrix.trace_density_blockMap_mul_eq σ (Φ A) (Φ B)).symm
      _ = Matrix.trace (Φ.symm (G (Φ B)) * A) :=
        (Matrix.trace_unitaryReindexLinearEquiv_symm_mul e U hU _ _).symm
  refine ⟨K, d, m, e, U, σ, hU, hd, hm, hBlock, hσpos, hσtrace, hPFormula, ?_⟩
  intro B
  let Φ := Matrix.unitaryReindexLinearEquiv e U hU
  let G : Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
        ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ →
      Matrix ((k : Fin K) × (Fin (m k) × Fin (d k)))
        ((k : Fin K) × (Fin (m k) × Fin (d k))) ℂ :=
    fun B ↦ Matrix.blockDiagonal' fun k ↦
      σ k ⊗ₖ Matrix.partialTraceLeft
        (Matrix.directSumBlockCompression (m := m) (d := d) k B)
  rw [← hT.meanErgodicProjection_apply_eq_self_iff_of_tracePreserving hTP B]
  constructor
  · intro hPB
    refine ⟨fun k ↦ Matrix.partialTraceLeft
      (Matrix.directSumBlockCompression (m := m) (d := d) k (Φ B)), ?_⟩
    have hpcoord : P B = Φ.symm (G (Φ B)) := by
      simpa only [Φ, G, Matrix.unitaryReindexLinearEquiv_apply,
        Matrix.unitaryReindexLinearEquiv_symm_apply] using hPFormula B
    have hcoord : Φ B = G (Φ B) := by
      apply Φ.symm.injective
      rw [LinearEquiv.symm_apply_apply]
      exact hPB.symm.trans hpcoord
    calc
      star U * B * U = Matrix.reindex e e (Φ B) := by
        ext i j
        simp [Φ]
      _ = Matrix.reindex e e (G (Φ B)) := congrArg (Matrix.reindex e e) hcoord
      _ = _ := by rfl
  · rintro ⟨X, hX⟩
    have hcoord : Φ B = Matrix.blockDiagonal' (fun k ↦ σ k ⊗ₖ X k) := by
      rw [Matrix.unitaryReindexLinearEquiv_apply, hX]
      ext i j
      simp
    have hG : G (Φ B) = Φ B := by
      rw [hcoord]
      simp only [G]
      congr 1
      funext k
      have hcomp : Matrix.directSumBlockCompression (m := m) (d := d) k
            (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ X j) = σ k ⊗ₖ X k := by
        ext i j
        simp [Matrix.directSumBlockCompression, Matrix.blockDiagonal'_apply_eq]
      rw [hcomp, Matrix.partialTraceLeft_kronecker, hσtrace]
      simp
    calc
      P B = Φ.symm (G (Φ B)) := by
        simpa only [Φ, G, Matrix.unitaryReindexLinearEquiv_apply,
          Matrix.unitaryReindexLinearEquiv_symm_apply] using hPFormula B
      _ = Φ.symm (Φ B) := by rw [hG]
      _ = B := Φ.symm_apply_apply B

/-- **Schrödinger fixed-point blocks in the coordinates of the adjoint algebra.**

This is the Schrödinger-picture projection of
`IsPositiveMap.exists_block_densities_of_meanErgodicProjection_with_adjoint`.
It retains the established API for clients that do not need the simultaneous
trace-adjoint fixed-point characterization. -/
theorem IsPositiveMap.exists_block_densities_of_meanErgodicProjection
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ.PosDef) (hρfix : T ρ = ρ) :
    let P := LinearMap.meanErgodicProjection (𝕜 := ℂ)
      (E := Matrix (Fin D) (Fin D) ℂ) T
      (hT.hasBoundedOrbits_of_tracePreserving hTP)
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (σ k).PosSemidef) ∧ (∀ k, (σ k).trace = 1) ∧
        (∀ B, P B = U * Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦
            σ k ⊗ₖ Matrix.partialTraceLeft
              (Matrix.directSumBlockCompression (m := m) (d := d) k
                (Matrix.reindex e.symm e.symm (star U * B * U)))) * star U) ∧
        ∀ B, T B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
  dsimp only
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, -, hσpos, hσtrace, hFormula, hFixed⟩ :=
    hT.exists_block_densities_of_meanErgodicProjection_with_adjoint
      hTP hSchwarz hρ hρfix
  exact ⟨K, d, m, e, U, σ, hU, hd, hm, hσpos, hσtrace, hFormula, hFixed⟩

end

end TraceAdjointDensityBlocks

section SupportCompressedDensityBlocks

open Matrix

noncomputable section

variable {D n : ℕ}

local notation "MatD" => Matrix (Fin D) (Fin D) ℂ
local notation "Matn" => Matrix (Fin n) (Fin n) ℂ

/-- Taking the trace adjoint commutes with compression along an isometric
inclusion.

This is the trace-pairing identity used in Wolf, Lemma 6.5, especially
Equation (6.54); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1345--1368. -/
theorem Matrix.traceAdjointMap_stationarySupportCompression
    (T : MatD →ₗ[ℂ] MatD) (V : Matrix (Fin D) (Fin n) ℂ) :
    Matrix.traceAdjointMap (IsPositiveMap.stationarySupportCompression T V) =
      IsPositiveMap.stationarySupportCompression (Matrix.traceAdjointMap T) V := by
  apply LinearMap.ext
  intro A
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  calc
    (Matrix.traceAdjointMap (IsPositiveMap.stationarySupportCompression T V) A * B).trace =
        (A * IsPositiveMap.stationarySupportCompression T V B).trace :=
      Matrix.trace_traceAdjointMap_mul _ _ _
    _ = ((A * Vᴴ) * (T (V * B * Vᴴ) * V)).trace := by
      simp only [IsPositiveMap.stationarySupportCompression_apply, Matrix.mul_assoc]
    _ = ((T (V * B * Vᴴ) * V) * (A * Vᴴ)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (T (V * B * Vᴴ) * (V * A * Vᴴ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((V * A * Vᴴ) * T (V * B * Vᴴ)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (Matrix.traceAdjointMap T (V * A * Vᴴ) * (V * B * Vᴴ)).trace :=
      (Matrix.trace_traceAdjointMap_mul _ _ _).symm
    _ = ((Matrix.traceAdjointMap T (V * A * Vᴴ) * V) * (B * Vᴴ)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((B * Vᴴ) * (Matrix.traceAdjointMap T (V * A * Vᴴ) * V)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (B * (Vᴴ * Matrix.traceAdjointMap T (V * A * Vᴴ) * V)).trace := by
      simp only [Matrix.mul_assoc]
    _ = ((Vᴴ * Matrix.traceAdjointMap T (V * A * Vᴴ) * V) * B).trace :=
      Matrix.trace_mul_comm _ _
    _ = (IsPositiveMap.stationarySupportCompression
          (Matrix.traceAdjointMap T) V A * B).trace := rfl

/-- **Wolf Equation (6.53).** If `A` is fixed by the trace adjoint of a
positive trace-preserving map `T`, then its compression `Vᴴ * A * V` is fixed
by the trace adjoint of the restriction of `T` to the support of a stationary
positive matrix.

The argument uses the support intertwining of Equation (6.52) and the
trace-adjoint identity, without complete positivity or a Schwarz hypothesis.

Source: Wolf, Lemma 6.5, Equation (6.53); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1345--1376. -/
theorem Matrix.traceAdjointMap_stationarySupportCompression_fixed
    {T : MatD →ₗ[ℂ] MatD} (hT : IsPositiveMap T)
    (_hTP : IsTracePreservingMap T)
    {ρ : MatD} (hρ : ρ.PosSemidef) (hρfix : T ρ = ρ)
    (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1)
    (hVrange : V * Vᴴ = Kraus.stationaryProj hρ)
    {A : MatD} (hAfix : Matrix.traceAdjointMap T A = A) :
    Matrix.traceAdjointMap (IsPositiveMap.stationarySupportCompression T V)
        (Vᴴ * A * V) = Vᴴ * A * V := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  rw [Matrix.trace_traceAdjointMap_mul]
  have hintertwine := IsPositiveMap.stationarySupportCompression_intertwine
    hT hρ hρfix V hV hVrange B
  have htraceIntertwine :
      (Vᴴ * A * V * IsPositiveMap.stationarySupportCompression T V B).trace =
        (A * T (V * B * Vᴴ)).trace := by
    rw [hintertwine]
    simpa only [Matrix.mul_assoc] using
      (Matrix.trace_mul_cycle (A * V)
        (IsPositiveMap.stationarySupportCompression T V B) Vᴴ).symm
  rw [htraceIntertwine]
  calc
    (A * T (V * B * Vᴴ)).trace =
        (Matrix.traceAdjointMap T A * (V * B * Vᴴ)).trace :=
      (Matrix.trace_traceAdjointMap_mul T A (V * B * Vᴴ)).symm
    _ = (A * (V * B * Vᴴ)).trace := by rw [hAfix]
    _ = (Vᴴ * A * V * B).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A * V) B Vᴴ

/-- Compression along an isometry preserves the Schwarz inequality for a
positive map.

The proof compresses the original Schwarz defect and adds the positive corner
through $1-VV^*$.  This is Wolf, Equations (6.58)--(6.59), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1370--1386. -/
theorem IsSchwarzMap.stationarySupportCompression
    {E : MatD →ₗ[ℂ] MatD} (hE : IsSchwarzMap E) (hEpos : IsPositiveMap E)
    (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1) :
    IsSchwarzMap (IsPositiveMap.stationarySupportCompression E V) := by
  intro A
  let X : MatD := V * A * Vᴴ
  let Q : MatD := V * Vᴴ
  have hQ : IsOrthogonalProjection Q := by
    constructor
    · change Qᴴ = Q
      simp [Q]
    · dsimp [Q]
      calc
        (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by
          simp only [Matrix.mul_assoc]
        _ = V * Vᴴ := by rw [hV, Matrix.mul_one]
  have hcompressed :
      (Vᴴ * (E (Xᴴ * X) - E Xᴴ * E X) * V).PosSemidef :=
    (hE X).conjTranspose_mul_mul_same V
  have hcomplement :
      (Vᴴ * (E X)ᴴ * (1 - Q) * E X * V).PosSemidef := by
    have hQcomp : (1 - Q).PosSemidef :=
      isOrthogonalProjection_posSemidef hQ.one_sub
    have h := hQcomp.conjTranspose_mul_mul_same (E X * V)
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h
  have hXstar : E Xᴴ = (E X)ᴴ := hEpos.map_conjTranspose X
  change
    (Vᴴ * E (V * (Aᴴ * A) * Vᴴ) * V -
      (Vᴴ * E (V * Aᴴ * Vᴴ) * V) *
        (Vᴴ * E (V * A * Vᴴ) * V)).PosSemidef
  have hXsq : Xᴴ * X = V * (Aᴴ * A) * Vᴴ := by
    dsimp only [X]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    calc
      V * (Aᴴ * Vᴴ) * (V * A * Vᴴ) =
          V * Aᴴ * (Vᴴ * V) * A * Vᴴ := by
        simp only [Matrix.mul_assoc]
      _ = V * (Aᴴ * A) * Vᴴ := by rw [hV]; simp [Matrix.mul_assoc]
  have hXadj : Xᴴ = V * Aᴴ * Vᴴ := by
    dsimp only [X]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    exact (Matrix.mul_assoc _ _ _).symm
  rw [← hXsq, ← hXadj]
  rw [show
      Vᴴ * E (Xᴴ * X) * V -
          (Vᴴ * E Xᴴ * V) * (Vᴴ * E X * V) =
        Vᴴ * (E (Xᴴ * X) - E Xᴴ * E X) * V +
          Vᴴ * (E X)ᴴ * (1 - Q) * E X * V by
    rw [hXstar]
    dsimp only [Q]
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
    have hcorner :
        (Vᴴ * (E X)ᴴ * V) * (Vᴴ * E X * V) =
          Vᴴ * (E X)ᴴ * (V * Vᴴ) * E X * V := by
      simp only [Matrix.mul_assoc]
    have hwhole :
        Vᴴ * ((E X)ᴴ * E X) * V = Vᴴ * (E X)ᴴ * E X * V := by
      simp only [Matrix.mul_assoc]
    rw [hcorner]
    rw [hwhole]
    abel]
  exact hcompressed.add hcomplement

/-- If the trace adjoint of a positive map satisfies the Schwarz inequality,
then so does the trace adjoint after compression along an isometry.

This is Wolf, Equation (6.55), local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1369--1386. -/
theorem IsSchwarzMap.traceAdjointMap_stationarySupportCompression
    {T : MatD →ₗ[ℂ] MatD}
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) (hT : IsPositiveMap T)
    (V : Matrix (Fin D) (Fin n) ℂ) (hV : Vᴴ * V = 1) :
    IsSchwarzMap
      (Matrix.traceAdjointMap (IsPositiveMap.stationarySupportCompression T V)) := by
  rw [Matrix.traceAdjointMap_stationarySupportCompression]
  exact hSchwarz.stationarySupportCompression hT.traceAdjointMap V hV

/-- The restriction to maximal stationary support admits the density-block
description of its fixed points.

The support restriction is Wolf, Lemma 6.5, and the density-block conclusion
is the full-support step in the proof of Wolf, Theorem 6.14; local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1345--1386 and
1483--1494.

**Completion status:** This theorem records both the equivalence between the
original and compressed fixed-point spaces and the positive definite
density-block description after maximal-support compression.  The subsequent
unitary transport with its complementary zero summand, completing Wolf,
Theorem 6.14 and Equation (6.63), is proved in the section on fixed-point density blocks
below.  The completion is recorded in
`docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`.

The corresponding formula for the mean ergodic projection is supplied by
`IsPositiveMap.exists_block_densities_of_meanErgodicProjection`. -/
theorem IsPositiveMap.exists_block_densities_of_maximalSupportCompression
    {T : MatD →ₗ[ℂ] MatD} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    let ρ₀ := IsPositiveMap.maximalSupportPoint T hT hTP
    ∃ (hρ₀ : ρ₀.PosSemidef) (n : ℕ)
      (V : Matrix (Fin D) (Fin n) ℂ),
      T ρ₀ = ρ₀ ∧ Vᴴ * V = 1 ∧
        V * Vᴴ = Kraus.stationaryProj hρ₀ ∧
        (∃ ρfull : Matrix (Fin n) (Fin n) ℂ,
          ρfull.PosDef ∧
            IsPositiveMap.stationarySupportCompression T V ρfull = ρfull) ∧
        (∀ B : MatD, T B = B ↔
          ∃ X : Matrix (Fin n) (Fin n) ℂ,
            IsPositiveMap.stationarySupportCompression T V X = X ∧
              B = V * X * Vᴴ) ∧
        ∃ (K : ℕ) (d m : Fin K → ℕ)
          (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
          (U : Matrix (Fin n) (Fin n) ℂ)
          (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
          U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
            (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
            (∀ k, (σ k).PosDef) ∧ (∀ k, (σ k).trace = 1) ∧
            ∀ B, IsPositiveMap.stationarySupportCompression T V B = B ↔
              ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
                star U * B * U = Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
  dsimp only
  obtain ⟨hρ₀, n, V, hρ₀fix, hV, hVrange, hpositive, htrace, _,
      ⟨ρfull, hρfull, hρfullFix⟩, hambientFixed⟩ :=
    hT.exists_maximalSupportCompression hTP
  have hcompressedSchwarz :
      IsSchwarzMap (Matrix.traceAdjointMap
        (IsPositiveMap.stationarySupportCompression T V)) :=
    hSchwarz.traceAdjointMap_stationarySupportCompression hT V hV
  obtain ⟨K, d, m, e, U, σ, hU, hd, hm, _, hσtrace, _, hfixed⟩ :=
    hpositive.exists_block_densities_of_meanErgodicProjection
      htrace hcompressedSchwarz hρfull hρfullFix
  obtain ⟨X, hρblocks⟩ := (hfixed ρfull).mp hρfullFix
  let Uunitary : unitary (Matrix (Fin n) (Fin n) ℂ) := ⟨U, hU⟩
  have hUunit : IsUnit U := ⟨Unitary.toUnits Uunitary, rfl⟩
  have hρcoord : (star U * ρfull * U).PosDef := by
    simpa only [star_eq_conjTranspose] using
      hρfull.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_iff_isUnit.mpr hUunit)
  have hreindexed :
      (Matrix.reindex e e
        (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)).PosDef := by
    rw [← hρblocks]
    exact hρcoord
  have hblockDiagonal :
      (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k).PosDef := by
    have hprincipal := hreindexed.submatrix e.injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_submatrix,
      Equiv.symm_comp_self, Matrix.submatrix_id_id] using hprincipal
  have hσ : ∀ k, (σ k).PosDef := by
    intro k
    let : Nonempty (Fin (m k)) := Fin.pos_iff_nonempty.mp (hm k)
    let : Nonempty (Fin (d k)) := Fin.pos_iff_nonempty.mp (hd k)
    have hblock : (σ k ⊗ₖ X k).PosDef := by
      have hprincipal := hblockDiagonal.submatrix
        (e := fun i ↦ ⟨k, i⟩)
        (fun _ _ hij ↦ eq_of_heq (Sigma.mk.inj_iff.mp hij).2)
      have heq :
          (Matrix.blockDiagonal' fun j ↦ σ j ⊗ₖ X j).submatrix
              (fun i ↦ ⟨k, i⟩) (fun i ↦ ⟨k, i⟩) = σ k ⊗ₖ X k := by
        ext i j
        exact Matrix.blockDiagonal'_apply_eq
          (fun q : Fin K ↦ σ q ⊗ₖ X q) k i j
      rw [heq] at hprincipal
      exact hprincipal
    exact hblock.left_of_kronecker_of_trace_eq_one (hσtrace k)
  exact ⟨hρ₀, n, V, hρ₀fix, hV, hVrange,
    ⟨ρfull, hρfull, hρfullFix⟩, hambientFixed,
    K, d, m, e, U, σ, hU, hd, hm, hσ, hσtrace, hfixed⟩

end

end SupportCompressedDensityBlocks

section FixedPointDensityBlocks

/-!
## Fixed points of positive trace-preserving maps

This file proves the density-block classification of the fixed points of a
positive trace-preserving map whose trace adjoint satisfies the Schwarz
inequality.  Restriction to maximal stationary support gives the full-support
density blocks.  A unitary extension of the support isometry places the
orthogonal complement in one zero summand.

### Reference

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
  Equation (6.63); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1469--1494.
-/

open Matrix

noncomputable section

variable {D : ℕ}

local notation "MatD" => Matrix (Fin D) (Fin D) ℂ

/-- **Wolf Theorem 6.14, Equation (6.63).** Let `T` be positive and trace
preserving, and suppose that its trace adjoint satisfies the Schwarz
inequality.  Then, after a unitary change of basis, the fixed-point space is
one zero summand followed by density-weighted full matrix blocks.  Every
density matrix is positive definite and has trace one.

The formalization orders each nonzero summand as
`ℂ^{m k} ⊗ ℂ^{d k}`, so its matrices are `σ k ⊗ₖ X k`.  This differs from
Wolf's displayed order only by the canonical interchange of the two tensor
factors.

Source: Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14 and
Equation (6.63); local source
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1469--1494. -/
theorem IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero
    {T : MatD →ₗ[ℂ] MatD} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    ∃ (n K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
      (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup (Fin D) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (σ k).PosDef) ∧ (∀ k, (σ k).trace = 1) ∧
        ∀ B : MatD, T B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e₀ e₀
              (Matrix.fromBlocks 0 0 0
                (Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k))) := by
  obtain ⟨_, n, V, _, hV, _, _, hambientFixed, hblocks⟩ :=
    hT.exists_block_densities_of_maximalSupportCompression hTP hSchwarz
  obtain ⟨K, d, m, e, Uc, σ, hUc, hd, hm, hσ, hσtrace, hcompressedFixed⟩ :=
    hblocks
  have hUcLeft : star Uc * Uc = 1 := Matrix.mem_unitaryGroup_iff'.mp hUc
  have hUcRight : Uc * star Uc = 1 := Matrix.mem_unitaryGroup_iff.mp hUc
  let W : Matrix (Fin D) (Fin n) ℂ := V * Uc
  have hWH : Wᴴ = star Uc * Vᴴ := by
    simp only [W, Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose]
  have hW : Wᴴ * W = 1 := by
    rw [hWH]
    dsimp only [W]
    calc
      star Uc * Vᴴ * (V * Uc) = star Uc * (Vᴴ * V) * Uc := by
        simp only [Matrix.mul_assoc]
      _ = star Uc * Uc := by rw [hV]; simp
      _ = 1 := hUcLeft
  obtain ⟨e₀, Uunitary, hzeroExtension⟩ :=
    Matrix.exists_unitary_zero_extension_eq W hW
  let U : Matrix (Fin D) (Fin D) ℂ := Uunitary
  have hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ := Uunitary.property
  have hULeft : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hURight : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  refine ⟨n, K, d, m, e, e₀, U, σ, hU, hd, hm, hσ, hσtrace, fun B ↦ ?_⟩
  constructor
  · intro hBfix
    obtain ⟨Y, hYfix, hBY⟩ := (hambientFixed B).mp hBfix
    obtain ⟨X, hYcoord⟩ := (hcompressedFixed Y).mp hYfix
    let A : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.reindex e e (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)
    have hYeq : Y = Uc * A * star Uc := by
      calc
        Y = (Uc * star Uc) * Y * (Uc * star Uc) := by rw [hUcRight]; simp
        _ = Uc * (star Uc * Y * Uc) * star Uc := by
          simp only [Matrix.mul_assoc]
        _ = Uc * A * star Uc := by rw [hYcoord]
    have hBzero :
        B = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := by
      calc
        B = V * Y * Vᴴ := hBY
        _ = W * A * Wᴴ := by
          rw [hYeq]
          dsimp only [W]
          simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
            Matrix.mul_assoc]
        _ = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := by
          simpa only [U] using hzeroExtension A
    refine ⟨X, ?_⟩
    change star U * B * U = Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A)
    calc
      star U * B * U =
          star U *
            (U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U) * U := by
        rw [hBzero]
      _ = (star U * U) * Matrix.reindex e₀ e₀
            (Matrix.fromBlocks 0 0 0 A) * (star U * U) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) := by
        rw [hULeft]
        simp
  · rintro ⟨X, hBcoord⟩
    let A : Matrix (Fin n) (Fin n) ℂ :=
      Matrix.reindex e e (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)
    let Y : Matrix (Fin n) (Fin n) ℂ := Uc * A * star Uc
    have hYcoord : star Uc * Y * Uc = A := by
      dsimp only [Y]
      calc
        star Uc * (Uc * A * star Uc) * Uc =
            (star Uc * Uc) * A * (star Uc * Uc) := by
          simp only [Matrix.mul_assoc]
        _ = A := by rw [hUcLeft]; simp
    have hYfix : IsPositiveMap.stationarySupportCompression T V Y = Y :=
      (hcompressedFixed Y).mpr ⟨X, hYcoord⟩
    have hBeq : B = V * Y * Vᴴ := by
      have hBzero :
          B = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := by
        calc
          B = (U * star U) * B * (U * star U) := by rw [hURight]; simp
          _ = U * (star U * B * U) * star U := by
            simp only [Matrix.mul_assoc]
          _ = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := by
            rw [hBcoord]
      calc
        B = U * Matrix.reindex e₀ e₀ (Matrix.fromBlocks 0 0 0 A) * star U := hBzero
        _ = W * A * Wᴴ := by
          simpa only [U] using (hzeroExtension A).symm
        _ = V * Y * Vᴴ := by
          dsimp only [Y, W]
          simp only [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose,
            Matrix.mul_assoc]
    exact (hambientFixed B).mpr ⟨Y, hYfix, hBeq⟩

end

end FixedPointDensityBlocks
