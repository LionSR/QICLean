/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.FixedPoint.TraceNonincreasingDirectSum
import QICLean.Channel.Peripheral.DensityBlockCoordinates
import QICLean.Channel.Peripheral.RecurrentInverse

/-!
# Dynamics in Wolf's density-block coordinates

This file transports the positive trace-preserving dynamics on Wolf's asymptotic
image to the full-matrix factors in the density-block coordinates supplied by
`IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero`.

For the embedding `E` and compression `R` defined in
`QICLean.Channel.Peripheral.DensityBlockCoordinates`, the transported map is

`Abar = R.comp (A.comp E)`.

Applied to `A = T` and to the recurrent restricted inverse `A = S` from
`IsPositiveMap.exists_peripheralRestrictedInverse`, this gives Wolf's maps on the
direct sum of the full matrix factors.  The formal factor order remains
`sigma k ⊗ X k`, the reverse of Wolf's displayed tensor order and the convention
already fixed by the density-block theorem.

The results below establish only the transport needed for Wolf Theorem 6.16,
lines 1641--1659: exact intertwining with `E`, mutual inverse identities,
positivity, and preservation of the sum of the block traces.  They do not assert a
global inverse for `T`, equality of multiplicity dimensions, a CP/Kraus
classification, or the later unitary/transpose alternative.

## Reference

* M. M. Wolf, *Quantum Channels & Operations: Guided Tour*, proof of Theorem 6.16;
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
  lines 1637--1659.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators Kronecker

noncomputable section

namespace Matrix

/-- Transport an ambient matrix endomorphism to Wolf's full-matrix density-block
coordinates by first encoding, then applying the ambient map, and finally compressing. -/
noncomputable def densityBlockDynamics
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (A : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) :
    Module.End ℂ (∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :=
  (densityBlockWithZeroCompression e e₀ U hU).comp
    (A.comp (densityBlockWithZeroEmbedding e e₀ U hU sigma))

@[simp]
theorem densityBlockDynamics_apply
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (A : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ))
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    densityBlockDynamics e e₀ U hU sigma A X =
      densityBlockWithZeroCompression e e₀ U hU
        (A (densityBlockWithZeroEmbedding e e₀ U hU sigma X)) :=
  rfl

/-- Encoding after the transported action of `T` is exactly the ambient action of
`T` on encoded coordinates.  The proof uses only that the encoded family is fixed
by `T.peripheralProjection` and that the peripheral projection commutes with `T`. -/
theorem densityBlockWithZeroEmbedding_densityBlockDynamics
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hfixed : ∀ B, T.peripheralProjection B = B ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))))
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    densityBlockWithZeroEmbedding e e₀ U hU sigma
        (densityBlockDynamics e e₀ U hU sigma T X) =
      T (densityBlockWithZeroEmbedding e e₀ U hU sigma X) := by
  apply densityBlockWithZeroEmbedding_compression_of_fixed
    e e₀ U hU sigma hsigmaTrace hfixed
  calc
    T.peripheralProjection
          (T (densityBlockWithZeroEmbedding e e₀ U hU sigma X)) =
        T (T.peripheralProjection
          (densityBlockWithZeroEmbedding e e₀ U hU sigma X)) :=
      LinearMap.congr_fun T.peripheralProjection_comp _
    _ = T (densityBlockWithZeroEmbedding e e₀ U hU sigma X) := by
      rw [densityBlockWithZeroEmbedding_fixed e e₀ U hU sigma hfixed]

/-- Encoding after the transported recurrent restricted inverse `S` is exactly
the ambient action of `S` on encoded coordinates.  The absorption identity
`T.peripheralProjection.comp S = S` is the precise replacement for a nonexistent
global inverse. -/
theorem densityBlockWithZeroEmbedding_densityBlockRestrictedInverse
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    {T S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hfixed : ∀ B, T.peripheralProjection B = B ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))))
    (hPS : T.peripheralProjection.comp S = S)
    (X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) :
    densityBlockWithZeroEmbedding e e₀ U hU sigma
        (densityBlockDynamics e e₀ U hU sigma S X) =
      S (densityBlockWithZeroEmbedding e e₀ U hU sigma X) := by
  apply densityBlockWithZeroEmbedding_compression_of_fixed
    e e₀ U hU sigma hsigmaTrace hfixed
  exact LinearMap.congr_fun hPS _

/-- On density-block coordinates, the recurrent restricted inverse is a left
inverse for the transported action of `T`.  The ambient identity used is exactly
`S.comp T = T.peripheralProjection`, not a global inverse equation. -/
theorem densityBlockRestrictedInverse_comp_densityBlockDynamics
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    {T S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hfixed : ∀ B, T.peripheralProjection B = B ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))))
    (hST : S.comp T = T.peripheralProjection) :
    (densityBlockDynamics e e₀ U hU sigma S).comp
        (densityBlockDynamics e e₀ U hU sigma T) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  change densityBlockWithZeroCompression e e₀ U hU
      (S (densityBlockWithZeroEmbedding e e₀ U hU sigma
        (densityBlockDynamics e e₀ U hU sigma T X))) = X
  rw [densityBlockWithZeroEmbedding_densityBlockDynamics
    e e₀ U hU sigma hsigmaTrace hfixed X]
  rw [show S (T (densityBlockWithZeroEmbedding e e₀ U hU sigma X)) =
      T.peripheralProjection
        (densityBlockWithZeroEmbedding e e₀ U hU sigma X) from
    LinearMap.congr_fun hST _]
  rw [densityBlockWithZeroEmbedding_fixed e e₀ U hU sigma hfixed]
  exact densityBlockWithZeroCompression_embedding
    e e₀ U hU sigma hsigmaTrace X

/-- On density-block coordinates, the transported action of `T` is a left
inverse for the recurrent restricted inverse.  The proof uses the second
restricted identity `T.comp S = T.peripheralProjection` together with the
absorption identity that keeps the image of `S` inside the asymptotic image. -/
theorem densityBlockDynamics_comp_densityBlockRestrictedInverse
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    {T S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hfixed : ∀ B, T.peripheralProjection B = B ↔
      ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
        star U * B * U = Matrix.reindex e₀ e₀
          (Matrix.fromBlocks 0 0 0
            (Matrix.reindex e e
              (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k))))
    (hTS : T.comp S = T.peripheralProjection)
    (hPS : T.peripheralProjection.comp S = S) :
    (densityBlockDynamics e e₀ U hU sigma T).comp
        (densityBlockDynamics e e₀ U hU sigma S) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  change densityBlockWithZeroCompression e e₀ U hU
      (T (densityBlockWithZeroEmbedding e e₀ U hU sigma
        (densityBlockDynamics e e₀ U hU sigma S X))) = X
  rw [densityBlockWithZeroEmbedding_densityBlockRestrictedInverse
    e e₀ U hU sigma hsigmaTrace hfixed hPS X]
  rw [show T (S (densityBlockWithZeroEmbedding e e₀ U hU sigma X)) =
      T.peripheralProjection
        (densityBlockWithZeroEmbedding e e₀ U hU sigma X) from
    LinearMap.congr_fun hTS _]
  rw [densityBlockWithZeroEmbedding_fixed e e₀ U hU sigma hfixed]
  exact densityBlockWithZeroCompression_embedding
    e e₀ U hU sigma hsigmaTrace X

/-- Positivity of an ambient map descends to positivity on every full-matrix
factor in Wolf's density-block coordinates. -/
theorem densityBlockDynamics_isPositiveDirectSumMap
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigma : ∀ k, (sigma k).PosSemidef)
    {A : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hA : IsPositiveMap A) :
    IsPositiveDirectSumMap (densityBlockDynamics e e₀ U hU sigma A) := by
  intro X hX k
  apply densityBlockWithZeroCompression_posSemidef e e₀ U hU
  exact hA _
    (densityBlockWithZeroEmbedding_posSemidef
      e e₀ U hU sigma hsigma hX)

/-- Trace preservation of an ambient map descends to preservation of the total
trace of the full-matrix factors whenever its transported action intertwines
with the density-block embedding. -/
theorem densityBlockDynamics_isTracePreservingBetweenDirectSums
    {D n K : ℕ} {d m : Fin K → ℕ}
    (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
    (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
    (U : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
    (hsigmaTrace : ∀ k, (sigma k).trace = 1)
    {A : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hA : IsTracePreservingMap A)
    (hencode : ∀ X,
      densityBlockWithZeroEmbedding e e₀ U hU sigma
          (densityBlockDynamics e e₀ U hU sigma A X) =
        A (densityBlockWithZeroEmbedding e e₀ U hU sigma X)) :
    IsTracePreservingBetweenDirectSums
      (densityBlockDynamics e e₀ U hU sigma A) := by
  intro X
  calc
    ∑ k, (densityBlockDynamics e e₀ U hU sigma A X k).trace =
        (densityBlockWithZeroEmbedding e e₀ U hU sigma
          (densityBlockDynamics e e₀ U hU sigma A X)).trace :=
      (trace_densityBlockWithZeroEmbedding
        e e₀ U hU sigma hsigmaTrace _).symm
    _ = (A (densityBlockWithZeroEmbedding e e₀ U hU sigma X)).trace := by
      rw [hencode X]
    _ = (densityBlockWithZeroEmbedding e e₀ U hU sigma X).trace := hA _
    _ = ∑ k, (X k).trace :=
      trace_densityBlockWithZeroEmbedding e e₀ U hU sigma hsigmaTrace X

end Matrix

open Matrix

namespace IsPositiveMap

/-- **Wolf Theorem 6.16, density-block dynamics package.**

For a positive trace-preserving map whose trace adjoint is Schwarz, choose the
zero-extended density-block coordinates of
`IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero` for
`T.peripheralProjection`, and choose the recurrent restricted inverse `S` of
`IsPositiveMap.exists_peripheralRestrictedInverse`.  In the exact witness order
of the fixed-point theorem, this produces the transported maps

`Tbar = R.comp (T.comp E)` and `Sbar = R.comp (S.comp E)`.

They intertwine with the ambient maps under `E`, are mutually inverse on the
direct sum, are positive, and preserve the total trace.  These are precisely
the hypotheses consumed by the subsequent pure-state face-permutation argument
at Wolf Theorem 6.16, lines 1641--1659.  The conclusion is restricted to the
asymptotic-image coordinates and does not assert that `T` has a global inverse. -/
theorem exists_peripheralDensityBlockDynamics
    {D : ℕ} [NeZero D]
    {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hPos : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hAdjointSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    ∃ (n K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ Fin n)
      (e₀ : (Fin (D - n) ⊕ Fin n) ≃ Fin D)
      (U : Matrix (Fin D) (Fin D) ℂ)
      (sigma : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ)
      (S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)),
      (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (sigma k).PosDef) ∧ (∀ k, (sigma k).trace = 1) ∧
        (∀ B, T.peripheralProjection B = B ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * B * U = Matrix.reindex e₀ e₀
              (Matrix.fromBlocks 0 0 0
                (Matrix.reindex e e
                  (Matrix.blockDiagonal' fun k ↦ sigma k ⊗ₖ X k)))) ∧
        IsPositiveMap S ∧ IsTracePreservingMap S ∧
        (let Tbar := Matrix.densityBlockDynamics e e₀ U hU sigma T
         let Sbar := Matrix.densityBlockDynamics e e₀ U hU sigma S
         (∀ X, Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma (Tbar X) =
            T (Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma X)) ∧
         (∀ X, Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma (Sbar X) =
            S (Matrix.densityBlockWithZeroEmbedding e e₀ U hU sigma X)) ∧
         Sbar.comp Tbar = LinearMap.id ∧
         Tbar.comp Sbar = LinearMap.id ∧
         Matrix.IsPositiveDirectSumMap Tbar ∧
         Matrix.IsPositiveDirectSumMap Sbar ∧
         Matrix.IsTracePreservingBetweenDirectSums Tbar ∧
         Matrix.IsTracePreservingBetweenDirectSums Sbar) := by
  have hPPos : IsPositiveMap T.peripheralProjection :=
    hPos.peripheralProjection_isPositiveMap hTP
  have hPTP : IsTracePreservingMap T.peripheralProjection :=
    hPos.peripheralProjection_isTracePreservingMap hTP
  have hPAdjointSchwarz :
      IsSchwarzMap (Matrix.traceAdjointMap T.peripheralProjection) :=
    hPos.traceAdjointMap_peripheralProjection_isSchwarzMap hTP hAdjointSchwarz
  obtain ⟨n, K, d, m, e, e₀, U, sigma, hU, hd, hm, hsigma,
      hsigmaTrace, hfixed⟩ :=
    hPPos.exists_fixedPoints_densityBlocks_with_zero hPTP hPAdjointSchwarz
  obtain ⟨S, hSPos, hSTP, hST, hTS, _hSP, hPS, _hRange⟩ :=
    hPos.exists_peripheralRestrictedInverse hTP
  refine ⟨n, K, d, m, e, e₀, U, sigma, hU, S, hd, hm, hsigma,
    hsigmaTrace, hfixed, hSPos, hSTP, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.densityBlockWithZeroEmbedding_densityBlockDynamics
      e e₀ U hU sigma hsigmaTrace hfixed
  · exact Matrix.densityBlockWithZeroEmbedding_densityBlockRestrictedInverse
      e e₀ U hU sigma hsigmaTrace hfixed hPS
  · exact Matrix.densityBlockRestrictedInverse_comp_densityBlockDynamics
      e e₀ U hU sigma hsigmaTrace hfixed hST
  · exact Matrix.densityBlockDynamics_comp_densityBlockRestrictedInverse
      e e₀ U hU sigma hsigmaTrace hfixed hTS hPS
  · exact Matrix.densityBlockDynamics_isPositiveDirectSumMap
      e e₀ U hU sigma (fun k ↦ (hsigma k).posSemidef) hPos
  · exact Matrix.densityBlockDynamics_isPositiveDirectSumMap
      e e₀ U hU sigma (fun k ↦ (hsigma k).posSemidef) hSPos
  · exact Matrix.densityBlockDynamics_isTracePreservingBetweenDirectSums
      e e₀ U hU sigma hsigmaTrace hTP
        (Matrix.densityBlockWithZeroEmbedding_densityBlockDynamics
          e e₀ U hU sigma hsigmaTrace hfixed)
  · exact Matrix.densityBlockDynamics_isTracePreservingBetweenDirectSums
      e e₀ U hU sigma hsigmaTrace hSTP
        (Matrix.densityBlockWithZeroEmbedding_densityBlockRestrictedInverse
          e e₀ U hU sigma hsigmaTrace hfixed hPS)

end IsPositiveMap
