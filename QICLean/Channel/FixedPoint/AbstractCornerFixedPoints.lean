/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.AbstractAlgebra
import QICLean.Channel.FixedPoint.CornerAlgebra
import QICLean.Channel.FixedPoint.SupportCompressedDensityBlocks

/-!
# Support-corner fixed points for positive maps

This file proves Wolf Corollary 6.6 under the hypotheses printed in the
source: `T` is positive and trace preserving, and its trace adjoint satisfies
the Schwarz inequality. No Kraus representation or complete positivity is
assumed.

For a positive-semidefinite stationary matrix `ρ`, let `Q` be its support
projection. The corner-restricted adjoint fixed points
`{Y ∈ Q M_D(ℂ) Q | Q T*(Y) Q = Y}` form a star-subalgebra of the corner
algebra. Wolf states the result for a maximum-rank stationary point; the proof
here works for every positive-semidefinite stationary point, and hence includes
that source case.

The multiplication proof follows Wolf exactly: compress `T` to the support of
`ρ`, identify the displayed set with the fixed points of the compressed trace
adjoint, apply the full-support Schwarz fixed-point algebra theorem, and extend
the product back through the support isometry.

## Main declarations

* `IsPositiveMap.stationaryCornerAdjointFixedPointsStarSubalgebra`: Wolf
  Corollary 6.6 and Equation (6.61), under the source hypotheses.
* `IsPositiveMap.mem_stationaryCornerAdjointFixedPointsStarSubalgebra`: the
  exact displayed membership condition in Equation (6.61).

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 6.6 and
  Equation (6.61); local source
  `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`, lines 1423--1437.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

namespace IsPositiveMap

/-- Multiplication closure for the support-corner fixed points of the trace
adjoint of a positive trace-preserving map whose trace adjoint is Schwarz.

The proof is the support-compression route in Wolf Corollary 6.6: the
compressed map has a positive-definite stationary point, so Wolf Theorem 6.12
applies to its trace adjoint. Source: local Wolf TeX, lines 1423--1437. -/
theorem stationaryCornerAdjointFixed_mul
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {ρ : Mat} (hρ : ρ.PosSemidef) (hρfix : T ρ = ρ)
    {Y₁ Y₂ : Mat}
    (hY₁mem : Kraus.stationaryProj hρ * Y₁ * Kraus.stationaryProj hρ = Y₁)
    (hY₂mem : Kraus.stationaryProj hρ * Y₂ * Kraus.stationaryProj hρ = Y₂)
    (hY₁fix : Kraus.stationaryProj hρ * Matrix.traceAdjointMap T Y₁ *
      Kraus.stationaryProj hρ = Y₁)
    (hY₂fix : Kraus.stationaryProj hρ * Matrix.traceAdjointMap T Y₂ *
      Kraus.stationaryProj hρ = Y₂) :
    Kraus.stationaryProj hρ * Matrix.traceAdjointMap T (Y₁ * Y₂) *
      Kraus.stationaryProj hρ = Y₁ * Y₂ := by
  classical
  let Q : Mat := Kraus.stationaryProj hρ
  obtain ⟨n, V, hV, hVrange⟩ :=
    (Kraus.isOrthogonalProjection_stationaryProj hρ).exists_range_isometry
  let T' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    stationarySupportCompression T V
  let E : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Matrix.traceAdjointMap T'
  have hT'pos : IsPositiveMap T' :=
    stationarySupportCompression_isPositiveMap hT V
  have hT'tp : IsTracePreservingMap T' :=
    stationarySupportCompression_isTracePreservingMap
      hT hTP hρ hρfix V hV hVrange
  have hEpos : IsPositiveMap E := hT'pos.traceAdjointMap
  have hESchwarz : IsSchwarzMap E := by
    simpa only [E, T'] using
      hSchwarz.traceAdjointMap_stationarySupportCompression hT V hV
  obtain ⟨σ, hσpd, hσfix⟩ :=
    exists_posDef_fixedPoint_stationarySupportCompression
      hρ hρfix V hV hVrange
  have hσEfix : Matrix.traceAdjointMap E σ = σ := by
    change Matrix.traceAdjointMap (Matrix.traceAdjointMap T') σ = σ
    rw [Matrix.traceAdjointMap_traceAdjointMap]
    simpa only [T'] using hσfix
  have hEapply (X : Matrix (Fin n) (Fin n) ℂ) :
      E X = Vᴴ * Matrix.traceAdjointMap T (V * X * Vᴴ) * V := by
    change Matrix.traceAdjointMap T' X = _
    rw [Matrix.traceAdjointMap_stationarySupportCompression]
    rfl
  have hexpand {Y : Mat} (hY : Q * Y * Q = Y) :
      V * (Vᴴ * Y * V) * Vᴴ = Y := by
    calc
      V * (Vᴴ * Y * V) * Vᴴ = (V * Vᴴ) * Y * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = Q * Y * Q := by rw [hVrange]
      _ = Y := hY
  have hcompressFixed {Y : Mat}
      (hYmem : Q * Y * Q = Y)
      (hYfix : Q * Matrix.traceAdjointMap T Y * Q = Y) :
      E (Vᴴ * Y * V) = Vᴴ * Y * V := by
    rw [hEapply]
    rw [hexpand hYmem]
    calc
      Vᴴ * Matrix.traceAdjointMap T Y * V =
          Vᴴ * (Q * Matrix.traceAdjointMap T Y * Q) * V := by
        rw [show Q = V * Vᴴ by simpa only [Q] using hVrange.symm]
        calc
          Vᴴ * Matrix.traceAdjointMap T Y * V =
              (Vᴴ * V) * Vᴴ * Matrix.traceAdjointMap T Y * V * (Vᴴ * V) := by
            rw [hV]
            simp
          _ = Vᴴ * ((V * Vᴴ) * Matrix.traceAdjointMap T Y * (V * Vᴴ)) * V := by
            simp only [Matrix.mul_assoc]
      _ = Vᴴ * Y * V := by rw [hYfix]
  let X₁ : Matrix (Fin n) (Fin n) ℂ := Vᴴ * Y₁ * V
  let X₂ : Matrix (Fin n) (Fin n) ℂ := Vᴴ * Y₂ * V
  have hX₁fix : E X₁ = X₁ := by
    simpa only [X₁] using hcompressFixed hY₁mem hY₁fix
  have hX₂fix : E X₂ = X₂ := by
    simpa only [X₂] using hcompressFixed hY₂mem hY₂fix
  have hX₁₂fix : E (X₁ * X₂) = X₁ * X₂ :=
    SchwarzMap.mul_mem_fixedPoints E hEpos hESchwarz hσpd hσEfix hX₁fix hX₂fix
  have hQidem : Q * Q = Q := by
    simpa only [Q] using (Kraus.isOrthogonalProjection_stationaryProj hρ).2
  have hQY₁ : Q * Y₁ = Y₁ := by
    conv_lhs => rw [← hY₁mem]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQidem]
    exact hY₁mem
  have hY₂Q : Y₂ * Q = Y₂ := by
    conv_lhs => rw [← hY₂mem]
    rw [Matrix.mul_assoc, hQidem]
    exact hY₂mem
  have hY₁Q : Y₁ * Q = Y₁ := by
    conv_lhs => rw [← hY₁mem]
    rw [Matrix.mul_assoc, hQidem]
    exact hY₁mem
  have hmulExpand : V * (X₁ * X₂) * Vᴴ = Y₁ * Y₂ := by
    dsimp only [X₁, X₂]
    calc
      V * ((Vᴴ * Y₁ * V) * (Vᴴ * Y₂ * V)) * Vᴴ =
          (V * Vᴴ) * Y₁ * (V * Vᴴ) * Y₂ * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = Q * Y₁ * Q * Y₂ * Q := by rw [hVrange]
      _ = Y₁ * Y₂ := by
        calc
          Q * Y₁ * Q * Y₂ * Q = (Q * Y₁) * Q * (Y₂ * Q) := by
            simp only [Matrix.mul_assoc]
          _ = Y₁ * Y₂ := by rw [hQY₁, hY₁Q, hY₂Q]
  calc
    Q * Matrix.traceAdjointMap T (Y₁ * Y₂) * Q =
        (V * Vᴴ) * Matrix.traceAdjointMap T
          (V * (X₁ * X₂) * Vᴴ) * (V * Vᴴ) := by
      rw [hVrange, hmulExpand]
    _ = V * (Vᴴ * Matrix.traceAdjointMap T
          (V * (X₁ * X₂) * Vᴴ) * V) * Vᴴ := by
      simp only [Matrix.mul_assoc]
    _ = V * E (X₁ * X₂) * Vᴴ := by rw [hEapply]
    _ = V * (X₁ * X₂) * Vᴴ := by rw [hX₁₂fix]
    _ = Y₁ * Y₂ := hmulExpand

/-- The support projection is the unit of the support-corner adjoint fixed
points. This is unitality of the trace adjoint after stationary-support
compression. -/
theorem stationaryCornerAdjointFixed_one
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    {ρ : Mat} (hρ : ρ.PosSemidef) (hρfix : T ρ = ρ) :
    Kraus.stationaryProj hρ *
        Matrix.traceAdjointMap T (Kraus.stationaryProj hρ) *
      Kraus.stationaryProj hρ = Kraus.stationaryProj hρ := by
  classical
  let Q : Mat := Kraus.stationaryProj hρ
  obtain ⟨n, V, hV, hVrange⟩ :=
    (Kraus.isOrthogonalProjection_stationaryProj hρ).exists_range_isometry
  let T' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    stationarySupportCompression T V
  have hT'tp : IsTracePreservingMap T' :=
    stationarySupportCompression_isTracePreservingMap
      hT hTP hρ hρfix V hV hVrange
  have hEone : Matrix.traceAdjointMap T' (1 : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    isTracePreservingMap_iff_traceAdjointMap_one.mp hT'tp
  have hEapply :
      Matrix.traceAdjointMap T' (1 : Matrix (Fin n) (Fin n) ℂ) =
        Vᴴ * Matrix.traceAdjointMap T
          (V * (1 : Matrix (Fin n) (Fin n) ℂ) * Vᴴ) * V := by
    rw [Matrix.traceAdjointMap_stationarySupportCompression]
    rfl
  change Kraus.stationaryProj hρ *
      Matrix.traceAdjointMap T (Kraus.stationaryProj hρ) *
    Kraus.stationaryProj hρ = Kraus.stationaryProj hρ
  rw [← hVrange]
  calc
    (V * Vᴴ) * Matrix.traceAdjointMap T (V * Vᴴ) * (V * Vᴴ) =
        V * (Vᴴ * Matrix.traceAdjointMap T
          (V * (1 : Matrix (Fin n) (Fin n) ℂ) * Vᴴ) * V) * Vᴴ := by
      simp [Matrix.mul_assoc]
    _ = V * Matrix.traceAdjointMap T'
          (1 : Matrix (Fin n) (Fin n) ℂ) * Vᴴ := by rw [hEapply]
    _ = V * (1 : Matrix (Fin n) (Fin n) ℂ) * Vᴴ := by rw [hEone]
    _ = V * Vᴴ := by rw [Matrix.mul_one]

/-- **Wolf Corollary 6.6, Equation (6.61).**

Let `T` be positive and trace preserving, with Schwarz trace adjoint, and let
`Q` be the support projection of a positive-semidefinite stationary matrix
`ρ`. Then
`{Y ∈ Q M_D(ℂ) Q | Q T*(Y) Q = Y}` is a star-subalgebra of the corner
algebra `Q M_D(ℂ) Q`.

Wolf chooses `ρ` of maximum rank. The support-compression proof only uses that
`ρ` is positive semidefinite and stationary, so this statement strengthens the
choice of support while retaining exactly the source hypotheses on `T`. No
complete positivity or Kraus representation is assumed. -/
noncomputable def stationaryCornerAdjointFixedPointsStarSubalgebra
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {ρ : Mat} (hρ : ρ.PosSemidef) (hρfix : T ρ = ρ) :
    letI hQ : IsIdempotentElem (Kraus.stationaryProj hρ) :=
      (Kraus.isOrthogonalProjection_stationaryProj hρ).2
    letI : Semiring hQ.Corner := instSemiringCorner _ hQ
    letI : Algebra ℂ hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
    letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
      (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
    letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
      (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
    letI : StarModule ℂ hQ.Corner := MatrixCorner.cornerStarModuleComplex hQ
      (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
    StarSubalgebra ℂ hQ.Corner :=
  letI hQ : IsIdempotentElem (Kraus.stationaryProj hρ) :=
    (Kraus.isOrthogonalProjection_stationaryProj hρ).2
  letI : Semiring hQ.Corner := instSemiringCorner _ hQ
  letI : Algebra ℂ hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
  letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
    (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
  letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
    (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
  letI : StarModule ℂ hQ.Corner := MatrixCorner.cornerStarModuleComplex hQ
    (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
  let Q : Mat := Kraus.stationaryProj hρ
  have hQherm : Qᴴ = Q :=
    (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
  { carrier := {Y : hQ.Corner |
      Q * Matrix.traceAdjointMap T Y.1 * Q = Y.1}
    zero_mem' := by
      change Q * Matrix.traceAdjointMap T (0 : Mat) * Q = (0 : Mat)
      simp
    add_mem' := by
      intro X Y hX hY
      change Q * Matrix.traceAdjointMap T (X.1 + Y.1) * Q = X.1 + Y.1
      rw [map_add, Matrix.mul_add, Matrix.add_mul, hX, hY]
    one_mem' := by
      change Q * Matrix.traceAdjointMap T Q * Q = Q
      exact stationaryCornerAdjointFixed_one hT hTP hρ hρfix
    mul_mem' := by
      intro X Y hX hY
      change Q * Matrix.traceAdjointMap T (X.1 * Y.1) * Q = X.1 * Y.1
      have hXmem : Q * X.1 * Q = X.1 := by
        obtain ⟨hL, hR⟩ := (Subsemigroup.mem_corner_iff hQ).mp X.2
        rw [Matrix.mul_assoc, hR, hL]
      have hYmem : Q * Y.1 * Q = Y.1 := by
        obtain ⟨hL, hR⟩ := (Subsemigroup.mem_corner_iff hQ).mp Y.2
        rw [Matrix.mul_assoc, hR, hL]
      exact stationaryCornerAdjointFixed_mul
        hT hTP hSchwarz hρ hρfix hXmem hYmem hX hY
    algebraMap_mem' := by
      intro c
      change Q * Matrix.traceAdjointMap T (c • Q) * Q = c • Q
      rw [map_smul, Matrix.mul_smul, Matrix.smul_mul,
        stationaryCornerAdjointFixed_one hT hTP hρ hρfix]
    star_mem' := by
      intro X hX
      change Q * Matrix.traceAdjointMap T X.1ᴴ * Q = X.1ᴴ
      rw [hT.traceAdjointMap.map_conjTranspose]
      have h := congrArg Matrix.conjTranspose hX
      simpa [Matrix.conjTranspose_mul, hQherm, Matrix.mul_assoc] using h }

/-- Membership in the source-general corner fixed-point star-algebra is exactly
the displayed condition `Q T*(Y) Q = Y` of Wolf Equation (6.61). -/
@[simp] theorem mem_stationaryCornerAdjointFixedPointsStarSubalgebra
    {T : Mat →ₗ[ℂ] Mat} (hT : IsPositiveMap T)
    (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T))
    {ρ : Mat} (hρ : ρ.PosSemidef) (hρfix : T ρ = ρ)
    (hQ : IsIdempotentElem (Kraus.stationaryProj hρ) :=
      (Kraus.isOrthogonalProjection_stationaryProj hρ).2)
    (Y : hQ.Corner) :
    letI : Semiring hQ.Corner := instSemiringCorner _ hQ
    letI : Algebra ℂ hQ.Corner := MatrixCorner.instAlgebraComplexCorner hQ
    letI : Star hQ.Corner := MatrixCorner.cornerStar hQ
      (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
    letI : StarRing hQ.Corner := MatrixCorner.cornerStarRing hQ
      (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
    letI : StarModule ℂ hQ.Corner := MatrixCorner.cornerStarModuleComplex hQ
      (Kraus.isOrthogonalProjection_stationaryProj hρ).1.eq
    Y ∈ stationaryCornerAdjointFixedPointsStarSubalgebra
      hT hTP hSchwarz hρ hρfix ↔
      Kraus.stationaryProj hρ * Matrix.traceAdjointMap T Y.1 *
        Kraus.stationaryProj hρ = Y.1 :=
  Iff.rfl

end IsPositiveMap
