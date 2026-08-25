/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.IrreducibleChannel
import QICLean.Kraus.CPPrimitive
import QICLean.Kraus.InvariantProjection
import QICLean.Kraus.PrimitiveFixedPoint.Basic

/-!
# Primitive fixed points from peripheral primitivity

This module turns peripheral-spectrum primitivity of a trace-preserving finite Kraus map
into complementary fixed-point-gap data. The results are stated directly for
`Kraus.mapLM`: no transfer-map or matrix-product-state compatibility layer is involved.

For an irreducible Kraus family, the channel has a nonzero positive-semidefinite fixed
point. Peripheral primitivity forces every eigenvalue of the complementary map to have
modulus below one, hence its spectral radius is below one. Injective families inherit the
same conclusions through map irreducibility.

## Main declarations

* `Kraus.mapLM_fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible`
* `Kraus.mapLM_fixedPoint_eq_zero_of_trace_eq_zero`
* `Kraus.spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible`
* `Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible`
* `Kraus.spectralRadius_compl_lt_one_of_peripheralPrimitive`
* `Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive`
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators Kraus
open Matrix

namespace Kraus

variable {d D : ℕ}

/-- For an irreducible trace-preserving finite Kraus family, every traceless fixed point
of its Kraus map is zero. -/
theorem mapLM_fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hIrr : IsIrreducibleFamily K)
    (hTP : IsTP K)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hXfix : mapLM K X = X)
    (htrX : Matrix.trace X = 0) :
    X = 0 :=
  fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible_channel
    (isChannel_mapLM K hTP)
    (isIrreducibleMap_mapLM_of_isIrreducibleFamily K hIrr) X hXfix htrX

/-- For an injective trace-preserving finite Kraus family, every traceless fixed point of
its Kraus map is zero. -/
theorem mapLM_fixedPoint_eq_zero_of_trace_eq_zero
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hInj : IsInjective K)
    (hTP : IsTP K)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (hXfix : mapLM K X = X)
    (htrX : Matrix.trace X = 0) :
    X = 0 := by
  have hIrr : IsIrreducibleFamily K :=
    isIrreducibleFamily_of_isIrreducibleMap_mapLM K
      (injective_implies_irreducibleCP K hInj)
  exact mapLM_fixedPoint_eq_zero_of_trace_eq_zero_of_irreducible
    K hIrr hTP X hXfix htrX

/-- Peripheral primitivity of the Kraus map of an irreducible trace-preserving family
produces a nonzero positive-semidefinite fixed point whose complementary map has spectral
radius below one. -/
theorem spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hIrr : IsIrreducibleFamily K)
    (hTP : IsTP K)
    (hPrim : _root_.IsPrimitive (mapLM K)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ mapLM K ρ = ρ ∧
        ∃ htr : Matrix.trace ρ ≠ 0,
          spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              (mapLM K - fixedPointProj (D := D) ρ htr)) < 1 := by
  have hCh : IsChannel (mapLM K) := isChannel_mapLM K hTP
  have hIrrMap : IsIrreducibleMap (mapLM K) :=
    isIrreducibleMap_mapLM_of_isIrreducibleFamily K hIrr
  obtain ⟨ρ, hρ_psd, hρ_ne, hρ_fix⟩ :=
    hCh.exists_posSemidef_fixedPoint (E := mapLM K) (NeZero.pos D)
  obtain ⟨htr, hgap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (mapLM K) hCh hIrrMap hPrim ρ hρ_psd hρ_ne hρ_fix
  exact ⟨ρ, hρ_psd, hρ_ne, hρ_fix, htr, hgap⟩

/-- Peripheral primitivity of the Kraus map of an irreducible trace-preserving family
implies the existence of a primitive fixed point. -/
theorem hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hIrr : IsIrreducibleFamily K)
    (hTP : IsTP K)
    (hPrim : _root_.IsPrimitive (mapLM K)) :
    HasPrimitiveFixedPoint K := by
  rcases spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
      K hIrr hTP hPrim with ⟨ρ, hρ_psd, hρ_ne, hρ_fix, htr, hgap⟩
  refine ⟨ρ, hTP, hρ_ne, hρ_psd, hρ_fix, ?_⟩
  simpa only using hgap

/-- Peripheral primitivity of the Kraus map of an injective trace-preserving family
produces a nonzero positive-semidefinite fixed point whose complementary map has spectral
radius below one. -/
theorem spectralRadius_compl_lt_one_of_peripheralPrimitive
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hInj : IsInjective K)
    (hTP : IsTP K)
    (hPrim : _root_.IsPrimitive (mapLM K)) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ,
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ mapLM K ρ = ρ ∧
        ∃ htr : Matrix.trace ρ ≠ 0,
          spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              (mapLM K - fixedPointProj (D := D) ρ htr)) < 1 := by
  have hIrr : IsIrreducibleFamily K :=
    isIrreducibleFamily_of_isIrreducibleMap_mapLM K
      (injective_implies_irreducibleCP K hInj)
  exact spectralRadius_compl_lt_one_of_peripheralPrimitive_of_irreducible
    K hIrr hTP hPrim

/-- Peripheral primitivity of the Kraus map of an injective trace-preserving family
implies the existence of a primitive fixed point. -/
theorem hasPrimitiveFixedPoint_of_peripheralPrimitive
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hInj : IsInjective K)
    (hTP : IsTP K)
    (hPrim : _root_.IsPrimitive (mapLM K)) :
    HasPrimitiveFixedPoint K := by
  rcases spectralRadius_compl_lt_one_of_peripheralPrimitive
      K hInj hTP hPrim with ⟨ρ, hρ_psd, hρ_ne, hρ_fix, htr, hgap⟩
  refine ⟨ρ, hTP, hρ_ne, hρ_psd, hρ_fix, ?_⟩
  simpa only using hgap

end Kraus
