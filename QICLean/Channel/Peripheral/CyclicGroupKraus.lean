/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Peripheral.ClosureFixedPointKraus
import QICLean.Channel.Peripheral.AbstractEigenvectors
import QICLean.Channel.Peripheral.CyclicGroup
import QICLean.Channel.Schwarz.MultiplicativeDomainFull

/-!
# Finite-Kraus specializations of peripheral cyclicity

These historical declarations retain their signatures. Product closure is
specialized from the abstract Schwarz theorem, and cyclicity uses the common
finite-set argument. The source-general four-clause result, including the
order bound, is `SchwarzMap.wolf_theorem_6_6` in `IrreducibleSchwarz`.

## References

* Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

variable {d D : ℕ}

/-- Peripheral product closure for a finite Kraus map, specialized from
Wolf's abstract positive unital irreducible Schwarz-map theorem. The historical
adjoint-weight arguments are retained for downstream compatibility. -/
theorem peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (Kraus.mapLM K)) :
    ∀ μ ν : ℂ,
      μ ∈ peripheralEigenvalues (Kraus.mapLM K) →
      ν ∈ peripheralEigenvalues (Kraus.mapLM K) →
        μ * ν ∈ peripheralEigenvalues (Kraus.mapLM K) := by
  have _ := hρ
  have _ := hfix
  intro μ ν hμ hν
  exact SchwarzMap.peripheralEigenvalues_mul_mem (Kraus.mapLM K)
    (Kraus.isPositiveMap_mapLM K)
    (by simpa only [Kraus.mapLM_apply] using
      Kraus.map_one_of_isUnital K h_unital)
    (KadisonSchwarz.krausMap_isSchwarzMap K h_unital) hIrr hμ hν

/-- Cyclicity for a finite Kraus map, by the common finite-set theorem.
Wolf's source-general result with all four clauses and the order bound is
`SchwarzMap.wolf_theorem_6_6`. The historical stationary-weight arguments are
retained for downstream compatibility. -/
theorem peripheralEigenvalues_eq_range_primitiveRoot [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (h_unital : KadisonSchwarz.IsUnitalKraus (d := d) (D := D) K)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (Kraus.mapLM K)) :
    let E := Kraus.mapLM K
    let hfin := peripheralEigenvalues_finite (f := E)
    let m := hfin.toFinset.card
    0 < m ∧
    ∃ (γ : ℂ), IsPrimitiveRoot γ m ∧
      peripheralEigenvalues E = Set.range (fun j : Fin m => γ ^ (j : ℕ)) := by
  obtain ⟨hm, -, hγ, hperiph⟩ :=
    peripheralEigenvalues_eq_range_exp_of_mul_mem (Kraus.mapLM K)
      (one_mem_peripheralEigenvalues (Kraus.mapLM K) 1
        (by simpa only [Kraus.mapLM_apply] using
          Kraus.map_one_of_isUnital K h_unital) one_ne_zero)
      (peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint
        K h_unital ρ hρ hfix hIrr)
  exact ⟨hm, _, hγ, hperiph⟩

end Kraus
