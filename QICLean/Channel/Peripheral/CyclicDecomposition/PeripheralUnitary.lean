/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap
import QICLean.Channel.Peripheral.CyclicDecomposition.Basic
import QICLean.Channel.Peripheral.IrreducibleSchwarz
import QICLean.Channel.Schwarz.MultiplicativeDomainFull

/-!
# Finite-Kraus specializations of the abstract peripheral-unitary theorem

The established declarations retain their signatures for downstream users.
Their proofs use the positive unital irreducible Schwarz-map development;
complete positivity is used only to discharge its positivity and Schwarz
hypotheses. No stationary weight is required by the abstract theorem.

## References

* Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

/-- Every fixed point of an irreducible unital finite Kraus map is scalar,
by the abstract positive-map simplicity theorem (Wolf Theorem 6.6). -/
theorem fixed_eq_scalar_of_irreducible_unital
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (hIrr : IsIrreducibleMap (mapLM K))
    (X : MatrixAlg D)
    (hfix : mapLM K X = X) :
    ∃ c : ℂ, X = c • 1 := by
  exact SchwarzMap.fixed_eq_scalar_of_irreducible_unital (mapLM K)
    (isPositiveMap_mapLM K)
    (by simpa only [mapLM_apply] using map_one_of_isUnital K hUnital)
    hIrr hfix

/-- A peripheral eigenvalue of an irreducible unital finite Kraus map has a
unitary eigenvector, by the abstract Schwarz theorem (Wolf Theorem 6.6).
The historical adjoint-weight arguments are retained for compatibility;
the faithful stationary weight is now derived internally. -/
theorem exists_peripheral_unitary_of_irreducible_schwarz
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (mapLM K))
    {γ : ℂ}
    (hγ : γ ∈ peripheralEigenvalues (mapLM K)) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      mapLM K (U : MatrixAlg D) = γ • (U : MatrixAlg D) := by
  have _ := hρ
  have _ := hρfix
  exact SchwarzMap.exists_peripheral_unitary (mapLM K)
    (isPositiveMap_mapLM K)
    (by simpa only [mapLM_apply] using map_one_of_isUnital K hUnital)
    (KadisonSchwarz.krausMap_isSchwarzMap K hUnital) hIrr hγ

/-- Powers of a peripheral unitary remain eigenvectors, by the abstract
multiplicative-domain theorem (Wolf Theorem 6.6(3)). -/
theorem map_powers_of_peripheral_unitary
    {r D : ℕ} [NeZero D]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    {γ : ℂ}
    (hγ : γ ∈ peripheralEigenvalues (mapLM K))
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (hU : mapLM K (U : MatrixAlg D) = γ • (U : MatrixAlg D)) :
    ∀ k : ℕ,
      mapLM K ((U : MatrixAlg D) ^ k) =
        γ ^ k • ((U : MatrixAlg D) ^ k) := by
  have _ := hρ
  have _ := hρfix
  exact SchwarzMap.map_powers_of_peripheral_unitary (mapLM K)
    (isPositiveMap_mapLM K)
    (by simpa only [mapLM_apply] using map_one_of_isUnital K hUnital)
    (KadisonSchwarz.krausMap_isSchwarzMap K hUnital) hγ.2 U hU

/-- A peripheral generator can be normalized to have `m`-th power one,
by the abstract Schwarz theorem (Wolf Theorem 6.6(4)). -/
theorem exists_normalized_peripheral_unitary_of_irreducible_schwarz
    {r D m : ℕ} [NeZero D] [NeZero m]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (mapLM K))
    {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (hγ : γ ∈ peripheralEigenvalues (mapLM K)) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      mapLM K (U : MatrixAlg D) = γ • (U : MatrixAlg D) ∧
      ((U : MatrixAlg D) ^ m = 1) := by
  have _ := hρ
  have _ := hρfix
  exact SchwarzMap.exists_normalized_peripheral_unitary (mapLM K)
    (isPositiveMap_mapLM K)
    (by simpa only [mapLM_apply] using map_one_of_isUnital K hUnital)
    (KadisonSchwarz.krausMap_isSchwarzMap K hUnital) hIrr hγprim hγ

end Kraus
