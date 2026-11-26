/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausMap.KrausMap
import QICLean.Channel.Peripheral.Irreducible.CornerRestriction
import QICLean.Channel.Peripheral.Irreducible.AbstractEigenvectors
import QICLean.Channel.Schwarz.MultiplicativeDomainFull
import QICLean.Channel.Peripheral.Irreducible.CyclicProjections

/-!
# Finite-Kraus specializations of the abstract peripheral-unitary theorem

The established declarations retain their signatures for downstream users.
Their proofs use the positive unital irreducible Schwarz-map development;
complete positivity is used only to discharge its positivity and Schwarz
hypotheses. No stationary weight is required by the abstract theorem.

It also contains the following results.

* `Kraus.exists_cyclic_decomposition_of_irreducible_schwarz`: cyclic decompositions for irreducible
  finite Kraus maps.

## References

* Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace Kraus

section PeripheralUnitary

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

end PeripheralUnitary

section CyclicDecomposition

/-!
## Cyclic decompositions for irreducible finite Kraus maps

This file combines the peripheral-unitary and cyclic-projection constructions
for finite Kraus maps.

**Scope restriction (complete positivity and adjoint fixed point):** Wolf
Theorem 6.6 assumes an irreducible positive unital Schwarz map. The declaration
here uses a finite Kraus family and a positive-definite fixed point of its
adjoint. See `docs/paper-gaps/wolf_thm6_6_kraus_scope.tex`.

### Main statements

* `exists_cyclic_decomposition_of_irreducible_schwarz` — cyclic
  decomposition for irreducible unital finite Kraus maps.

### References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.6]
-/

/-- A cyclic decomposition for an irreducible unital finite Kraus map,
assuming that its peripheral spectrum is generated by a primitive `m`-th root `γ`.

**Scope restriction (complete positivity and adjoint fixed point):** This is the
finite-Kraus specialization of the cyclic decomposition in Wolf Theorem 6.6,
with a positive-definite adjoint fixed point assumed explicitly. See
`docs/paper-gaps/wolf_thm6_6_kraus_scope.tex`. -/
theorem exists_cyclic_decomposition_of_irreducible_schwarz
    {r D m : ℕ} [NeZero D] [NeZero m]
    (K : Fin r → MatrixAlg D)
    (hUnital : KadisonSchwarz.IsUnitalKraus (d := r) (D := D) K)
    (ρ : MatrixAlg D) (hρ : ρ.PosDef)
    (hρfix : Kraus.adjointMap K ρ = ρ)
    (hIrr : IsIrreducibleMap (Kraus.mapLM K))
    {γ : ℂ} (hγprim : IsPrimitiveRoot γ m)
    (hperiph : peripheralEigenvalues (Kraus.mapLM K) =
      Set.range (fun j : Fin m => γ ^ (j : ℕ))) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      ∃ P : Fin m → MatrixAlg D,
        Kraus.mapLM K (U : MatrixAlg D) = γ • (U : MatrixAlg D) ∧
        (∀ k : ℕ,
          Kraus.mapLM K ((U : MatrixAlg D) ^ k) =
            γ ^ k • ((U : MatrixAlg D) ^ k)) ∧
        ((U : MatrixAlg D) ^ m = 1) ∧
        (∀ k : Fin m, IsOrthogonalProjection (P k)) ∧
        (∑ k : Fin m, P k = 1) ∧
        ((U : MatrixAlg D) = ∑ k : Fin m, γ ^ (k : ℕ) • P k) ∧
        (∀ k : Fin m, Kraus.mapLM K (P (k + 1)) = P k) := by
  have hγ : γ ∈ peripheralEigenvalues (Kraus.mapLM K) := by
    rw [hperiph]
    by_cases hm1 : m = 1
    · subst hm1
      simp only [
        IsPrimitiveRoot.one_right_iff.mp hγprim, Fin.val_eq_zero, pow_zero, Set.range_const,
        Set.mem_singleton_iff
      ]
    · have hm0 : m ≠ 0 := NeZero.ne m
      have hm_gt : 1 < m := Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hm0, hm1⟩
      exact ⟨⟨1, hm_gt⟩, by simp only [pow_one]⟩
  obtain ⟨U, hU, hUm⟩ :=
    exists_normalized_peripheral_unitary_of_irreducible_schwarz
      (K := K) hUnital ρ hρ hρfix hIrr hγprim hγ
  have hPow :
      ∀ k : ℕ,
        Kraus.mapLM K ((U : MatrixAlg D) ^ k) =
          γ ^ k • ((U : MatrixAlg D) ^ k) :=
    map_powers_of_peripheral_unitary
      (K := K) hUnital ρ hρ hρfix hγ U hU
  obtain ⟨P, hPproj, hPsum, hUspec, hcyclic⟩ :=
    exists_cyclic_projections_of_peripheral_unitary
      (T := Kraus.mapLM K) hγprim U hUm hPow
  exact ⟨U, P, hU, hPow, hUm, hPproj, hPsum, hUspec, hcyclic⟩

end CyclicDecomposition

end Kraus
