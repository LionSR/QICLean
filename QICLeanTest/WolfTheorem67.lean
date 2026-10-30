/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.WolfTheorem67

/-! Boundary checks for Wolf's positive-map theorem, beyond CP maps. -/

open Matrix WolfTheorem67
open scoped Matrix ComplexOrder

namespace WolfTheorem67Test

private abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℂ
private abbrev End₂ := Module.End ℂ Mat₂

-- The theorem applies directly to the positive, trace-preserving transpose map.
example :
    HasStrictlyPositivePower (transposeLinearMapComplex (Fin 2)) ↔
      (IsPrimitive (transposeLinearMapComplex (Fin 2)) ∧
        (transposeLinearMapComplex (Fin 2)).charpoly.rootMultiplicity 1 = 1 ∧
        ∃ σ ∈ densityMatrices 2, σ.PosDef ∧ transposeLinearMapComplex (Fin 2) σ = σ) :=
  (wolf_theorem_6_7_tfae _ transposeLinearMapComplex_isPositiveMap
    transposeLinearMapComplex_isTracePreservingMap).out 1 4

-- Set-level primitivity admits an identity map with four peripheral copies of 1.
private theorem identity_isPrimitive : IsPrimitive (1 : End₂) := by
  apply isPrimitive_of_unique_norm_one _ (1 : Mat₂) (by simp) one_ne_zero
  intro μ hμ _
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  have heq : (1 : ℂ) • X = μ • X := by
    simpa using Module.End.mem_eigenspace_iff.mp hX.1
  exact ((smul_left_injective ℂ hX.2) heq).symm

private theorem identity_multiplicity : (1 : End₂).charpoly.rootMultiplicity 1 = 4 := by
  rw [LinearMap.charpoly_one, ← Polynomial.C_1, Polynomial.rootMultiplicity_X_sub_C_pow]
  simp [Mat₂, Module.finrank_matrix]

example : IsPrimitive (1 : End₂) ∧ ¬ HasSimpleFaithfulPeripheralSpectrum (1 : End₂) := by
  refine ⟨identity_isPrimitive, fun h ↦ ?_⟩
  have hm := ((simpleFaithfulPeripheralSpectrum_iff _).mp h).2.1
  rw [identity_multiplicity] at hm
  norm_num at hm

private theorem identity_not_irreducible : ¬ IsIrreducibleMap (1 : End₂) := by
  intro hirr
  have hpos : IsPositiveMap (1 : End₂) := fun _ hX ↦ hX
  obtain ⟨σ, _, hσpd, _, _⟩ :=
    hpos.exists_unique_density_fixedPoint_of_irreducible (1 : End₂) (fun _ ↦ rfl) hirr
  have hrank := finrank_eigenspace_eq_one_of_irreducible_positive
    (1 : End₂) hpos hirr (r := 1) zero_le_one hσpd (by simp)
  have hspace : Module.End.eigenspace (1 : End₂) 1 = ⊤ := by
    ext X
    simp
  change Module.finrank ℂ (Module.End.eigenspace (1 : End₂) (1 : ℂ)) = 1 at hrank
  rw [hspace, finrank_top] at hrank
  norm_num [Mat₂, Module.finrank_matrix] at hrank

-- A clause demanding irreducibility at k = 0 would exclude every map on M₂.
example (T : End₂) : ¬ IsIrreducibleMap (T ^ 0) := by
  simpa using identity_not_irreducible

-- The one-dimensional boundary permits a zeroth strict-positivity witness.
example : HasStrictlyPositivePower (1 : Module.End ℂ (Matrix (Fin 1) (Fin 1) ℂ)) := by
  refine ⟨0, fun ρ hρ ↦ ?_⟩
  have heq : ρ = 1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [Matrix.trace] using hρ.2
  simpa [heq] using (Matrix.PosDef.one : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef)

end WolfTheorem67Test
