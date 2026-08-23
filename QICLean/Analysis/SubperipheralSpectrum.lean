/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Wolf's subperipheral spectral modulus

For a finite-dimensional complex endomorphism `T`, Wolf denotes by `μ` the
largest modulus of an eigenvalue in the open unit disc.  This file gives that
quantity one shared definition.  It uses `Module.End.HasEigenvalue`, which is
equivalent to membership in the spectrum in finite dimension.

The empty case is totalized by `μ = 0`.  When the subperipheral spectrum is
nonempty, finiteness shows that the supremum is attained and is strictly less
than one.  Notice that `μ = 0` does *not* imply that this spectrum is empty:
it may consist only of the zero eigenvalue.

Source: Wolf (2012), Chapter 8, Theorem "Asymptotic convergence I",
local source `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines
1225--1228.
-/

noncomputable section

namespace Module.End

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Wolf's **subperipheral spectrum**: eigenvalues in the open unit disc. -/
def subperipheralSpectrum (T : Module.End ℂ V) : Set ℂ :=
  {z | T.HasEigenvalue z ∧ ‖z‖ < 1}

/-- Wolf's `μ`: the largest modulus of a subperipheral eigenvalue.

The supremum is `0` when the subperipheral spectrum is empty. -/
def subperipheralModulus (T : Module.End ℂ V) : ℝ :=
  sSup ((fun z : ℂ ↦ ‖z‖) '' T.subperipheralSpectrum)

/-- The convention for an empty subperipheral spectrum is `μ = 0`. -/
theorem subperipheralModulus_eq_zero_of_empty (T : Module.End ℂ V)
    (hT : T.subperipheralSpectrum = ∅) : T.subperipheralModulus = 0 := by
  simp [subperipheralModulus, hT]

variable [FiniteDimensional ℂ V]

/-- The subperipheral spectrum of a finite-dimensional endomorphism is finite. -/
theorem subperipheralSpectrum_finite (T : Module.End ℂ V) :
    T.subperipheralSpectrum.Finite := by
  apply T.finite_hasEigenvalue.subset
  intro z hz
  exact hz.1

/-- Spectral form of Wolf's definition in finite dimension. -/
theorem mem_subperipheralSpectrum_iff_mem_spectrum (T : Module.End ℂ V) {z : ℂ} :
    z ∈ T.subperipheralSpectrum ↔ z ∈ spectrum ℂ T ∧ ‖z‖ < 1 := by
  simp only [subperipheralSpectrum, Set.mem_ofPred_eq,
    Module.End.hasEigenvalue_iff_mem_spectrum]

/-- When the subperipheral spectrum is nonempty, some eigenvalue realizes
Wolf's largest modulus `μ`. -/
theorem exists_norm_eq_subperipheralModulus (T : Module.End ℂ V)
    (hT : T.subperipheralSpectrum.Nonempty) :
    ∃ z ∈ T.subperipheralSpectrum, ‖z‖ = T.subperipheralModulus := by
  have hfinite : ((fun z : ℂ ↦ ‖z‖) '' T.subperipheralSpectrum).Finite :=
    T.subperipheralSpectrum_finite.image _
  have hnonempty : ((fun z : ℂ ↦ ‖z‖) '' T.subperipheralSpectrum).Nonempty :=
    hT.image _
  have hmem := hnonempty.csSup_mem hfinite
  rcases hmem with ⟨z, hz, hnorm⟩
  exact ⟨z, hz, hnorm⟩

/-- Every subperipheral eigenvalue has modulus at most Wolf's `μ`. -/
theorem norm_le_subperipheralModulus (T : Module.End ℂ V) {z : ℂ}
    (hz : z ∈ T.subperipheralSpectrum) : ‖z‖ ≤ T.subperipheralModulus := by
  apply le_csSup
  · exact (T.subperipheralSpectrum_finite.image _).bddAbove
  · exact ⟨z, hz, rfl⟩

/-- Wolf's `μ` is nonnegative, including under the empty-set convention. -/
theorem subperipheralModulus_nonneg (T : Module.End ℂ V) :
    0 ≤ T.subperipheralModulus := by
  by_cases hT : T.subperipheralSpectrum.Nonempty
  · obtain ⟨z, hz, hnorm⟩ := T.exists_norm_eq_subperipheralModulus hT
    rw [← hnorm]
    exact norm_nonneg z
  · rw [T.subperipheralModulus_eq_zero_of_empty (Set.not_nonempty_iff_eq_empty.mp hT)]

/-- If there is a subperipheral eigenvalue, Wolf's `μ` remains strictly
inside the unit disc. -/
theorem subperipheralModulus_lt_one (T : Module.End ℂ V)
    (hT : T.subperipheralSpectrum.Nonempty) : T.subperipheralModulus < 1 := by
  rw [subperipheralModulus,
    (T.subperipheralSpectrum_finite.image _).csSup_lt_iff (hT.image _)]
  intro r hr
  rcases hr with ⟨z, hz, rfl⟩
  exact hz.2

/-- Exact qualification of the `μ = 0` case: the subperipheral spectrum is
empty or contains only the zero eigenvalue. -/
theorem subperipheralModulus_eq_zero_iff (T : Module.End ℂ V) :
    T.subperipheralModulus = 0 ↔ ∀ z ∈ T.subperipheralSpectrum, z = 0 := by
  constructor
  · intro hμ z hz
    have hle := T.norm_le_subperipheralModulus hz
    rw [hμ] at hle
    exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg z))
  · intro hzero
    by_cases hT : T.subperipheralSpectrum.Nonempty
    · obtain ⟨z, hz, hnorm⟩ := T.exists_norm_eq_subperipheralModulus hT
      rw [← hnorm, hzero z hz, norm_zero]
    · exact T.subperipheralModulus_eq_zero_of_empty
        (Set.not_nonempty_iff_eq_empty.mp hT)

end Module.End
