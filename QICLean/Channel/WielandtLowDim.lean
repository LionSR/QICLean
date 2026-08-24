/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.NilpotentSubspaceThree
import QICLean.Analysis.MatrixNonzeroTraceEigenvalue
import QICLean.Channel.WolfTheorem68

/-!
# Low-dimensional obstructions for the quantum Wielandt corollary

This file develops the trace-preserving obstruction used in Wolf's
low-dimensional quantum Wielandt corollary.  It proves the complete `D = 2`
one-step conclusion and the common-kernel obstruction needed in dimension three.

Source: Wolf, *Quantum Channels & Operations*, Chapter 6,
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex` lines 1110–1126.
The nilpotent-subspace classifications invoked there are not proved in Wolf's
notes; the dimension-two classification is supplied in
`QICLean.Algebra.NilpotentSubspaceTwo`.
-/

open scoped Matrix BigOperators

namespace Kraus

variable {d D : ℕ}

/-- A trace-preserving Kraus family cannot have a nonzero common kernel vector. -/
theorem eq_zero_of_isTP_of_forall_mulVec_eq_zero
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (hTP : IsTP K)
    {v : Fin D → ℂ} (hv : ∀ i, K i *ᵥ v = 0) : v = 0 := by
  have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M *ᵥ v) hTP
  simp_rw [Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero] at h
  simpa using h.symm

/-- For a `2 × 2` matrix, vanishing trace and determinant imply square-zero. -/
theorem isNilpotent_fin_two_of_trace_eq_zero_of_det_eq_zero
    {M : Matrix (Fin 2) (Fin 2) ℂ} (htr : M.trace = 0) (hdet : M.det = 0) :
    IsNilpotent M := by
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have h11 : M 1 1 = -M 0 0 := by linear_combination htr
  have hdiag : M 0 0 ^ 2 + M 0 1 * M 1 0 = 0 := by
    rw [h11] at hdet
    linear_combination -hdet
  refine ⟨2, ?_⟩
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, h11]
  · simpa [pow_two] using hdiag
  · ring
  · ring
  · simpa [pow_two, add_comm, mul_comm] using hdiag

/-- A nonnilpotent `2 × 2` complex matrix has a nonzero eigenvalue and a
corresponding nonzero eigenvector. -/
theorem exists_nonzero_eigenvector_fin_two_of_not_isNilpotent
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : ¬ IsNilpotent M) :
    ∃ (μ : ℂ) (φ : Fin 2 → ℂ), μ ≠ 0 ∧ φ ≠ 0 ∧ M *ᵥ φ = μ • φ := by
  by_cases htr : M.trace = 0
  · have hdet : M.det ≠ 0 := by
      intro hdet
      exact hM (isNilpotent_fin_two_of_trace_eq_zero_of_det_eq_zero htr hdet)
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' M)
    obtain ⟨φ, hφ⟩ := hμ.exists_hasEigenvector
    have heig : M *ᵥ φ = μ • φ := by
      simpa [Matrix.toLin'_apply'] using hφ.apply_eq_smul
    have hμ0 : μ ≠ 0 := by
      intro hzero
      subst μ
      have hker : M *ᵥ φ = 0 := by simpa using heig
      exact hdet (Matrix.exists_mulVec_eq_zero_iff.mp ⟨φ, hφ.2, hker⟩)
    exact ⟨μ, φ, hμ0, hφ.2, heig⟩
  · exact exists_eigenvector_of_trace_ne_zero M htr

/-- **Wolf's low-dimensional Kraus-span conclusion in dimension two.**

For a trace-preserving finite Kraus family on `M₂(ℂ)`, its one-step span
contains a matrix with a nonzero eigenvalue.  The primitivity hypothesis in
Wolf's corollary is therefore not needed for this first conclusion when
`D = 2`.

Source: Wolf, Chapter 6, corollary at lines 1110–1126.  Wolf leaves the
nilpotent-subspace classification implicit; the proof here uses
`QICLean.exists_common_ker_of_isNilpotent_submodule_fin_two`. -/
theorem exists_nonzero_eigenvector_mem_wordSpan_one_fin_two
    (K : Fin d → Matrix (Fin 2) (Fin 2) ℂ) (hTP : IsTP K) :
    ∃ (M : Matrix (Fin 2) (Fin 2) ℂ) (μ : ℂ) (φ : Fin 2 → ℂ),
      M ∈ wordSpan K 1 ∧ μ ≠ 0 ∧ φ ≠ 0 ∧ M *ᵥ φ = μ • φ := by
  by_contra h
  push Not at h
  have hnil : ∀ M ∈ wordSpan K 1, IsNilpotent M := by
    intro M hM
    by_contra hMnil
    obtain ⟨μ, φ, hμ, hφ, heig⟩ :=
      exists_nonzero_eigenvector_fin_two_of_not_isNilpotent M hMnil
    exact h M μ φ hM hμ hφ heig
  obtain ⟨v, hv, hcommon⟩ :=
    QICLean.exists_common_ker_of_isNilpotent_submodule_fin_two (wordSpan K 1) hnil
  apply hv
  apply eq_zero_of_isTP_of_forall_mulVec_eq_zero K hTP
  intro i
  apply hcommon (K i)
  rw [wordSpan_one]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- A trace-preserving Kraus family on `M₃(ℂ)` cannot have a square-zero
one-step span.  This eliminates the square-zero branch of the
three-dimensional nilpotent-subspace classification. -/
theorem exists_mem_wordSpan_one_sq_ne_zero_fin_three
    (K : Fin d → Matrix (Fin 3) (Fin 3) ℂ) (hTP : IsTP K) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℂ, M ∈ wordSpan K 1 ∧ M ^ 2 ≠ 0 := by
  by_contra h
  push Not at h
  have hsq : ∀ M ∈ wordSpan K 1, M ^ 2 = 0 := by
    intro M hM
    exact h M hM
  obtain ⟨v, hv, hcommon⟩ :=
    QICLean.exists_common_ker_of_forall_sq_eq_zero (wordSpan K 1) hsq
  apply hv
  apply eq_zero_of_isTP_of_forall_mulVec_eq_zero K hTP
  intro i
  apply hcommon (K i)
  rw [wordSpan_one]
  exact Submodule.subset_span ⟨i, rfl⟩


end Kraus
