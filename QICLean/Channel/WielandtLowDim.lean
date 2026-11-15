/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.NilpotentSubspaceThree
import QICLean.Algebra.NilpotentSubspaceThreeGrading
import QICLean.Channel.Irreducible.AdjointFamily
import QICLean.Channel.QuantumWielandt
import QICLean.Analysis.MatrixNonzeroTraceEigenvalue
import QICLean.Channel.WolfTheorem68

/-!
# Low-dimensional obstructions for the quantum Wielandt corollary

This file proves Wolf's low-dimensional quantum Wielandt corollary. For `D = 2` the one-step
span of a trace-preserving family contains a matrix with a nonzero eigenvalue. For `D = 3` a
nilpotent one-step span of a trace-preserving family is graded by the exceptional nilpotent
space, which gives the peripheral eigenvalue `-1`; a primitive channel therefore has a
non-nilpotent, hence nonzero-eigenvalue, element in its one-step span. In both dimensions the
Wielandt index is at most `D²`.

Source: Wolf, *Quantum Channels & Operations*, Chapter 6,
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex` lines 1110–1126.
The nilpotent-subspace classifications invoked there are not proved in Wolf's
notes; the dimension-two classification is supplied in
`QICLean.Algebra.NilpotentSubspaceTwo`, and the dimension-three classification
needed here in `QICLean.Algebra.NilpotentSubspaceThree` and
`QICLean.Algebra.NilpotentSubspaceThreeGrading`.
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

/-- **A nilpotent one-step span obstructs primitivity in dimension three.** If every member of
the one-step span of a trace-preserving Kraus family on `M₃(ℂ)` is nilpotent, then the span is
graded, `K P₀ = P₁ K` with `P₀ + P₁ = 1`, and `P₀ - P₁` is an eigenvector of the trace adjoint
with eigenvalue `-1`. Hence the channel is not primitive.

Source: Wolf, Chapter 6, corollary at lines 1110--1126: the exceptional two-dimensional nilpotent
space only leads to channels with a degenerate peripheral spectrum. The classification is
`QICLean.exists_grading_of_isNilpotent_submodule_fin_three`. -/
theorem not_isPrimitive_of_isTP_of_forall_isNilpotent_fin_three
    (K : Fin d → Matrix (Fin 3) (Fin 3) ℂ) (hTP : IsTP K)
    (hnil : ∀ M ∈ wordSpan K 1, IsNilpotent M) : ¬ IsPrimitive (mapLM K) := by
  intro hPrim
  have hmemK : ∀ i, K i ∈ wordSpan K 1 := fun i ↦ by
    rw [wordSpan_one]
    exact Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨P₀, P₁, hsum, hne, hgrade⟩ :=
    QICLean.exists_grading_of_isNilpotent_submodule_fin_three (wordSpan K 1) hnil
      (fun v hv ↦ eq_zero_of_isTP_of_forall_mulVec_eq_zero K hTP fun i ↦ hv (K i) (hmemK i))
  have hP₁ : P₁ = 1 - P₀ := by rw [← hsum]; abel
  have hgrade' : ∀ i, K i * P₁ = P₀ * K i := by
    intro i
    have h := hgrade (K i) (hmemK i)
    rw [hP₁, Matrix.mul_sub, Matrix.mul_one, h, hP₁, Matrix.sub_mul, Matrix.one_mul]
    abel
  have heig : Matrix.traceAdjointMap (mapLM K) (P₀ - P₁) = (-1 : ℂ) • (P₀ - P₁) := by
    rw [traceAdjointMap_mapLM_eq_mapLM_conjTranspose, mapLM_apply, map_apply]
    have hterm : ∀ i, (K i)ᴴ * (P₀ - P₁) * ((K i)ᴴ)ᴴ = (K i)ᴴ * K i * (P₁ - P₀) := by
      intro i
      rw [Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, ← hgrade' i, ← hgrade (K i) (hmemK i), Matrix.mul_sub,
        ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp_rw [hterm, ← Finset.sum_mul]
    rw [show (∑ i, (K i)ᴴ * K i) = 1 from hTP, Matrix.one_mul, neg_one_smul, neg_sub]
  have hEig : Module.End.HasEigenvalue (Matrix.traceAdjointMap (mapLM K)) (-1) :=
    hasEigenvalue_of_eigenvector_eq _ (-1) _ heig hne
  have := hPrim.unique_peripheral (-1)
    ((Matrix.traceAdjointMap_hasEigenvalue_iff (mapLM K) (-1)).mp hEig) (by simp)
  norm_num at this

/-- **Wolf's low-dimensional Kraus-span conclusion in dimension three.** For a primitive
trace-preserving Kraus family on `M₃(ℂ)`, its one-step span contains a matrix that is not
nilpotent. Source: Wolf, Chapter 6, corollary at lines 1110--1126. -/
theorem exists_not_isNilpotent_mem_wordSpan_one_fin_three
    (K : Fin d → Matrix (Fin 3) (Fin 3) ℂ) (hTP : IsTP K) (hPrim : IsPrimitive (mapLM K)) :
    ∃ M ∈ wordSpan K 1, ¬ IsNilpotent M := by
  by_contra h
  push Not at h
  exact not_isPrimitive_of_isTP_of_forall_isNilpotent_fin_three K hTP h hPrim

/-- A complex matrix that is not nilpotent has a nonzero eigenvalue with a nonzero eigenvector:
otherwise every root of its split characteristic polynomial vanishes, the characteristic
polynomial is `X^D`, and the matrix is nilpotent by the Cayley--Hamilton theorem. -/
theorem exists_nonzero_eigenvector_of_not_isNilpotent {D : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) (hM : ¬ IsNilpotent M) :
    ∃ (μ : ℂ) (φ : Fin D → ℂ), μ ≠ 0 ∧ φ ≠ 0 ∧ M *ᵥ φ = μ • φ := by
  by_contra h
  push Not at h
  apply hM
  let f := Matrix.toLin' M
  have hroots : ∀ μ ∈ f.charpoly.roots, μ = 0 := by
    intro μ hμ
    have hev : Module.End.HasEigenvalue f μ :=
      Module.End.hasEigenvalue_iff_isRoot_charpoly f μ |>.mpr
        (Polynomial.isRoot_of_mem_roots hμ)
    obtain ⟨φ, hφ⟩ := hev.exists_hasEigenvector
    by_contra hμ0
    exact h μ φ hμ0 hφ.2 (by simpa [f, Matrix.toLin'_apply'] using hφ.apply_eq_smul)
  have hsplit := IsAlgClosed.splits f.charpoly
  have hchar : f.charpoly = Polynomial.X ^ Module.finrank ℂ (Fin D → ℂ) := by
    rw [hsplit.eq_prod_roots_of_monic (LinearMap.charpoly_monic f),
      Multiset.eq_replicate_of_mem hroots]
    simp only [Multiset.map_replicate, map_zero, sub_zero, Multiset.prod_replicate]
    congr 1
    rw [← hsplit.natDegree_eq_card_roots, LinearMap.charpoly_natDegree]
  have hf : IsNilpotent f := (LinearMap.isNilpotent_iff_charpoly f).mpr hchar
  have h' := hf.map (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin D)).symm.toRingHom
  have heq : (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin D)).symm.toRingHom f = M :=
    (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin D)).symm_apply_apply M
  rwa [heq] at h'

/-- **Wolf's low-dimensional quantum Wielandt corollary in dimension three.** For an irreducible
primitive trace-preserving Kraus family on `M₃(ℂ)`, the one-step span contains a matrix with a
nonzero eigenvalue, and the Wielandt index is at most `3² = 9`. Source: Wolf, Chapter 6,
corollary at lines 1110--1126. -/
theorem wielandtIndex_le_nine_fin_three
    (K : Fin d → Matrix (Fin 3) (Fin 3) ℂ) (hTP : IsTP K) (hIrr : IsIrreducibleMap (mapLM K))
    (hPrim : IsPrimitive (mapLM K)) : wielandtIndex K ≤ 3 ^ 2 := by
  obtain ⟨M, hM, hMnil⟩ := exists_not_isNilpotent_mem_wordSpan_one_fin_three K hTP hPrim
  obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_nonzero_eigenvector_of_not_isNilpotent M hMnil
  exact wielandtIndex_le_of_mem_wordSpan_one_of_nonzero_eigenvalue K hTP hIrr hPrim hM hμ hφ heig

/-- **Wolf's low-dimensional quantum Wielandt corollary in dimension two.** For an irreducible
primitive trace-preserving Kraus family on `M₂(ℂ)`, the Wielandt index is at most `2² = 4`.
Source: Wolf, Chapter 6, corollary at lines 1110--1126. -/
theorem wielandtIndex_le_four_fin_two
    (K : Fin d → Matrix (Fin 2) (Fin 2) ℂ) (hTP : IsTP K) (hIrr : IsIrreducibleMap (mapLM K))
    (hPrim : IsPrimitive (mapLM K)) : wielandtIndex K ≤ 2 ^ 2 := by
  obtain ⟨M, μ, φ, hM, hμ, hφ, heig⟩ := exists_nonzero_eigenvector_mem_wordSpan_one_fin_two K hTP
  exact wielandtIndex_le_of_mem_wordSpan_one_of_nonzero_eigenvalue K hTP hIrr hPrim hM hμ hφ heig

end Kraus
