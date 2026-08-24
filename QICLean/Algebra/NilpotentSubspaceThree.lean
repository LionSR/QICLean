/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.NilpotentSubspaceTwo
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Square-zero subspaces of 3×3 complex matrices

This file proves the square-zero branch of the three-dimensional nilpotent-subspace
classification: if every matrix in a complex linear subspace of `3 × 3` matrices
squares to zero, then the matrices have a common nonzero kernel vector.

The complete classification invoked without proof by Wolf's low-dimensional quantum
Wielandt corollary is not established here.  In particular, the branch containing a
matrix of nilpotency index three and the exceptional two-dimensional family remain to
be formalized.  That missing argument is external to Wolf, *Quantum Channels &
Operations*, Chapter 6, `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`
lines 1115–1126.

## Main result

* `exists_common_ker_of_forall_sq_eq_zero`: a square-zero subspace of `M₃(ℂ)`
  has a common nonzero kernel vector.

## Proof outline

A nonzero member `A` has rank at most one, so it has the form
`x ↦ ℓ(x) • u`.  Polarizing `(A + M)² = 0` shows that every other member `M`
preserves the line spanned by `u`.  Nilpotence forces the corresponding scalar
to vanish, giving the common kernel vector `u`.
-/
open scoped Matrix

namespace QICLean

variable {S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ)}

/-- A square-zero `3 × 3` complex matrix has rank at most one. -/
theorem Matrix.rank_le_one_of_sq_eq_zero {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : M ^ 2 = 0) : Matrix.rank M ≤ 1 := by
  have hsub : LinearMap.range (Matrix.toLin' M) ≤ LinearMap.ker (Matrix.toLin' M) := by
    rintro y ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.toLin'_apply]
    rw [Matrix.mulVec_mulVec, ← pow_two, hM, Matrix.zero_mulVec]
  have hrk := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have hle := Submodule.finrank_mono hsub
  have h3 : Module.finrank ℂ (Fin 3 → ℂ) = 3 := by
    simp [Module.finrank_fintype_fun_eq_card]
  rw [h3] at hrk
  have hrank : Matrix.rank M = Module.finrank ℂ (LinearMap.range (Matrix.toLin' M)) :=
    rfl
  omega

/-- A nonzero matrix of rank at most one has a one-dimensional range. -/
theorem exists_range_eq_span_singleton_of_rank_le_one {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : M ≠ 0) (hrank : Matrix.rank M ≤ 1) :
    ∃ u : Fin 3 → ℂ, u ≠ 0 ∧ LinearMap.range (Matrix.toLin' M) = ℂ ∙ u := by
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hM (Matrix.ext fun i j => h i j)
  have hu0 : M *ᵥ Pi.single j 1 ≠ 0 := by
    intro hzero
    have h_entry := congr_fun hzero i
    rw [Matrix.mulVec_single] at h_entry
    simp only [MulOpposite.op_one, one_smul] at h_entry
    rw [Matrix.col_apply] at h_entry
    exact hij h_entry
  refine ⟨M *ᵥ (Pi.single j 1), hu0, ?_⟩
  · have hmem : M *ᵥ (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' M) :=
      ⟨Pi.single j 1, by simp [Matrix.toLin'_apply]⟩
    have hle : ℂ ∙ (M *ᵥ Pi.single j 1) ≤ LinearMap.range (Matrix.toLin' M) :=
      (Submodule.span_singleton_le_iff_mem _ _).2 hmem
    have hfin1 : Module.finrank ℂ (ℂ ∙ (M *ᵥ Pi.single j 1) : Submodule ℂ _) = 1 :=
      finrank_span_singleton hu0
    have hfinr : Module.finrank ℂ (LinearMap.range (Matrix.toLin' M)) = 1 := by
      have hpos : 0 < Module.finrank ℂ (LinearMap.range (Matrix.toLin' M)) := by
        have hn : Nontrivial (LinearMap.range (Matrix.toLin' M)) :=
          ⟨⟨M *ᵥ Pi.single j 1, hmem⟩, ⟨0, Submodule.zero_mem _⟩,
            fun hcon => hu0 (Subtype.ext_iff.mp hcon)⟩
        exact Module.finrank_pos_iff.mpr hn
      have hle1 : Module.finrank ℂ (LinearMap.range (Matrix.toLin' M)) ≤ 1 := by
        have := hrank
        rwa [Matrix.rank] at this
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin1, hfinr])).symm

/-- A nilpotent matrix has no nonzero eigenvalues: if `M *ᵥ u = μ • u` with
`u ≠ 0` and `M` nilpotent, then `μ = 0`. -/
theorem IsNilpotent.eq_zero_of_mulVec_eq_smul {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hM : IsNilpotent M) {u : Fin 3 → ℂ} (hu : u ≠ 0) {μ : ℂ}
    (h : M *ᵥ u = μ • u) : μ = 0 := by
  obtain ⟨k, hk⟩ := hM
  have hiter : ∀ j : ℕ, (M ^ j) *ᵥ u = (μ ^ j) • u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, ← pow_succ]
  have h0 := hiter k
  rw [hk, Matrix.zero_mulVec] at h0
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact one_ne_zero hk
  have hμk : μ ^ k = 0 := (smul_eq_zero.mp h0.symm).resolve_right hu
  exact (pow_eq_zero_iff hk0).mp hμk

/-- **Square-zero case**: a submodule of `3 × 3` complex matrices in which
every element squares to zero has a common kernel vector. -/
theorem exists_common_ker_of_forall_sq_eq_zero
    (S : Submodule ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    (hS : ∀ M ∈ S, M ^ 2 = 0) :
    ∃ u : Fin 3 → ℂ, u ≠ 0 ∧ ∀ M ∈ S, M *ᵥ u = 0 := by
  rcases eq_or_ne S ⊥ with rfl | hbot
  · refine ⟨![1, 0, 0], ?_, fun M hM => ?_⟩
    · intro h
      have := congr_fun h 0
      simp at this
    · rw [Submodule.mem_bot] at hM
      subst hM
      simp
  obtain ⟨A, hAS, hA0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨u, hu, hrange⟩ :=
    exists_range_eq_span_singleton_of_rank_le_one hA0
      (Matrix.rank_le_one_of_sq_eq_zero (hS A hAS))
  -- Decompose `A` as `x ↦ ℓ x • u`.
  have hc : ∀ j : Fin 3, ∃ c : ℂ, A *ᵥ (Pi.single j 1) = c • u := by
    intro j
    have hmem : A *ᵥ (Pi.single j 1) ∈ LinearMap.range (Matrix.toLin' A) :=
      ⟨Pi.single j 1, by simp [Matrix.toLin'_apply]⟩
    rw [hrange] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  choose c hc using hc
  let ℓ : (Fin 3 → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => ∑ j : Fin 3, c j * x j
      map_add' := by
        intro x y
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring }
  have hentry : ∀ i j : Fin 3, A i j = c j * u i := by
    intro i j
    have h := congr_fun (hc j) i
    rw [Matrix.mulVec_single] at h
    simpa [Matrix.col_apply] using h
  have hA_eq : ∀ x : Fin 3 → ℂ, A *ᵥ x = ℓ x • u := by
    intro x
    ext i
    simp only [Matrix.mulVec, dotProduct, ℓ, Pi.smul_apply, smul_eq_mul]
    simp_rw [hentry]
    change (∑ j : Fin 3, c j * u i * x j) = (∑ j : Fin 3, c j * x j) * u i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- `ℓ` is nontrivial since `A ≠ 0`.
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Fin 3 → ℂ, ℓ x₀ = 1 := by
    by_contra h
    push Not at h
    have hℓ0 : ∀ x, ℓ x = 0 := by
      intro x
      by_contra hx
      exact h ((ℓ x)⁻¹ • x) (by simp [map_smul, hx])
    refine hA0 ?_
    ext i j
    have h1 : A *ᵥ (Pi.single j 1) = ℓ (Pi.single j 1) • u := hA_eq _
    rw [hℓ0, zero_smul] at h1
    have := congr_fun h1 i
    rw [Matrix.mulVec_single] at this
    simpa [Matrix.col_apply] using this
  -- For every `M ∈ S`, `M *ᵥ u ∈ ℂ ∙ u`.
  have hMu : ∀ M ∈ S, ∃ μ : ℂ, M *ᵥ u = μ • u := by
    intro M hMS
    have hsq : (A + M) ^ 2 = A ^ 2 + A * M + M * A + M ^ 2 := by noncomm_ring
    rw [hS (A + M) (S.add_mem hAS hMS), hS A hAS, hS M hMS] at hsq
    have key : A * M + M * A = 0 := by
      have h' := hsq.symm
      simpa using h'
    have happ : (A * M + M * A) *ᵥ x₀ = 0 := by rw [key, Matrix.zero_mulVec]
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at happ
    rw [hA_eq, hA_eq, hx₀, one_smul] at happ
    -- happ : ℓ (M *ᵥ x₀) • u + M *ᵥ u = 0
    refine ⟨-ℓ (M *ᵥ x₀), ?_⟩
    exact (eq_neg_of_add_eq_zero_right happ).trans (neg_smul _ _).symm
  -- A nilpotent matrix has no nonzero eigenvalues, so `M *ᵥ u = 0`.
  refine ⟨u, hu, fun M hMS => ?_⟩
  obtain ⟨μ, hμ⟩ := hMu M hMS
  have hnil : IsNilpotent M := ⟨2, hS M hMS⟩
  rw [IsNilpotent.eq_zero_of_mulVec_eq_smul hnil hu hμ, zero_smul] at hμ
  exact hμ

end QICLean
