/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.JordanBlockDirectSum
import QICLean.Analysis.JordanSimilarity

/-!
# The Jordan condition number

Wolf's infimum is over similarities to sums of normalized Jordan blocks, not
arbitrary triangular matrices or a single chosen diagonalization. The blocks
have positive dimensions and superdiagonal one.
A coordinate equivalence permits arbitrary block ordering.

The infimum comparison and approximation theorems require no minimizing basis.
Nonemptiness is explicit where needed: this file does not construct Jordan
normal form for an arbitrary complex matrix.

Source: Wolf (2012), Chapter 8, lines 1221--1224 and Eq. (8.108),
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite sum of positive-dimensional normalized Jordan blocks, up to
a permutation of coordinates. Source: Wolf,
Chapter 8, lines 1221--1224. -/
def IsJordanMatrix (J : Matrix ι ι ℂ) : Prop :=
  ∃ (K : ℕ) (D : Fin K → ℕ) (a : Fin K → ℂ)
    (e : ι ≃ Σ i, Fin (D i)), (∀ i, 0 < D i) ∧
    J = (jordanBlockDirectSum D a).submatrix e e

/-- Every supplied finite sum of positive-dimensional Jordan blocks is an
admissible normalized form. -/
theorem isJordanMatrix_jordanBlockDirectSum (K : ℕ) (D : Fin K → ℕ)
    (a : Fin K → ℂ) (hD : ∀ i, 0 < D i) : IsJordanMatrix (jordanBlockDirectSum D a) :=
  ⟨K, D, a, Equiv.refl _, hD, rfl⟩

omit [Fintype ι] in
/-- Diagonal matrices are sums of one-dimensional Jordan blocks. -/
theorem isJordanMatrix_diagonal [Finite ι] (a : ι → ℂ) : IsJordanMatrix (diagonal a) := by
  let := Fintype.ofFinite ι
  let f := Fintype.equivFin ι
  let e : ι ≃ Σ _i : Fin (Fintype.card ι), Fin 1 :=
    { toFun := fun i ↦ ⟨f i, 0⟩
      invFun := fun i ↦ f.symm i.1
      left_inv := fun i ↦ f.symm_apply_apply i
      right_inv := fun ⟨i, j⟩ ↦ by
        simp only [Equiv.apply_symm_apply, Fin.isValue, Sigma.mk.injEq, heq_eq_eq, true_and]
        exact Subsingleton.elim _ _ }
  refine ⟨Fintype.card ι, fun _ ↦ 1, a ∘ f.symm, e, fun _ ↦ zero_lt_one, ?_⟩
  ext i j
  by_cases h : i = j
  · subst j
    simp [e, jordanBlockDirectSum, blockDiagonal', jordanBlock, nilpotentShift]
  · have hf : f i ≠ f j := fun hij ↦ h (f.injective hij)
    simp [e, jordanBlockDirectSum, blockDiagonal', h, hf]

/-- The factors of all admissible Jordan changes of basis, using an explicit
inverse. This is exactly the family in Wolf's definition at lines 1221--1224. -/
def jordanConditionFactors (X : Matrix ι ι ℂ) : Set ℝ :=
  {c | ∃ P Q J : Matrix ι ι ℂ, P * Q = 1 ∧ Q * P = 1 ∧
    IsJordanMatrix J ∧ X = P * J * Q ∧ c = ‖P‖ * ‖Q‖}

/-- Wolf's Jordan condition number. Statements using its lower bound require
an admissible Jordan similarity; no existence theorem is hidden in this definition. -/
noncomputable def jordanConditionNumber (X : Matrix ι ι ℂ) : ℝ :=
  sInf (jordanConditionFactors X)

/-- The family of condition factors is bounded below, including when empty. -/
theorem bddBelow_jordanConditionFactors (X : Matrix ι ι ℂ) :
    BddBelow (jordanConditionFactors X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨P, Q, J, hPQ, hQP, hJ, hX, rfl⟩
  positivity

/-- Every admissible Jordan basis gives an upper bound on the infimum.
This is the comparison needed by Wolf's detailed-balance proposition. -/
theorem jordanConditionNumber_le (X P Q J : Matrix ι ι ℂ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hJ : IsJordanMatrix J) (hX : X = P * J * Q) :
    jordanConditionNumber X ≤ ‖P‖ * ‖Q‖ :=
  csInf_le (bddBelow_jordanConditionFactors X) ⟨P, Q, J, hPQ, hQP, hJ, hX, rfl⟩

/-- On a nonzero space every admissible condition factor is at least one. -/
theorem one_le_jordanConditionNumber [Nonempty ι] (X : Matrix ι ι ℂ)
    (hX : (jordanConditionFactors X).Nonempty) : 1 ≤ jordanConditionNumber X := by
  apply le_csInf hX
  rintro c ⟨P, Q, J, hPQ, hQP, hJ, hX, rfl⟩
  exact one_le_l2_opNorm_mul_of_mul_eq_one P Q hPQ

/-- The empty matrix has condition number zero under the real-infimum
convention. The lower bound one is therefore restricted to nonzero spaces. -/
theorem jordanConditionNumber_of_isEmpty [IsEmpty ι] (X : Matrix ι ι ℂ) :
    jordanConditionNumber X = 0 := by
  have hs : jordanConditionFactors X = {0} := by
    ext c
    constructor
    · rintro ⟨P, Q, J, hPQ, hQP, hJ, hX, rfl⟩
      have hP : P = 0 := Subsingleton.elim _ _
      simp [hP]
    · rintro rfl
      refine ⟨1, 1, diagonal (fun _ ↦ 0), by simp, by simp,
        isJordanMatrix_diagonal _, Subsingleton.elim _ _, ?_⟩
      have h1 : (1 : Matrix ι ι ℂ) = 0 := Subsingleton.elim _ _
      simp [h1]
  simp [jordanConditionNumber, hs]

/-- Arbitrarily near-minimal Jordan bases exist whenever the admissible family
is nonempty. This does not assert that the infimum is attained. -/
theorem exists_jordanConditionFactor_lt (X : Matrix ι ι ℂ)
    (hX : (jordanConditionFactors X).Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ c ∈ jordanConditionFactors X, c < jordanConditionNumber X + ε := by
  exact exists_lt_of_csInf_lt hX (lt_add_of_pos_right _ hε)

/-- Passing uniform two-sided bounds to Wolf's infimum. The common Jordan
norm must be justified separately; no minimizing Jordan basis is assumed.
Source: the infimum passage in Wolf Eq. (8.108), lines 1247--1254. -/
theorem jordanConditionNumber_bounds [Nonempty ι] (X : Matrix ι ι ℂ)
    (hX : (jordanConditionFactors X).Nonempty) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : ∀ c ∈ jordanConditionFactors X, r ≤ c * s ∧ s ≤ c * r) :
    (jordanConditionNumber X)⁻¹ * r ≤ s ∧ s ≤ jordanConditionNumber X * r := by
  have hk : 0 < jordanConditionNumber X := lt_of_lt_of_le zero_lt_one
    (one_le_jordanConditionNumber X hX)
  constructor
  · apply (inv_mul_le_iff₀ hk).2
    by_cases hs0 : s = 0
    · obtain ⟨c, hc⟩ := hX
      simpa [hs0] using (h c hc).1
    · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      exact (div_le_iff₀ hspos).mp (le_csInf hX (fun c hc ↦
        (div_le_iff₀ hspos).mpr (h c hc).1))
  · by_cases hr0 : r = 0
    · obtain ⟨c, hc⟩ := hX
      simpa [hr0] using (h c hc).2
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      exact (div_le_iff₀ hrpos).mp (le_csInf hX (fun c hc ↦
        (div_le_iff₀ hrpos).mpr (h c hc).2))

/-- The power comparison with the actual infimum, provided every admissible
normalized Jordan representative has the same power norm. Establishing this
invariance from uniqueness of Jordan form is a separate algebraic obligation.
Source: Wolf Eq. (8.108), lines 1247--1254. -/
theorem l2_opNorm_pow_jordanConditionNumber_bounds [Nonempty ι]
    (X : Matrix ι ι ℂ) (hX : (jordanConditionFactors X).Nonempty)
    (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hform : ∀ P Q J : Matrix ι ι ℂ, P * Q = 1 → Q * P = 1 →
      IsJordanMatrix J → X = P * J * Q → ‖J ^ n‖ = r) :
    (jordanConditionNumber X)⁻¹ * r ≤ ‖X ^ n‖ ∧
      ‖X ^ n‖ ≤ jordanConditionNumber X * r := by
  apply jordanConditionNumber_bounds X hX hr (norm_nonneg _)
  rintro c ⟨P, Q, J, hPQ, hQP, hJ, hXJ, rfl⟩
  have hc : 0 < ‖P‖ * ‖Q‖ :=
    zero_lt_one.trans_le (one_le_l2_opNorm_mul_of_mul_eq_one P Q hPQ)
  have hb := l2_opNorm_pow_similarity_bounds P Q J X hPQ hQP hXJ n
  rw [hform P Q J hPQ hQP hJ hXJ] at hb
  exact ⟨(inv_mul_le_iff₀ hc).mp hb.1, hb.2⟩

end Matrix
