/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Order.FiniteKroneckerOrder
import Lean.Elab.Command

/-! Regression tests for tensor stability of two-sided PSD domination. -/

open scoped ComplexOrder

namespace FiniteKroneckerDominationTest

def signature : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i ↦ if i = 0 then 1 else -1)

theorem identity_add_signature : ((1 : Matrix (Fin 2) (Fin 2) ℂ) + signature).PosSemidef := by
  rw [← Matrix.diagonal_one, signature, Matrix.diagonal_add]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

theorem identity_sub_signature : ((1 : Matrix (Fin 2) (Fin 2) ℂ) - signature).PosSemidef := by
  rw [← Matrix.diagonal_one, signature, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

/-- Both signs of the dominated matrix fail to be PSD. -/
theorem signature_indefinite : ¬ signature.PosSemidef ∧ ¬ (-signature).PosSemidef := by
  constructor
  · intro h
    have hdiag := h.diag_nonneg (i := 1)
    norm_num [signature, Matrix.diagonal_apply, Complex.nonneg_iff] at hdiag
  · intro h
    have hdiag := h.diag_nonneg (i := 0)
    norm_num [signature, Matrix.diagonal_apply, Complex.nonneg_iff] at hdiag

theorem binary_indefinite :
    (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 +
      Matrix.kronecker signature signature).PosSemidef ∧
    (Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 -
      Matrix.kronecker signature signature).PosSemidef :=
  Matrix.kronecker_add_sub_posSemidef identity_add_signature identity_sub_signature
    identity_add_signature identity_sub_signature

theorem copies_indefinite (N : ℕ) :
    (Matrix.piKronecker (fun _ : Fin N ↦ (1 : Matrix (Fin 2) (Fin 2) ℂ)) +
      Matrix.piKronecker (fun _ : Fin N ↦ signature)).PosSemidef ∧
    (Matrix.piKronecker (fun _ : Fin N ↦ (1 : Matrix (Fin 2) (Fin 2) ℂ)) -
      Matrix.piKronecker (fun _ : Fin N ↦ signature)).PosSemidef :=
  Matrix.piKronecker_const_add_sub_posSemidef N identity_add_signature identity_sub_signature

/-- No local hypotheses are needed for zero factors, even for arbitrary families. -/
theorem zero_factors {I : Fin 0 → Type*} [∀ i, Finite (I i)]
    (A B : (i : Fin 0) → Matrix (I i) (I i) ℂ) :
    (Matrix.piKronecker A + Matrix.piKronecker B).PosSemidef ∧
    (Matrix.piKronecker A - Matrix.piKronecker B).PosSemidef :=
  Matrix.piKronecker_add_sub_posSemidef A B (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)

/-- Heterogeneous factors with an empty local basis. -/
theorem empty_local_space
    (A B : (i : Fin 2) → Matrix (Fin i.val) (Fin i.val) ℂ)
    (hadd : ∀ i, (A i + B i).PosSemidef)
    (hsub : ∀ i, (A i - B i).PosSemidef) :
    (Matrix.piKronecker A + Matrix.piKronecker B).PosSemidef ∧
    (Matrix.piKronecker A - Matrix.piKronecker B).PosSemidef :=
  Matrix.piKronecker_add_sub_posSemidef A B hadd hsub

theorem empty_dimension :
    (Matrix.piKronecker (fun _ : Fin 1 ↦ (0 : Matrix (Fin 0) (Fin 0) ℂ)) +
      Matrix.piKronecker (fun _ : Fin 1 ↦ (0 : Matrix (Fin 0) (Fin 0) ℂ))).PosSemidef ∧
    (Matrix.piKronecker (fun _ : Fin 1 ↦ (0 : Matrix (Fin 0) (Fin 0) ℂ)) -
      Matrix.piKronecker (fun _ : Fin 1 ↦ (0 : Matrix (Fin 0) (Fin 0) ℂ))).PosSemidef := by
  have hz : (0 : Matrix (Fin 0) (Fin 0) ℂ).PosSemidef := Matrix.PosSemidef.zero
  exact Matrix.piKronecker_const_add_sub_posSemidef 1
    (by simpa using hz) (by simpa using hz)

end FiniteKroneckerDominationTest

-- Reject every nonstandard axiom transitively, not just sorryAx.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``Matrix.kronecker_add_sub_posSemidef,
      ``Matrix.piKronecker_add_sub_posSemidef,
      ``Matrix.piKronecker_const_add_sub_posSemidef,
      ``FiniteKroneckerDominationTest.signature_indefinite,
      ``FiniteKroneckerDominationTest.binary_indefinite,
      ``FiniteKroneckerDominationTest.copies_indefinite,
      ``FiniteKroneckerDominationTest.zero_factors,
      ``FiniteKroneckerDominationTest.empty_local_space,
      ``FiniteKroneckerDominationTest.empty_dimension] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axs ← Lean.collectAxioms decl
    unless axs.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axs}"
    Lean.logInfo m!"{decl}: {axs}"
