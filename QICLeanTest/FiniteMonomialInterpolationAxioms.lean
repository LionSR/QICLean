/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.FiniteMonomialInterpolation

/-! # Kernel dependencies of finite monomial interpolation -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'MvPolynomial.exists_monomial_evaluation_recovery'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.exists_monomial_evaluation_recovery

/-- info:
'MvPolynomial.monomial_evaluation_recovery_smul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.monomial_evaluation_recovery_smul

/-- info:
'MvPolynomial.exists_weighted_monomial_evaluation_recovery'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.exists_weighted_monomial_evaluation_recovery

open scoped BigOperators

-- The same scalar witnesses recover the selected coefficient for dependent
-- matrix-valued families; no independence of coefficient operators is needed.
example :
    let S : Finset (Fin 1 →₀ ℕ) := {0, Finsupp.single 0 1}
    ∃ z : Fin S.card → (Fin 1 → ℂ), ∃ gamma : Fin S.card → ℂ,
      ∀ A : Matrix (Fin 2) (Fin 2) ℂ,
        (∑ r : Fin S.card, gamma r •
          (∑ β : S, MvPolynomial.eval (z r)
            (MvPolynomial.monomial (β : Fin 1 →₀ ℕ) (1 : ℂ)) • A)) = A := by
  classical
  intro S
  obtain ⟨z, hz⟩ := MvPolynomial.exists_weighted_monomial_evaluation_recovery
    (M := Matrix (Fin 2) (Fin 2) ℂ) S
  obtain ⟨gamma, hgamma⟩ := hz (fun α ↦ if (α : Fin 1 →₀ ℕ) = 0 then 1 else 0)
  refine ⟨z, gamma, fun A ↦ ?_⟩
  have hsel : (∑ α : S, (if (α : Fin 1 →₀ ℕ) = 0 then (1 : ℂ) else 0) • A) = A := by
    let α0 : S := ⟨0, by simp [S]⟩
    have hiff (α : S) : (α : Fin 1 →₀ ℕ) = 0 ↔ α = α0 := by
      constructor
      · exact fun h ↦ Subtype.ext h
      · exact fun h ↦ congrArg Subtype.val h
    simp only [hiff, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  exact (hgamma (fun _ ↦ A)).symm.trans hsel
