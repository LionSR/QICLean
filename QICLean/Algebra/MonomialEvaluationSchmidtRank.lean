/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.FiniteMonomialInterpolation
import QICLean.Algebra.OperatorSchmidtBounds

/-!
# Operator Schmidt rank of selected monomial coefficients

Suppose every evaluation of a finite operator-valued monomial sum has
operator Schmidt rank at most `r`. Every selected sum of its coefficients
then has rank at most the number of prescribed monomials times `r`.

The scalar recovery points and coefficients depend only on the monomial
support. Summing the recovery formulas combines the selected coefficients
at those same points before applying the finite-sum rank bound.
The operator coefficients may vanish or coincide.

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 626–644.
The Hamiltonian generating-polynomial identification and the locality bound
for its evaluated operators are separate statements.
-/

open scoped BigOperators

namespace Matrix

open Classical in
/-- A selected sum of coefficient operators inherits a finite interpolation rank bound.
Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 626–644.
The evaluated family need only span; the coefficient operators may be dependent.
This does not identify Hamiltonian coefficients or prove a locality estimate. -/
theorem operatorSchmidtRank_sum_le_of_monomial_evaluations
    {σ l n : Type*} [Fintype l] [Finite n]
    (S : Finset (σ →₀ ℕ)) :
    ∀ (f : (σ →₀ ℕ) → Matrix (l × n) (l × n) ℂ)
      (U : Finset (σ →₀ ℕ)), U ⊆ S → ∀ r : ℕ,
      (∀ z : σ → ℂ, operatorSchmidtRank
        (∑ α ∈ S, MvPolynomial.eval z
          (MvPolynomial.monomial α (1 : ℂ)) • f α) ≤ r) →
      operatorSchmidtRank (∑ α ∈ U, f α) ≤ S.card * r := by
  obtain ⟨z, c, hrec⟩ := MvPolynomial.exists_monomial_evaluation_recovery S
  intro f U hU r heval
  have hsum :
      (∑ α : U, ∑ i : Fin S.card, c ⟨α.val, hU α.property⟩ i •
        (∑ β : S, MvPolynomial.eval (z i)
          (MvPolynomial.monomial β.val (1 : ℂ)) • f β.val)) =
        ∑ α : U, f α.val :=
    Finset.sum_congr rfl fun α _ ↦
      MvPolynomial.monomial_evaluation_recovery_smul S z c hrec
        (fun β : S ↦ f β.val) ⟨α.val, hU α.property⟩
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.sum_smul] at hsum
  rw [← Finset.sum_coe_sort U f, ← hsum]
  refine (operatorSchmidtRank_sum_le Finset.univ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin S.card, r := Finset.sum_le_sum fun i _ ↦
      (operatorSchmidtRank_smul_le _ _).trans
        (by simpa only [← Finset.sum_coe_sort S (fun α ↦
          MvPolynomial.eval (z i) (MvPolynomial.monomial α (1 : ℂ)) • f α)]
          using heval (z i))
    _ = _ := by simp

end Matrix
