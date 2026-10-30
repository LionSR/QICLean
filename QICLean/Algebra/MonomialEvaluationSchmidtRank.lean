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

/-- A scalar-weighted sum of an injectively indexed finite monomial family has rank
at most its cardinality times the common evaluation-rank bound. Zero and dependent
operator coefficients are allowed. AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`),
lines 626--644. -/
theorem operatorSchmidtRank_sum_smul_le_of_injective_monomial_evaluations
    {σ τ l n : Type*} [Fintype l] [Finite n]
    (T : Finset τ) (ρ : τ → (σ →₀ ℕ)) (hρ : Set.InjOn ρ T)
    (f : τ → Matrix (l × n) (l × n) ℂ) (weight : τ → ℂ) (r : ℕ)
    (heval : ∀ z : σ → ℂ, operatorSchmidtRank
      (∑ α ∈ T, MvPolynomial.eval z
        (MvPolynomial.monomial (ρ α) (1 : ℂ)) • f α) ≤ r) :
    operatorSchmidtRank (∑ α ∈ T, weight α • f α) ≤ T.card * r := by
  classical
  let S := T.image ρ
  let lift : T → S := fun α ↦ ⟨ρ α.val, Finset.mem_image_of_mem ρ α.property⟩
  have hlift : Function.Bijective lift := by
    constructor
    · intro α β h
      exact Subtype.ext (hρ α.property β.property (congrArg Subtype.val h))
    · intro β
      obtain ⟨α, hα, hρα⟩ := Finset.mem_image.mp β.property
      exact ⟨⟨α, hα⟩, Subtype.ext hρα⟩
  let e : T ≃ S := Equiv.ofBijective lift hlift
  let g : S → Matrix (l × n) (l × n) ℂ := fun β ↦ f (e.symm β).val
  let w : S → ℂ := fun β ↦ weight (e.symm β).val
  let E (z : σ → ℂ) :=
    ∑ β : S, MvPolynomial.eval z (MvPolynomial.monomial β.val (1 : ℂ)) • g β
  have hE (z : σ → ℂ) : operatorSchmidtRank (E z) ≤ r := by
    have hsum :
        (∑ α : T, MvPolynomial.eval z
          (MvPolynomial.monomial (ρ α.val) (1 : ℂ)) • f α.val) = E z := by
      refine Fintype.sum_equiv e _ _ ?_
      intro α
      change MvPolynomial.eval z
          (MvPolynomial.monomial (ρ α.val) (1 : ℂ)) • f α.val =
        MvPolynomial.eval z (MvPolynomial.monomial (e α).val (1 : ℂ)) •
          f (e.symm (e α)).val
      rw [e.symm_apply_apply]
      rfl
    have hz : operatorSchmidtRank
        (∑ α : T, MvPolynomial.eval z
          (MvPolynomial.monomial (ρ α.val) (1 : ℂ)) • f α.val) ≤ r := by
      simpa only [← Finset.sum_coe_sort T (fun α ↦
        MvPolynomial.eval z (MvPolynomial.monomial (ρ α) (1 : ℂ)) • f α)]
        using heval z
    exact hsum ▸ hz
  obtain ⟨z, c, hrec⟩ := MvPolynomial.exists_monomial_evaluation_recovery S
  have hrecover (β : S) :
      (∑ t : Fin S.card, c β t • E (z t)) = g β :=
    MvPolynomial.monomial_evaluation_recovery_smul S z c hrec g β
  have hweighted : (∑ α ∈ T, weight α • f α) = ∑ β : S, w β • g β := by
    rw [← Finset.sum_coe_sort T (fun α ↦ weight α • f α)]
    refine Fintype.sum_equiv e _ _ ?_
    intro α
    simp only [w, g, e.symm_apply_apply]
  have hcontract :
      (∑ t : Fin S.card, (∑ β : S, w β * c β t) • E (z t)) =
        ∑ β : S, w β • g β := by
    simp_rw [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, hrecover]
  have hcard : S.card = T.card := Finset.card_image_of_injOn hρ
  rw [hweighted, ← hcontract]
  refine (operatorSchmidtRank_sum_le Finset.univ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin S.card, r := Finset.sum_le_sum fun t _ ↦
      (operatorSchmidtRank_smul_le _ _).trans (hE (z t))
    _ = T.card * r := by simp [hcard]


end Matrix
