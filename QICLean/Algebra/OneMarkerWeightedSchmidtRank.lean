/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MonomialEvaluationSchmidtRank
import QICLean.Algebra.CommutingPolynomialSchmidtRank
import QICLean.Algebra.WordCoefficientExpansion
import QICLean.Algebra.OperatorSchmidtProducts

/-!
# One-marker weighted frequency sums

The actual ordered-word coefficient family on one distinguished frequency slice has
a common interpolation and commuting-gap rank bound. Arbitrary scalar weights are
allowed, including selected subsums. No independence or nonvanishing of operator
coefficients is assumed.

**Local fix (count):** The stars-and-bars factor retains the additional `+1` missing
from AKLV's printed count, as recorded in
`docs/paper-gaps/aklv13_interpolation_and_word_count.tex`:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`),
source lines 626--662. The local tensor form is explicit in this algebraic auxiliary;
its derivation from physical supports and movement to the central chain cut are
separate statements.
-/

open scoped BigOperators Kronecker

namespace WordMultiplicity

/-- The actual ordered-word coefficient with a fixed marker frequency and prescribed
ordinary frequencies. AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`), lines 604--635. -/
noncomputable def oneMarkerCoefficient {ι R : Type*} [Fintype ι] [Semiring R]
    (H : ι → R) (T : R) (m k : ℕ) (α : ι → ℕ) : R :=
  open Classical in
  ∑ w ∈ (Finset.univ : Finset (Fin (m + k) → Option ι)).filter
      (fun w ↦ countsFinsupp w none = k ∧ ∀ a : ι, countsFinsupp w (some a) = α a),
    (List.ofFn (fun p ↦ match w p with
      | none => T
      | some a => H a)).prod

/-- A ring homomorphism preserves the actual one-marker word coefficient.
Supporting change-of-coordinates identity for AKLV, Lemma 4.2, lines 604--635. -/
theorem map_oneMarkerCoefficient {ι R S : Type*} [Fintype ι] [Semiring R] [Semiring S]
    (φ : R →+* S) (H : ι → R) (T : R) (m k : ℕ) (α : ι → ℕ) :
    φ (oneMarkerCoefficient H T m k α) =
      oneMarkerCoefficient (fun a ↦ φ (H a)) (φ T) m k α := by
  classical
  simp only [oneMarkerCoefficient, map_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext p
  dsimp only [Function.comp_def]
  cases w p <;> rfl

end WordMultiplicity

namespace Matrix

open Classical in
/-- A weighted sum of the actual one-marker frequency coefficients has one interpolation
cardinality factor and the corrected commuting-gap bound. AKLV, arXiv:1301.1162v1,
Lemma 4.2 (`l:agsp`), lines 626--662. Zero and dependent coefficient operators are included. -/
theorem operatorSchmidtRank_sum_smul_one_marker_counts_le
    {ι l n : Type*} [Fintype ι] [Fintype l] [Fintype n]
    (H : ι → Matrix (l × n) (l × n) ℂ)
    (HL : ι → Matrix l l ℂ) (HR : ι → Matrix n n ℂ)
    (hlocal : ∀ a, H a = HL a ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix l l ℂ) ⊗ₖ HR a)
    (T : Matrix (l × n) (l × n) ℂ) {r : ℕ} (hT : operatorSchmidtRank T ≤ r)
    (m k : ℕ) :
    let E := Finset.piAntidiag (Finset.univ : Finset ι) m
    let coefficient : E → Matrix (l × n) (l × n) ℂ := fun α ↦
      WordMultiplicity.oneMarkerCoefficient H T m k α.val
    ∀ weight : E → ℂ, operatorSchmidtRank (∑ α : E, weight α • coefficient α) ≤
      E.card * ((m + 2 * k + 1).choose (2 * k + 1) * r ^ k) := by
  intro E coefficient weight
  let residual : E → (ι →₀ ℕ) := fun α ↦ Finsupp.equivFunOnFinite.symm α.val
  have hinj : Set.InjOn residual (Finset.univ : Finset E) := by
    intro α _ β _ h
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm.injective h
  have hmonomial (z : ι → ℂ) (α : E) :
      MvPolynomial.eval z (MvPolynomial.monomial (residual α) (1 : ℂ)) =
        ∏ a, z a ^ α.val a := by
    rw [MvPolynomial.eval_monomial, one_mul,
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
    rfl
  apply (show operatorSchmidtRank (∑ α : E, weight α • coefficient α) ≤
      (Finset.univ : Finset E).card *
        ((m + 2 * k + 1).choose (2 * k + 1) * r ^ k) from ?_).trans_eq
    (by simp only [Finset.card_univ, Fintype.card_coe])
  apply operatorSchmidtRank_sum_smul_le_of_injective_monomial_evaluations
    Finset.univ residual hinj coefficient weight
  intro z
  let A := (∑ a, z a • HL a) ⊗ₖ (1 : Matrix n n ℂ)
  let B := (1 : Matrix l l ℂ) ⊗ₖ (∑ a, z a • HR a)
  have hD : (∑ a, z a • H a) = A + B := by
    simp only [hlocal]
    ext ⟨x, u⟩ ⟨y, v⟩
    simp [A, B, Matrix.sum_apply, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm]
  have hAB : Commute A B := by
    change A * B = B * A
    dsimp only [A, B]
    simp only [← mul_kronecker_mul, mul_one, one_mul]
  have hgenerate := Polynomial.coeff_pow_sum_smul_add_C_mul_X_eq_sum_counts H T z m k
  have hrank := operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le A B T hAB
    (operatorSchmidtRank_kronecker_le_one _ _) (operatorSchmidtRank_kronecker_le_one _ _) hT m k
  change ((Polynomial.C (∑ a, z a • H a) + Polynomial.C T * Polynomial.X) ^
    (m + k)).coeff k = ∑ α : E, (∏ a, z a ^ α.val a) • coefficient α at hgenerate
  simp only [hmonomial]
  rw [← hgenerate, hD]
  exact hrank

end Matrix
