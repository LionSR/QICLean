/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.CommutingPolynomialGaps
import QICLean.Algebra.MatrixKroneckerEmbed
import QICLean.Algebra.OperatorSchmidtBounds
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Coefficient extraction with a fixed family of left factors

An inner central variable occurs only in the ordinary operator on the right tensor factor.
The crossing operator and the left-local ordinary operator are constant in
that variable. A commuting-gap expansion then has a finite family of left
factors independent of the inner variable. Taking any inner coefficient
therefore preserves the length bound on this family.

**Local fix (count):** The exponent-tuple count retains the additional `+1`
missing from AKLV, Lemma l:agsp. The correction and its stars-and-bars derivation
are recorded in `docs/paper-gaps/aklv13_interpolation_and_word_count.tex`.

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 604–617 and 646–653, and ALVV, arXiv:1602.08828v2,
Proposition prop:Cheby-AGSP-eff, lines 1324–1332. The two distinguished
frequencies, their common ordered-word family, and the selected low-frequency
partition are later applications. No commutative algebra of operators or
polynomial-variable interchange is used here.
-/

open scoped BigOperators Kronecker
noncomputable section
namespace Matrix

variable {l n : Type*} [Fintype l] [Fintype n]

open Classical in
/-- Coefficientwise tensoring with a fixed left operator, expressed through
an existing unital right tensor homomorphism. -/
private def tensorPolynomial (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ)) :
    Polynomial (Matrix (l × n) (l × n) ℂ) :=
  Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ)) *
    B.map (rightKroneckerEmbed (m := l)).toRingHom

open Classical in
private theorem tensorPolynomial_C (A : Matrix l l ℂ) (B : Matrix n n ℂ) :
    tensorPolynomial A (Polynomial.C B) = Polynomial.C (A ⊗ₖ B) := by
  simp [tensorPolynomial, Polynomial.map_C, ← Polynomial.C_mul,
    rightKroneckerEmbed_apply, ← mul_kronecker_mul]

open Classical in
private theorem coeff_tensorPolynomial
    (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ)) (s : ℕ) :
    (tensorPolynomial A B).coeff s = A ⊗ₖ B.coeff s := by
  simp [tensorPolynomial, Polynomial.coeff_C_mul, Polynomial.coeff_map,
    rightKroneckerEmbed_apply, ← mul_kronecker_mul]

open Classical in
private theorem commute_constant_left_rightPolynomial
    (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ)) :
    Commute (Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ)))
      (B.map (rightKroneckerEmbed (m := l)).toRingHom) := by
  exact Polynomial.ext fun s ↦ by
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_map,
      rightKroneckerEmbed_apply, ← mul_kronecker_mul]

open Classical in
private theorem tensorPolynomial_mul
    (A U : Matrix l l ℂ) (B V : Polynomial (Matrix n n ℂ)) :
    tensorPolynomial A B * tensorPolynomial U V =
      tensorPolynomial (A * U) (B * V) := by
  simpa only [tensorPolynomial, ← Polynomial.C_mul, ← Polynomial.map_mul,
    ← mul_kronecker_mul, mul_one] using
    (commute_constant_left_rightPolynomial U B).symm.mul_mul_mul_comm
      (Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ)))
      (V.map (rightKroneckerEmbed (m := l)).toRingHom)

open Classical in
private theorem tensorPolynomial_powers
    (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ)) (a b : ℕ) :
    Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ)) ^ a *
        (B.map (rightKroneckerEmbed (m := l)).toRingHom) ^ b =
      tensorPolynomial (A ^ a) (B ^ b) := by
  have hA : Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ)) ^ a =
      Polynomial.C ((A ^ a) ⊗ₖ (1 : Matrix n n ℂ)) := by
    induction a <;> simp_all [pow_succ, ← Polynomial.C_mul, ← mul_kronecker_mul]
  simpa only [tensorPolynomial, Polynomial.map_pow] using
    congrArg (fun P : Polynomial (Matrix (l × n) (l × n) ℂ) ↦
      P * (B.map (rightKroneckerEmbed (m := l)).toRingHom) ^ b) hA

open Classical in
/-- The actual left factors associated with a fixed crossing decomposition. -/
private def leftGap (A : Matrix l l ℂ) {r : ℕ} (U : Fin r → Matrix l l ℂ)
    (j : ℕ) (d : Fin (j + 1) × Bool → ℕ) (ξ : Fin j → Fin r) : Matrix l l ℂ :=
  (List.ofFn (fun a : Fin j ↦ A ^ d (a.castSucc, false) * U (ξ a))).prod *
    A ^ d (Fin.last j, false)

open Classical in
/-- The matching right polynomial factors, retaining their original order. -/
private def rightGap (B : Polynomial (Matrix n n ℂ)) {r : ℕ}
    (V : Fin r → Matrix n n ℂ)
    (j : ℕ) (d : Fin (j + 1) × Bool → ℕ) (ξ : Fin j → Fin r) :
    Polynomial (Matrix n n ℂ) :=
  (List.ofFn (fun a : Fin j ↦
    B ^ d (a.castSucc, true) * Polynomial.C (V (ξ a)))).prod *
      B ^ d (Fin.last j, true)

open Classical in
/-- Expanding the crossing factors gives a left family independent of the inner variable.
The hypothesis is an actual product decomposition, not a rank assumption about a coefficient. -/
private theorem polynomial_gap_decomposition
    (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ))
    {r : ℕ} (U : Fin r → Matrix l l ℂ) (V : Fin r → Matrix n n ℂ)
    (j : ℕ) (d : Fin (j + 1) × Bool → ℕ) :
    let Ap := Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ))
    let Bp := B.map (rightKroneckerEmbed (m := l)).toRingHom
    let Tp := Polynomial.C (∑ t, U t ⊗ₖ V t)
    (List.ofFn (fun a : Fin j ↦
      Ap ^ d (a.castSucc, false) * Bp ^ d (a.castSucc, true) * Tp)).prod *
      (Ap ^ d (Fin.last j, false) * Bp ^ d (Fin.last j, true)) =
        ∑ ξ : Fin j → Fin r,
          tensorPolynomial (leftGap A U j d ξ) (rightGap B V j d ξ) := by
  dsimp only
  induction j with
  | zero =>
    simpa [leftGap, rightGap] using
      tensorPolynomial_powers A B (d (0, false)) (d (0, true))
  | succ j ih =>
    rw [List.ofFn_succ, List.prod_cons, mul_assoc]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ, ← Fin.succ_last]
    rw [ih (fun pair ↦ d (pair.1.succ, pair.2))]
    rw [tensorPolynomial_powers]
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul, ← tensorPolynomial_C,
      tensorPolynomial_mul]
    rw [Finset.sum_comm, ← Fintype.sum_prod_type
      (fun pair : Fin r × (Fin j → Fin r) ↦
        tensorPolynomial
          ((A ^ d (0, false) * U pair.1) *
            leftGap A U j (fun qb ↦ d (qb.1.succ, qb.2)) pair.2)
          ((B ^ d (0, true) * Polynomial.C (V pair.1)) *
            rightGap B V j (fun qb ↦ d (qb.1.succ, qb.2)) pair.2))]
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (j + 1) ↦ Fin r)) _ _ ?_
    simp [Fin.consEquiv, leftGap, rightGap, List.ofFn_succ, mul_assoc]

open Classical in
private theorem rank_gap_coefficient_le
    (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ))
    (T : Matrix (l × n) (l × n) ℂ)
    (j : ℕ) (d : Fin (j + 1) × Bool → ℕ) (s : ℕ) :
    let Ap := Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ))
    let Bp := B.map (rightKroneckerEmbed (m := l)).toRingHom
    operatorSchmidtRank
      (((List.ofFn (fun a : Fin j ↦
        Ap ^ d (a.castSucc, false) * Bp ^ d (a.castSucc, true) *
          Polynomial.C T)).prod *
        (Ap ^ d (Fin.last j, false) * Bp ^ d (Fin.last j, true))).coeff s) ≤
      operatorSchmidtRank T ^ j := by
  intro Ap Bp
  obtain ⟨U, V, hT⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank T
  have hcoeff :
      ((List.ofFn (fun a : Fin j ↦
        Ap ^ d (a.castSucc, false) * Bp ^ d (a.castSucc, true) *
          Polynomial.C T)).prod *
        (Ap ^ d (Fin.last j, false) * Bp ^ d (Fin.last j, true))).coeff s =
      ∑ ξ : Fin j → Fin (operatorSchmidtRank T),
        leftGap A U j d ξ ⊗ₖ (rightGap B V j d ξ).coeff s := by
    simpa only [← hT, Polynomial.finsetSum_coeff, coeff_tensorPolynomial] using
      congrArg (fun P : Polynomial (Matrix (l × n) (l × n) ℂ) ↦ P.coeff s)
        (polynomial_gap_decomposition A B U V j d)
  rw [hcoeff]
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    operatorSchmidtRank_le_card_of_blocks_mem_span
      (∑ ξ : Fin j → Fin (operatorSchmidtRank T),
        leftGap A U j d ξ ⊗ₖ (rightGap B V j d ξ).coeff s)
      (fun ξ : Fin j → Fin (operatorSchmidtRank T) ↦ (rightGap B V j d ξ).coeff s)
      (by
        intro x y
        have hblock :
            operatorBlock (∑ ξ : Fin j → Fin (operatorSchmidtRank T),
              leftGap A U j d ξ ⊗ₖ (rightGap B V j d ξ).coeff s) x y =
            ∑ ξ : Fin j → Fin (operatorSchmidtRank T),
              leftGap A U j d ξ x y • (rightGap B V j d ξ).coeff s := by
          ext u v
          simp [operatorBlock, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
        rw [hblock]
        exact Submodule.sum_smul_mem _ _ fun ξ _ ↦ Submodule.subset_span ⟨ξ, rfl⟩)

open Classical in
/-- Any inner coefficient of a distinguished-letter coefficient has the same
commuting-gap rank bound when the inner variable occurs only on the right.
Supporting algebra for ALVV, arXiv:1602.08828v2, prop:Cheby-AGSP-eff,
lines 1324 and 1332, and AKLV, arXiv:1301.1162v1, l:agsp, lines 646–653.
The weak-composition count uses the established additional +1. -/
theorem operatorSchmidtRank_coeff_coeff_pow_left_add_right_le
    (A : Matrix l l ℂ) (B : Polynomial (Matrix n n ℂ))
    (T : Matrix (l × n) (l × n) ℂ)
    {r : ℕ} (hT : operatorSchmidtRank T ≤ r) (m j s : ℕ) :
    let B' : Polynomial (Matrix (l × n) (l × n) ℂ) :=
      B.map (rightKroneckerEmbed (m := l)).toRingHom
    let F : Polynomial (Polynomial (Matrix (l × n) (l × n) ℂ)) :=
      Polynomial.C (Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ)) + B') +
        Polynomial.C (Polynomial.C T) * Polynomial.X
    operatorSchmidtRank (((F ^ (m + j)).coeff j).coeff s) ≤
      (m + 2 * j + 1).choose (2 * j + 1) * r ^ j := by
  intro B' F
  let Ap := Polynomial.C (A ⊗ₖ (1 : Matrix n n ℂ))
  let E := Finset.piAntidiag (Finset.univ : Finset (Fin (j + 1) × Bool)) m
  let G : E → Polynomial (Matrix (l × n) (l × n) ℂ) := fun d ↦
    (List.ofFn (fun a : Fin j ↦
      Ap ^ d.val (a.castSucc, false) * B' ^ d.val (a.castSucc, true) *
        Polynomial.C T)).prod *
      (Ap ^ d.val (Fin.last j, false) * B' ^ d.val (Fin.last j, true))
  have hspan : (F ^ (m + j)).coeff j ∈ Submodule.span ℂ (Set.range G) :=
    Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps (𝕜 := ℂ)
      Ap B' (Polynomial.C T) (commute_constant_left_rightPolynomial A B) m j
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan
  have hcoeff : ((F ^ (m + j)).coeff j).coeff s =
      ∑ d : E, c d • (G d).coeff s := by
    simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul] using
      congrArg (fun P : Polynomial (Matrix (l × n) (l × n) ℂ) ↦ P.coeff s) hc.symm
  rw [hcoeff]
  refine (operatorSchmidtRank_sum_le Finset.univ (fun d : E ↦ c d • (G d).coeff s)).trans ?_
  calc
    _ ≤ ∑ _ : E, r ^ j := Finset.sum_le_sum fun d _ ↦
      (operatorSchmidtRank_smul_le (c d) ((G d).coeff s)).trans
        ((rank_gap_coefficient_le A B T j d.val s).trans (Nat.pow_le_pow_left hT j))
    _ = _ := by simp [E, Finset.card_piAntidiag_univ_fin_prod_bool]

end Matrix
