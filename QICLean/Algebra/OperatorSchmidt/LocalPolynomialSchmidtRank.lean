/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Polynomial.CommutingPolynomialGaps
import QICLean.Algebra.Matrix.KroneckerEmbed
import QICLean.Algebra.OperatorSchmidt.Bounds
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import QICLean.Algebra.OperatorSchmidt.Basic
import QICLean.Algebra.Polynomial.OrderedPolynomialGaps
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.LinearAlgebra.Matrix.Reindex

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

It also contains the following results.

* `Matrix.operatorSchmidtRank_middle_coeff_coeff_pow_le`: operator Schmidt rank of a tripartite
  coefficient.
-/

open scoped BigOperators Kronecker

section LocalPolynomialSchmidtRank

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

end

end LocalPolynomialSchmidtRank

section TripartitePolynomialSchmidtRank

/-!
## Operator Schmidt rank of a tripartite coefficient

Three local ordinary operators and two crossing operators define a common
coefficient counting both distinguished occurrences. Its middle-versus-exterior
operator Schmidt rank is bounded by the product of the two commuting-gap counts
and the corresponding powers of the crossing ranks. Finite factors of dimension
zero are included.

**Local fix (count):** The exponent-tuple counts retain the additional `+1`
missing from AKLV, Lemma l:agsp. The corrected count is recorded in
`docs/paper-gaps/aklv13_interpolation_and_word_count.tex`.

Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7,
prop:Cheby-AGSP-eff, lines 1316–1332, especially the simultaneous boundary
control at lines 1324 and 1332. The displayed tensor supports are explicit
assumptions of this auxiliary algebraic statement; their identification with
physical chain terms and the low-frequency partition are separate steps.
This theorem does not assert the full proposition, a spectral estimate, or
an MPO construction.
-/

noncomputable section

namespace Matrix

/-- The coefficient counting the two distinguished occurrences. -/
private def twoCount {R : Type*} [Semiring R]
    (D U V : R) (k i j : ℕ) : R :=
  let F : Polynomial (Polynomial R) :=
    Polynomial.C (Polynomial.C D + Polynomial.C V * Polynomial.X) +
      Polynomial.C (Polynomial.C U) * Polynomial.X
  ((F ^ k).coeff i).coeff j

/-- Coefficientwise transport uses a ring homomorphism, with no commutative
coefficient-algebra assumption. -/
private theorem twoCount_map {R S : Type*} [Semiring R] [Semiring S]
    (f : R →+* S) (D U V : R) (k i j : ℕ) :
    f (twoCount D U V k i j) = twoCount (f D) (f U) (f V) k i j := by
  unfold twoCount
  dsimp only
  have hP :
      (Polynomial.C (Polynomial.C (f D) + Polynomial.C (f V) * Polynomial.X) +
          Polynomial.C (Polynomial.C (f U)) * Polynomial.X) =
        (Polynomial.C (Polynomial.C D + Polynomial.C V * Polynomial.X) +
          Polynomial.C (Polynomial.C U) * Polynomial.X).map
            (Polynomial.mapRingHom f) := by
    simp only [Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.coe_mapRingHom]
  rw [hP, ← Polynomial.map_pow]
  simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]

open Classical in
/-- The existing one-sided estimate already allows an arbitrary inner
coefficient, because its left product family is independent of that variable. -/
private theorem rank_twoCount_left_boundary
    {l n : Type*} [Fintype l] [Fintype n] [dl : DecidableEq l] [dn : DecidableEq n]
    (A : Matrix l l ℂ) (B₀ B₁ : Matrix n n ℂ)
    (T : Matrix (l × n) (l × n) ℂ)
    {r k i j : ℕ} (hT : operatorSchmidtRank T ≤ r) (hi : i ≤ k) :
    operatorSchmidtRank
        (twoCount (A ⊗ₖ (1 : Matrix n n ℂ) +
          (1 : Matrix l l ℂ) ⊗ₖ B₀) T
          ((1 : Matrix l l ℂ) ⊗ₖ B₁) k i j) ≤
      (k + i + 1).choose (2 * i + 1) * r ^ i := by
  cases Subsingleton.elim dl (Classical.typeDecidableEq l)
  cases Subsingleton.elim dn (Classical.typeDecidableEq n)
  have hk : k - i + i = k := Nat.sub_add_cancel hi
  have hc : k - i + 2 * i + 1 = k + i + 1 := by
    simp only [two_mul, ← Nat.add_assoc, hk]
  have h := operatorSchmidtRank_coeff_coeff_pow_left_add_right_le A
    (Polynomial.C B₀ + Polynomial.C B₁ * Polynomial.X) T hT (k - i) i j
  simp only [twoCount, Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul,
    Polynomial.map_X, rightKroneckerEmbed, Polynomial.C_add, add_assoc, hk, hc] at h ⊢
  convert h using 1
  congr 8

open Classical in
/-- Reindexing into an actual one-sided tensor decomposition transports the
same coefficient before applying the fixed-left-family bound. -/
private theorem rank_twoCount_reindex_left
    {p l n : Type*} [Fintype p] [Fintype l] [Finite n]
    [DecidableEq p] [DecidableEq l] [DecidableEq n]
    (e : p ≃ l × n) (D U V : Matrix p p ℂ)
    (A : Matrix l l ℂ) (B₀ B₁ : Matrix n n ℂ)
    {r k i j : ℕ}
    (hD : D.reindex e e = A ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix l l ℂ) ⊗ₖ B₀)
    (hV : V.reindex e e = (1 : Matrix l l ℂ) ⊗ₖ B₁)
    (hU : operatorSchmidtRank (U.reindex e e) ≤ r) (hi : i ≤ k) :
    operatorSchmidtRank ((twoCount D U V k i j).reindex e e) ≤
      (k + i + 1).choose (2 * i + 1) * r ^ i := by
  let : Fintype n := Fintype.ofFinite n
  have ht : (twoCount D U V k i j).reindex e e =
      twoCount (D.reindex e e) (U.reindex e e) (V.reindex e e) k i j :=
    twoCount_map (Matrix.reindexRingEquiv ℂ e).toRingHom D U V k i j
  rw [ht, hD, hV]
  exact rank_twoCount_left_boundary A B₀ B₁ (U.reindex e e) hU hi

/-- Reversing the two tensor factors preserves operator Schmidt rank. The
proof exchanges factors in an actual minimal product decomposition. -/
private theorem rank_flip_le
    {l n : Type*} [Fintype l] [Fintype n]
    (W : Matrix (l × n) (l × n) ℂ) :
    operatorSchmidtRank
        (W.reindex (Equiv.prodComm l n) (Equiv.prodComm l n)) ≤
      operatorSchmidtRank W := by
  classical
  obtain ⟨A, B, hW⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank W
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨B, A, ?_⟩
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp [hW, Matrix.reindex_apply, Matrix.sum_apply, mul_comm]

private theorem rank_flip_eq
    {l n : Type*} [Fintype l] [Fintype n]
    (W : Matrix (l × n) (l × n) ℂ) :
    operatorSchmidtRank
        (W.reindex (Equiv.prodComm l n) (Equiv.prodComm l n)) =
      operatorSchmidtRank W := by
  apply Nat.le_antisymm (rank_flip_le W)
  have h := rank_flip_le
    (W.reindex (Equiv.prodComm l n) (Equiv.prodComm l n))
  have hinv :
      (W.reindex (Equiv.prodComm l n) (Equiv.prodComm l n)).reindex
        (Equiv.prodComm n l) (Equiv.prodComm n l) = W := by
    ext ⟨x, y⟩ ⟨x', y'⟩
    rfl
  simpa only [hinv] using h

open Classical in
/-- Adding an identity spectator to the right does not increase the left
boundary rank. No spectator dimension is cancelled. -/
private theorem rank_left_spectator_le
    {l m n : Type*} [Fintype l] [Finite m] [Finite n]
    (U : Matrix (l × m) (l × m) ℂ) :
    operatorSchmidtRank
        ((U ⊗ₖ (1 : Matrix n n ℂ)).reindex
          (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n)) ≤
      operatorSchmidtRank U := by
  classical
  let : Fintype m := Fintype.ofFinite m
  let : Fintype n := Fintype.ofFinite n
  obtain ⟨A, B, hU⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank U
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨A, fun t ↦ B t ⊗ₖ (1 : Matrix n n ℂ), ?_⟩
  ext ⟨x, y, z⟩ ⟨x', y', z'⟩
  simp [hU, Matrix.reindex_apply, Matrix.sum_apply,
    Finset.sum_mul, mul_assoc]

open Classical in
/-- The corresponding reflected spectator estimate at the right boundary. -/
private theorem rank_right_spectator_le
    {l m n : Type*} [Finite l] [Fintype m] [Fintype n]
    (V : Matrix (m × n) (m × n) ℂ) :
    operatorSchmidtRank
        ((((1 : Matrix l l ℂ) ⊗ₖ V).reindex
          (Equiv.prodAssoc l m n).symm (Equiv.prodAssoc l m n).symm).reindex
            (Equiv.prodComm (l × m) n) (Equiv.prodComm (l × m) n)) ≤
      operatorSchmidtRank V := by
  classical
  let : Fintype l := Fintype.ofFinite l
  obtain ⟨B, C, hV⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank V
  apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
  refine ⟨C, fun t ↦ (1 : Matrix l l ℂ) ⊗ₖ B t, ?_⟩
  ext ⟨z, x, y⟩ ⟨z', x', y'⟩
  simp [hV, Matrix.reindex_apply, Matrix.sum_apply,
    Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

open Classical in
/-- The three local ordinary terms in left-boundary coordinates. -/
private theorem three_local_reindex_left
    {l m n : Type*}
    (AL : Matrix l l ℂ) (AM : Matrix m m ℂ) (AR : Matrix n n ℂ) :
    (((AL ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix n n ℂ) +
      ((1 : Matrix l l ℂ) ⊗ₖ AM) ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix (l × m) (l × m) ℂ) ⊗ₖ AR).reindex
        (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n)) =
      AL ⊗ₖ (1 : Matrix (m × n) (m × n) ℂ) +
        (1 : Matrix l l ℂ) ⊗ₖ
          (AM ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ AR) := by
  simp only [← one_kronecker_one (m := l) (n := m), Matrix.reindex_apply,
    Matrix.submatrix_add, Pi.add_apply, Matrix.kronecker_assoc',
    one_kronecker_one (m := m) (n := n), Matrix.kronecker_add, add_assoc]

open Classical in
/-- Simultaneous boundary control for the same actual double-frequency
coefficient. Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition 5.7,
prop:Cheby-AGSP-eff, lines 1316–1332. The explicit tensor forms state precisely
the support used here; no physical Hamiltonian identification is asserted. -/
theorem operatorSchmidtRank_middle_coeff_coeff_pow_le
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    (AL : Matrix l l ℂ) (AM : Matrix m m ℂ) (AR : Matrix n n ℂ)
    (U : Matrix (l × m) (l × m) ℂ)
    (V : Matrix (m × n) (m × n) ℂ)
    {rU rV k i j : ℕ}
    (hU : operatorSchmidtRank U ≤ rU)
    (hV : operatorSchmidtRank V ≤ rV)
    (hi : i ≤ k) (hj : j ≤ k) :
    let a := Equiv.prodAssoc l m n
    let e := a.trans ((Equiv.prodComm l (m × n)).trans
      ((Equiv.prodAssoc m n l).trans
        (Equiv.prodCongr (Equiv.refl m) (Equiv.prodComm n l))))
    let D : Matrix ((l × m) × n) ((l × m) × n) ℂ :=
      (AL ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix n n ℂ) +
      ((1 : Matrix l l ℂ) ⊗ₖ AM) ⊗ₖ (1 : Matrix n n ℂ) +
      (1 : Matrix (l × m) (l × m) ℂ) ⊗ₖ AR
    let U' := U ⊗ₖ (1 : Matrix n n ℂ)
    let V' := ((1 : Matrix l l ℂ) ⊗ₖ V).reindex a.symm a.symm
    let F : Polynomial (Polynomial
        (Matrix ((l × m) × n) ((l × m) × n) ℂ)) :=
      Polynomial.C (Polynomial.C D + Polynomial.C V' * Polynomial.X) +
        Polynomial.C (Polynomial.C U') * Polynomial.X
    let K := ((F ^ k).coeff i).coeff j
    operatorSchmidtRank (K.reindex e e) ≤
      (k + i + 1).choose (2 * i + 1) *
        (k + j + 1).choose (2 * j + 1) * rU ^ i * rV ^ j := by
  classical
  intro a e D U' V' F K
  let b := Equiv.prodComm (l × m) n
  let BL : Matrix (m × n) (m × n) ℂ :=
    AM ⊗ₖ (1 : Matrix n n ℂ) + (1 : Matrix m m ℂ) ⊗ₖ AR
  let BR : Matrix (l × m) (l × m) ℂ :=
    AL ⊗ₖ (1 : Matrix m m ℂ) + (1 : Matrix l l ℂ) ⊗ₖ AM
  have hDL : D.reindex a a =
      AL ⊗ₖ (1 : Matrix (m × n) (m × n) ℂ) +
        (1 : Matrix l l ℂ) ⊗ₖ BL := by
    exact three_local_reindex_left AL AM AR
  have hVL : V'.reindex a a = (1 : Matrix l l ℂ) ⊗ₖ V := by
    ext ⟨x, y, z⟩ ⟨x', y', z'⟩
    rfl
  have hUL : operatorSchmidtRank (U'.reindex a a) ≤ rU :=
    (rank_left_spectator_le (n := n) U).trans hU
  have hLraw := rank_twoCount_reindex_left (p := (l × m) × n) (l := l) (n := m × n)
    a D U' V' AL BL V (r := rU) (k := k) (i := i) (j := j)
      hDL hVL hUL hi
  have hL : operatorSchmidtRank (K.reindex a a) ≤
      (k + i + 1).choose (2 * i + 1) * rU ^ i := hLraw
  have hDR : D.reindex b b =
      AR ⊗ₖ (1 : Matrix (l × m) (l × m) ℂ) +
        (1 : Matrix n n ℂ) ⊗ₖ BR := by
    ext ⟨z, x, y⟩ ⟨z', x', y'⟩
    simp [D, b, BR, Matrix.reindex_apply,
      Matrix.one_apply, Matrix.add_apply, mul_add,
      mul_comm, add_assoc, add_comm, add_left_comm, ite_and]
    split_ifs <;> simp_all
  have hUR : U'.reindex b b = (1 : Matrix n n ℂ) ⊗ₖ U := by
    ext ⟨z, x, y⟩ ⟨z', x', y'⟩
    simp [U', b, Matrix.reindex_apply, mul_comm]
  have hKR : K.reindex b b =
      twoCount (AR ⊗ₖ (1 : Matrix (l × m) (l × m) ℂ) +
          (1 : Matrix n n ℂ) ⊗ₖ BR)
        (V'.reindex b b) ((1 : Matrix n n ℂ) ⊗ₖ U) k j i := by
    have ht : (twoCount D U' V' k i j).reindex b b =
        twoCount (D.reindex b b) (U'.reindex b b) (V'.reindex b b) k i j :=
      twoCount_map (Matrix.reindexRingEquiv ℂ b).toRingHom D U' V' k i j
    change (twoCount D U' V' k i j).reindex b b = _
    rw [ht]
    have hs :
        twoCount (D.reindex b b) (U'.reindex b b) (V'.reindex b b) k i j =
          twoCount (D.reindex b b) (V'.reindex b b) (U'.reindex b b) k j i := by
      exact Polynomial.coeff_coeff_pow_two_markers_swap
        (D.reindex b b) (U'.reindex b b) (V'.reindex b b) k i j
    rw [hs, hDR, hUR]
  have hR : operatorSchmidtRank K ≤
      (k + j + 1).choose (2 * j + 1) * rV ^ j := by
    rw [← rank_flip_eq K]
    change operatorSchmidtRank (K.reindex b b) ≤ _
    rw [hKR]
    exact rank_twoCount_left_boundary AR BR U (V'.reindex b b)
      ((rank_right_spectator_le (l := l) V).trans hV) hj
  calc
    operatorSchmidtRank (K.reindex e e) ≤
        operatorSchmidtRank (K.reindex a a) * operatorSchmidtRank K :=
      operatorSchmidtRank_middle_le_mul K
    _ ≤ ((k + i + 1).choose (2 * i + 1) * rU ^ i) *
        ((k + j + 1).choose (2 * j + 1) * rV ^ j) := Nat.mul_le_mul hL hR
    _ = _ := by ac_rfl

end Matrix

end

end TripartitePolynomialSchmidtRank
