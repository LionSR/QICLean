/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.LocalPolynomialSchmidtRank
import QICLean.Algebra.OperatorSchmidtTwoCuts
import QICLean.Algebra.PolynomialTwoMarkerPower
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Operator Schmidt rank of a tripartite coefficient

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

open scoped BigOperators Kronecker
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
  letI : Fintype n := Fintype.ofFinite n
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
  letI : Fintype m := Fintype.ofFinite m
  letI : Fintype n := Fintype.ofFinite n
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
  letI : Fintype l := Fintype.ofFinite l
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
