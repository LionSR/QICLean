/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import QICLean.Algebra.HermitianHelpers
import QICLean.Algebra.MatrixSpectralDecomp
import QICLean.Analysis.DeterminantTraceBound
import QICLean.Analysis.MatrixTraceInequalities
import QICLean.Channel.Basic

/-!
# Choi-type positive maps

This file records the Choi-type maps appearing in Wolf Chapter 3, Example 3.1,
equation (3.20).  The map is written on the cyclic index set `ZMod d`, which is
the natural home for the shift matrices \(U_{k0}\):
\[
  T_C(X)=(d-n)D(X)-X+\sum_{k=1}^{n}D(U_{k0}XU_{k0}^{\dagger}),
\]
where `D` projects a matrix to its diagonal part.

The main theorem in this file is the exact action on rank-one projectors.  This
is the algebraic reduction needed for the positivity proof of Wolf Example 3.1.
This file proves positivity at both ends of Wolf's range: \(n=1\) and
\(n=d-2\), in every dimension \(d\ge3\).  The scalar input for the top slice
is a reciprocal inequality valid for an arbitrary permutation; the bottom
slice follows from an elementary-symmetric AM--GM expansion.  The middle range
\(2\le n\le d-3\) still requires the general cyclic reciprocal inequality for
the diagonal weights.  Indecomposability is not proved here.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Example 3.1, equation (3.20)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder InnerProductSpace
open Finset

namespace Matrix

variable {d : ℕ} [NeZero d]

/-! ## Basic cyclic and diagonal operations -/

/-- The cyclic shift matrix \(U_{k0}\) from Wolf, equation (2.24), sending
\(\ket r\) to \(\ket{k+r}\). -/
def choiTypeShift (k : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (Equiv.addRight (-k)).permMatrix ℂ

/-- The diagonal projection \(D(X)\), which keeps the diagonal entries and
sets all off-diagonal entries to zero. -/
def diagonalProjection (d : ℕ) :
    Matrix (ZMod d) (ZMod d) ℂ →ₗ[ℂ] Matrix (ZMod d) (ZMod d) ℂ where
  toFun X := diagonal fun i => X i i
  map_add' X Y := by
    ext i j
    by_cases h : i = j <;> simp [h]
  map_smul' c X := by
    ext i j
    by_cases h : i = j <;> simp [h]

omit [NeZero d] in
@[simp]
theorem diagonalProjection_apply (X : Matrix (ZMod d) (ZMod d) ℂ) :
    diagonalProjection d X = diagonal fun i => X i i :=
  rfl

/-- Conjugation by a matrix, as the linear map \(X\mapsto AXA^\dagger\).

Wolf's Choi-type maps use this operation in the terms
\(U_{k0}XU_{k0}^{\dagger}\).  As a map on matrices it is completely positive;
that fact is not used in this file. -/
def conjugationLinearMap {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := A * X * Aᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

@[simp]
theorem conjugationLinearMap_apply {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (X : Matrix n n ℂ) :
    conjugationLinearMap A X = A * X * Aᴴ :=
  rfl

/-- The diagonal part of a cyclically conjugated matrix is the shifted diagonal. -/
theorem diagonalProjection_conj_choiTypeShift
    (k : ZMod d) (X : Matrix (ZMod d) (ZMod d) ℂ) :
    diagonalProjection d (choiTypeShift k * X * (choiTypeShift k)ᴴ) =
      diagonal fun i => X (i - k) (i - k) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [diagonalProjection, choiTypeShift, Equiv.Perm.permMatrix,
      PEquiv.toMatrix, Matrix.mul_apply, sub_eq_add_neg]
  · simp [diagonalProjection, h]

/-! ## The Choi-type map -/

/-- **Wolf Chapter 3, Example 3.1, equation (3.20).**  The Choi-type map
\[
  T_C(X)=(d-n)D(X)-X+\sum_{k=1}^{n}D(U_{k0}XU_{k0}^{\dagger})
\]
on matrices indexed by the cyclic group `ZMod d`.  The coefficient `d - n` is
the scalar difference appearing in the source; the positivity theorem uses the
range `1 ≤ n ≤ d - 2`. -/
def choiTypeMap (d n : ℕ) [NeZero d] :
    Matrix (ZMod d) (ZMod d) ℂ →ₗ[ℂ] Matrix (ZMod d) (ZMod d) ℂ :=
  ((d : ℂ) - (n : ℂ)) • diagonalProjection d - LinearMap.id +
    ∑ k : Fin n,
      (diagonalProjection d).comp
        (conjugationLinearMap (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d)))

@[simp]
theorem choiTypeMap_apply (n : ℕ) (X : Matrix (ZMod d) (ZMod d) ℂ) :
    choiTypeMap d n X =
      ((d : ℂ) - (n : ℂ)) • diagonalProjection d X - X +
        ∑ k : Fin n,
          diagonalProjection d
            (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d) * X *
              (choiTypeShift ((k.1 + 1 : ℕ) : ZMod d))ᴴ) := by
  simp [choiTypeMap]

/-- The Choi-type map applied to a rank-one projector is a diagonal matrix minus
that projector.  This is the rank-one reduction underlying Wolf's positivity
argument for equation (3.20). -/
theorem choiTypeMap_vecMulVec
    (n : ℕ) (v : ZMod d → ℂ) :
    choiTypeMap d n (vecMulVec v (star v)) =
      diagonal (fun i =>
        ((d : ℂ) - (n : ℂ)) * (v i * star (v i)) +
          ∑ k : Fin n,
            v (i - ((k.1 + 1 : ℕ) : ZMod d)) *
              star (v (i - ((k.1 + 1 : ℕ) : ZMod d)))) -
        vecMulVec v (star v) := by
  rw [choiTypeMap_apply]
  simp_rw [diagonalProjection_conj_choiTypeShift]
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
    ring_nf
  · simp [Matrix.sum_apply, vecMulVec_apply, h, smul_eq_mul]

/-- The real diagonal weight appearing in the rank-one Choi-type image. -/
noncomputable def choiTypeRankOneWeight (d n : ℕ) [NeZero d] (v : ZMod d → ℂ)
    (i : ZMod d) : ℝ :=
  ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 +
    ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2

private theorem choiType_cyclic_reciprocal_three_one_amgm
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * x * y * z ≤ x ^ 2 * y + y ^ 2 * z + z ^ 2 * x := by
  let f : Fin 3 → ℝ := ![x ^ 2 * y, y ^ 2 * z, z ^ 2 * x]
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    fin_cases i
    · change 0 ≤ x ^ 2 * y
      positivity
    · change 0 ≤ y ^ 2 * z
      positivity
    · change 0 ≤ z ^ 2 * x
      positivity
  have h := pow_card_mul_prod_le_sum_pow (D := 3) f hf
  have hcube : (3 * x * y * z) ^ 3 ≤
      (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ^ 3 := by
    simpa [f, Fin.prod_univ_three, Fin.sum_univ_three, pow_succ, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hleft_nonneg : 0 ≤ 3 * x * y * z := by positivity
  have hright_nonneg : 0 ≤ x ^ 2 * y + y ^ 2 * z + z ^ 2 * x := by positivity
  exact (pow_le_pow_iff_left₀ hleft_nonneg hright_nonneg
    (by decide : (3 : ℕ) ≠ 0)).mp hcube

/-- The first Choi cyclic reciprocal estimate, including boundary points.

**Scope restriction:** See
`docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`.  This proves
only the three-variable scalar estimate needed for the \(d=3,n=1\) rank-one
subcase of Wolf Chapter 3, Example 3.1, equation (3.20).  It is retained as an
explicit three-variable specialization of the general `n = 1` estimate below. -/
theorem choiType_cyclic_reciprocal_three_one_of_nonneg
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x / (2 * x + z) + y / (2 * y + x) + z / (2 * z + y) ≤ 1 := by
  by_cases hA : x * 2 + z = 0
  · have hx0 : x = 0 := by nlinarith
    have hz0 : z = 0 := by nlinarith
    subst x
    subst z
    simp only [mul_zero, add_zero, div_zero, zero_add, zero_div, ge_iff_le]
    by_cases hy0 : y = 0
    · subst y
      norm_num
    · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
      have h2y : 2 * y ≠ 0 := by positivity
      field_simp [h2y, hypos.ne']
      linarith
  by_cases hB : 2 * y + x = 0
  · have hy0 : y = 0 := by nlinarith
    have hx0 : x = 0 := by nlinarith
    subst y
    subst x
    simp only [mul_zero, zero_add, zero_div, add_zero, div_zero, ge_iff_le]
    by_cases hz0 : z = 0
    · subst z
      norm_num
    · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
      have h2z : 2 * z ≠ 0 := by positivity
      field_simp [h2z, hzpos.ne']
      linarith
  by_cases hC : 2 * z + y = 0
  · have hz0 : z = 0 := by nlinarith
    have hy0 : y = 0 := by nlinarith
    subst z
    subst y
    simp only [add_zero, mul_zero, zero_add, zero_div, div_zero, ge_iff_le]
    by_cases hx0 : x = 0
    · subst x
      norm_num
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have h2x : 2 * x ≠ 0 := by positivity
      field_simp [h2x, hxpos.ne']
      linarith
  have hApos : 0 < x * 2 + z :=
    lt_of_le_of_ne (by positivity : 0 ≤ x * 2 + z) (Ne.symm hA)
  have hBpos : 0 < 2 * y + x :=
    lt_of_le_of_ne (by positivity : 0 ≤ 2 * y + x) (Ne.symm hB)
  have hCpos : 0 < 2 * z + y :=
    lt_of_le_of_ne (by positivity : 0 ≤ 2 * z + y) (Ne.symm hC)
  rw [← sub_nonneg]
  field_simp [hApos.ne', hBpos.ne', hCpos.ne']
  have hamgm := choiType_cyclic_reciprocal_three_one_amgm hx hy hz
  nlinarith [hamgm]

/-- The cyclic reciprocal sum for the Choi rank-one weights when \(d=3\) and
\(n=1\), written in the three explicit cyclic coordinates. -/
theorem choiTypeRankOneWeight_reciprocal_sum_three_one (v : ZMod 3 → ℂ) :
    ∑ i : ZMod 3, ‖v i‖ ^ 2 / choiTypeRankOneWeight 3 1 v i =
      ‖v 0‖ ^ 2 / (2 * ‖v 0‖ ^ 2 + ‖v 2‖ ^ 2) +
        ‖v 1‖ ^ 2 / (2 * ‖v 1‖ ^ 2 + ‖v 0‖ ^ 2) +
          ‖v 2‖ ^ 2 / (2 * ‖v 2‖ ^ 2 + ‖v 1‖ ^ 2) := by
  have hfin2 : (ZMod.finEquiv 3) 2 = (2 : ZMod 3) := by decide
  have hminus : (-(1 : ZMod 3)) = 2 := by decide
  rw [← (ZMod.finEquiv 3).toEquiv.sum_comp]
  rw [Fin.sum_univ_three]
  simp [choiTypeRankOneWeight, hfin2, hminus]
  ring_nf

/-- Rank-one positivity of the Choi-type map reduced to the cyclic reciprocal
bound for the diagonal weights.

In the range \(n \le d-2\), the remaining scalar task is to prove the displayed
bound for all vectors `v`.  The cyclic placement of the shifted weights is
essential; equality of the two total sums alone does not imply such a bound. -/
theorem choiTypeMap_vecMulVec_posSemidef_of_weight_sum_le_one
    (n : ℕ) (v : ZMod d → ℂ) (hn₂ : n ≤ d - 2)
    (hbound : ∑ i, ‖v i‖ ^ 2 / choiTypeRankOneWeight d n v i ≤ 1) :
    (choiTypeMap d n (vecMulVec v (star v))).PosSemidef := by
  classical
  let a : ZMod d → ℝ := fun i => choiTypeRankOneWeight d n v i
  have hdpos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hnlt : n < d := by omega
  have hnle : n ≤ d := le_of_lt hnlt
  have hdn_nonneg : 0 ≤ (d : ℝ) - (n : ℝ) := by
    have hnleR : (n : ℝ) ≤ (d : ℝ) := by exact_mod_cast hnle
    linarith
  have hdn_pos : 0 < (d : ℝ) - (n : ℝ) := by
    have hnltR : (n : ℝ) < (d : ℝ) := by exact_mod_cast hnlt
    linarith
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a, choiTypeRankOneWeight]
    exact add_nonneg (mul_nonneg hdn_nonneg (sq_nonneg _))
      (Finset.sum_nonneg fun k _ => sq_nonneg _)
  have hvzero : ∀ i, a i = 0 → v i = 0 := by
    intro i hi
    have hfirst_nonneg : 0 ≤ ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 :=
      mul_nonneg hdn_nonneg (sq_nonneg _)
    have hsum_nonneg :
        0 ≤ ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2 :=
      Finset.sum_nonneg fun k _ => sq_nonneg _
    have hsum_eq :
        ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 +
            ∑ k : Fin n, ‖v (i - ((k.1 + 1 : ℕ) : ZMod d))‖ ^ 2 = 0 := by
      simpa [a, choiTypeRankOneWeight] using hi
    have hfirst_zero : ((d : ℝ) - (n : ℝ)) * ‖v i‖ ^ 2 = 0 := by
      nlinarith
    have hnormsq_zero : ‖v i‖ ^ 2 = 0 := by
      nlinarith [hfirst_zero, hdn_pos, sq_nonneg (‖v i‖)]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq_zero)
  have hdiag :
      (diagonal (fun i => (a i : ℂ)) - vecMulVec v (star v)).PosSemidef :=
    diagonal_sub_vecMulVec_posSemidef_of_sum_normSq_div_le_one a v ha hvzero
      (by simpa [a] using hbound)
  rw [choiTypeMap_vecMulVec]
  convert hdiag using 1
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [a, choiTypeRankOneWeight, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  · simp [hij]

/-- Rank-one positivity for the first Choi map.

For \(d=3\), \(n=1\), the rank-one image \(T_C(|v\rangle\langle v|)\) is
positive semidefinite.

**Scope restriction:** See
`docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`.  This is only
the \(3\times3\) rank-one subcase of the positivity assertion in Wolf Chapter 3,
Example 3.1, equation (3.20).  It is retained as the explicit \(3\times3\)
specialization and is subsumed by `choiTypeMap_vecMulVec_posSemidef_one`. -/
theorem choiTypeMap_vecMulVec_posSemidef_three_one (v : ZMod 3 → ℂ) :
    (choiTypeMap 3 1 (vecMulVec v (star v))).PosSemidef := by
  refine choiTypeMap_vecMulVec_posSemidef_of_weight_sum_le_one
    (d := 3) (n := 1) v (by decide) ?_
  have hnonneg0 : 0 ≤ ‖v 0‖ ^ 2 := sq_nonneg _
  have hnonneg1 : 0 ≤ ‖v 1‖ ^ 2 := sq_nonneg _
  have hnonneg2 : 0 ≤ ‖v 2‖ ^ 2 := sq_nonneg _
  rw [choiTypeRankOneWeight_reciprocal_sum_three_one]
  exact choiType_cyclic_reciprocal_three_one_of_nonneg hnonneg0 hnonneg1 hnonneg2

/-- A linear map on matrices is positive once its values on all rank-one
projectors are positive semidefinite: a positive semidefinite matrix is the
sum of the rank-one projectors of its spectral decomposition. -/
theorem isPositiveMap_of_forall_vecMulVec_posSemidef
    {m : Type*} [Finite m] (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : ∀ w : m → ℂ, (Φ (vecMulVec w (star w))).PosSemidef) :
    IsPositiveMap Φ := by
  classical
  let := Fintype.ofFinite m
  intro X hX
  rw [hX.eq_sum_vecMulVec_nonzero_eigs]
  rw [map_sum]
  exact Matrix.posSemidef_sum Finset.univ fun i _ => by
    let w : m → ℂ := fun p =>
      ((Real.sqrt (hX.1.eigenvalues i.1) : ℂ)) *
        hX.1.eigenvectorUnitary p i.1
    convert h w using 2
    ext p q
    simp [w, Matrix.vecMulVec_apply]

/-- Positivity of the first Choi map.

**Scope restriction:** See
`docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`.  This proves
only the \(d=3,n=1\) specialization of Wolf Chapter 3, Example 3.1,
equation (3.20), and is subsumed by `choiTypeMap_isPositiveMap_one`. -/
theorem choiTypeMap_isPositiveMap_three_one :
    IsPositiveMap (choiTypeMap 3 1) :=
  isPositiveMap_of_forall_vecMulVec_posSemidef _
    choiTypeMap_vecMulVec_posSemidef_three_one

/-! ## The top of Wolf's range: `n = d - 2`

For `n = d - 2` the backward window `x_{i-1}, …, x_{i-n}` misses exactly the
entries at `i` and `i + 1`, so the Choi diagonal weight collapses to
\(a_i = T + x_i - x_{i+1}\) with \(T = \sum_j x_j\).  The cyclic reciprocal
estimate for this case follows from a reciprocal inequality that holds for an
arbitrary permutation in place of the cyclic shift.  This case of Wolf's
positivity assertion is classical: it is due to Ando (*Positivity of certain
maps*, seminar notes, 1985), as recorded by Yamagami
[*Cyclic inequalities*, Proc. Amer. Math. Soc. 118 (1993), 521–527], who
proved the estimate for the whole range \(1\le n\le d-1\). -/

/-- Elementary summand bound for the permutation reciprocal inequality: if
`a + b ≤ T`, then \(a/(T+a-b) \le (aT - a(a-b) + (a-b)^2/2)/T^2\), because the
difference of the two sides is \((a-b)^2 (T-a-b) / 2\) up to the positive
denominators.  Zero denominators are read by the convention `x / 0 = 0`. -/
private theorem perm_reciprocal_term_le {T a b : ℝ} (ha : 0 ≤ a)
    (hT : 0 < T) (hpair : a + b ≤ T) :
    a / (T + a - b) ≤ (a * T - a * (a - b) + (a - b) ^ 2 / 2) / T ^ 2 := by
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ T + a - b by linarith) with h0 | hpos
  · have ha0 : a = 0 := by linarith
    subst ha0
    rw [zero_div]
    have hnum : (0 : ℝ) * T - 0 * (0 - b) + (0 - b) ^ 2 / 2 = b ^ 2 / 2 := by ring
    rw [hnum]
    positivity
  · rw [div_le_div_iff₀ hpos (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (a - b)) (sub_nonneg.2 hpair)]

/-- **The permutation reciprocal inequality.**  For nonnegative reals `x` with
total mass \(T=\sum_j x_j\) and any permutation \(\sigma\),
\[
  \sum_i \frac{x_i}{T + x_i - x_{\sigma(i)}} \le 1 ,
\]
with zero-denominator summands read as `0`.  Each summand is bounded by
\((x_iT - x_i\delta_i + \delta_i^2/2)/T^2\) with \(\delta_i=x_i-x_{\sigma(i)}\),
and the bounds sum to `1` exactly because
\(\sum_i x_i\delta_i = \tfrac12\sum_i \delta_i^2\) for a permutation.

Applied with \(\sigma\) the cyclic shift on `ZMod d`, this is the case
`n = d - 2` of the cyclic reciprocal estimate behind Wolf Chapter 3,
Example 3.1, equation (3.20); that case is classical (Ando 1985; see Yamagami,
Proc. Amer. Math. Soc. 118 (1993), 521–527). -/
theorem perm_reciprocal_sum_le_one {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i / ((∑ j, x j) + x i - x (σ i)) ≤ 1 := by
  classical
  set T : ℝ := ∑ j, x j with hTdef
  rcases eq_or_lt_of_le (Finset.sum_nonneg fun j _ => hx j : (0 : ℝ) ≤ T)
    with hT | hTpos
  · have hx0 : ∀ i ∈ Finset.univ, x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hx j).1 hT.symm
    have hzero : ∀ i ∈ Finset.univ,
        x i / (T + x i - x (σ i)) = 0 := fun i hi => by
      rw [hx0 i hi, zero_div]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact zero_le_one
  · have key : ∀ i ∈ Finset.univ, x i / (T + x i - x (σ i)) ≤
        (x i * T - x i * (x i - x (σ i)) + (x i - x (σ i)) ^ 2 / 2) / T ^ 2 := by
      intro i _
      by_cases hfix : σ i = i
      · rw [hfix]
        have hT' : T + x i - x i = T := by ring
        have hnum : x i * T - x i * (x i - x i) + (x i - x i) ^ 2 / 2
            = T * x i := by ring
        rw [hT', hnum, pow_two, mul_div_mul_left _ _ (ne_of_gt hTpos)]
      · have hpair : x i + x (σ i) ≤ T := by
          have hsum := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ ({i, σ i} : Finset ι)) fun j _ _ => hx j
          rwa [Finset.sum_pair (Ne.symm hfix)] at hsum
        exact perm_reciprocal_term_le (hx i) hTpos hpair
    have hsq : ∑ i, x (σ i) ^ 2 = ∑ i, x i ^ 2 :=
      Equiv.sum_comp σ fun j => x j ^ 2
    have hkey : ∑ i, (x i - x (σ i)) ^ 2 =
        2 * ∑ i, x i * (x i - x (σ i)) := by
      have hcross : ∑ i, ((x i - x (σ i)) ^ 2 - 2 * (x i * (x i - x (σ i))))
          = ∑ i, (x (σ i) ^ 2 - x i ^ 2) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hcross
      rw [Finset.sum_sub_distrib, hsq, sub_self] at hcross
      linarith [hcross]
    have htotal : ∑ i,
        (x i * T - x i * (x i - x (σ i)) + (x i - x (σ i)) ^ 2 / 2) / T ^ 2
          = 1 := by
      rw [← Finset.sum_div]
      have hnum : ∑ i,
          (x i * T - x i * (x i - x (σ i)) + (x i - x (σ i)) ^ 2 / 2)
            = T ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ← Finset.sum_div, ← hTdef, hkey]
        ring
      rw [hnum, div_self (by positivity)]
    calc ∑ i, x i / (T + x i - x (σ i))
        ≤ ∑ i, (x i * T - x i * (x i - x (σ i)) + (x i - x (σ i)) ^ 2 / 2)
            / T ^ 2 := Finset.sum_le_sum key
      _ = 1 := htotal

/-- For `3 ≤ d`, the backward shifts by `1, …, d - 2` from `i` run over every
index of `ZMod d` except `i` itself and `i + 1`. -/
theorem sum_shift_window_eq_sub_pair (hd : 3 ≤ d) (x : ZMod d → ℝ)
    (i : ZMod d) :
    ∑ k : Fin (d - 2), x (i - ((k.1 + 1 : ℕ) : ZMod d)) =
      (∑ j, x j) - (x i + x (i + 1)) := by
  classical
  have hne : i ≠ i + 1 := by
    intro h
    have h1 : (0 : ZMod d) = 1 := by
      have := congrArg (fun t => t - i) h
      simpa using this
    rw [eq_comm, ZMod.one_eq_zero_iff] at h1
    omega
  have hmain : ∑ k : Fin (d - 2), x (i - ((k.1 + 1 : ℕ) : ZMod d)) =
      ∑ c ∈ Finset.univ \ ({i, i + 1} : Finset (ZMod d)), x c := by
    refine Finset.sum_bij' (fun k _ => i - ((k.1 + 1 : ℕ) : ZMod d))
      (fun c hc => ⟨(i - c).val - 1, ?_⟩) ?_ ?_ ?_ ?_ ?_
    · -- the inverse lands in `Fin (d - 2)`
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hc
      obtain ⟨-, hc2⟩ := hc
      have hci : c ≠ i := fun h => hc2 (Or.inl h)
      have hci1 : c ≠ i + 1 := fun h => hc2 (Or.inr h)
      have hval_ne_zero : (i - c).val ≠ 0 := by
        intro h0
        have hic : i - c = 0 := (ZMod.val_eq_zero _).1 h0
        exact hci (sub_eq_zero.1 hic).symm
      have hval_lt : (i - c).val < d := ZMod.val_lt _
      have hval_ne_top : (i - c).val ≠ d - 1 := by
        intro hval
        have hcast : ((i - c).val : ZMod d) = i - c :=
          ZMod.natCast_rightInverse (i - c)
        rw [hval] at hcast
        have hd1 : ((d - 1 : ℕ) : ZMod d) = -1 := by
          have h1d : 1 ≤ d := by omega
          push_cast [Nat.cast_sub h1d]
          simp
        rw [hd1] at hcast
        exact hci1 (by linear_combination hcast)
      omega
    · -- forward map lands in the complement of the pair
      intro k _
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      have hk : k.1 + 1 < d := by omega
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro (h | h)
      · have hzero : ((k.1 + 1 : ℕ) : ZMod d) = 0 := by
          have := congrArg (fun t => i - t) h
          simpa using this
        rw [ZMod.natCast_eq_zero_iff] at hzero
        have := Nat.le_of_dvd (by omega) hzero
        omega
      · have hzero : ((k.1 + 2 : ℕ) : ZMod d) = 0 := by
          have hstep : ((k.1 + 1 : ℕ) : ZMod d) = -1 := by
            linear_combination -h
          push_cast at hstep ⊢
          linear_combination hstep
        rw [ZMod.natCast_eq_zero_iff] at hzero
        have := Nat.le_of_dvd (by omega) hzero
        omega
    · -- the inverse lands in `Fin (d - 2)` membership (trivial)
      intro c _
      exact Finset.mem_univ _
    · -- left inverse
      intro k _
      have hk : k.1 + 1 < d := by omega
      apply Fin.ext
      simp only [sub_sub_cancel]
      rw [ZMod.val_cast_of_lt hk]
      omega
    · -- right inverse
      intro c hc
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hc
      obtain ⟨-, hc2⟩ := hc
      have hci : c ≠ i := fun h => hc2 (Or.inl h)
      have hval_ne_zero : (i - c).val ≠ 0 := by
        intro h0
        have hic : i - c = 0 := (ZMod.val_eq_zero _).1 h0
        exact hci (sub_eq_zero.1 hic).symm
      simp only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hval_ne_zero)]
      rw [ZMod.natCast_rightInverse (i - c), sub_sub_cancel]
    · -- summand values agree
      intro k _
      rfl
  rw [hmain, Finset.sum_sdiff_eq_sub (Finset.subset_univ _),
    Finset.sum_pair hne]

/-- **Wolf Chapter 3, Example 3.1, equation (3.20), case `n = d - 2`.**  The
Choi rank-one diagonal weight collapses to
\(a_i = T + |v_i|^2 - |v_{i+1}|^2\) with \(T=\sum_j |v_j|^2\). -/
theorem choiTypeRankOneWeight_sub_two (hd : 3 ≤ d) (v : ZMod d → ℂ)
    (i : ZMod d) :
    choiTypeRankOneWeight d (d - 2) v i =
      (∑ j, ‖v j‖ ^ 2) + ‖v i‖ ^ 2 - ‖v (i + 1)‖ ^ 2 := by
  have hcast : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    have h2 : 2 ≤ d := by omega
    push_cast [Nat.cast_sub h2]
    ring
  have hshift := sum_shift_window_eq_sub_pair hd (fun j => ‖v j‖ ^ 2) i
  simp only [choiTypeRankOneWeight, hcast]
  rw [hshift]
  ring

/-- Rank-one positivity at the top of Wolf's range: for `3 ≤ d` and
`n = d - 2`, the image \(T_C(|v\rangle\langle v|)\) is positive semidefinite
(Wolf Chapter 3, Example 3.1, equation (3.20)).  The scalar input is the
permutation reciprocal inequality applied to the cyclic shift. -/
theorem choiTypeMap_vecMulVec_posSemidef_sub_two (hd : 3 ≤ d)
    (v : ZMod d → ℂ) :
    (choiTypeMap d (d - 2) (vecMulVec v (star v))).PosSemidef := by
  refine choiTypeMap_vecMulVec_posSemidef_of_weight_sum_le_one
    (d - 2) v le_rfl ?_
  have hperm := perm_reciprocal_sum_le_one (Equiv.addRight (1 : ZMod d))
    (fun j => ‖v j‖ ^ 2) fun j => sq_nonneg _
  simp only [Equiv.coe_addRight] at hperm
  calc ∑ i, ‖v i‖ ^ 2 / choiTypeRankOneWeight d (d - 2) v i
      = ∑ i, ‖v i‖ ^ 2 /
          ((∑ j, ‖v j‖ ^ 2) + ‖v i‖ ^ 2 - ‖v (i + 1)‖ ^ 2) :=
        Finset.sum_congr rfl fun i _ => by
          rw [choiTypeRankOneWeight_sub_two hd]
    _ ≤ 1 := hperm

/-- **Wolf Chapter 3, Example 3.1, equation (3.20), case `n = d - 2`.**  The
Choi-type map at the top of Wolf's range is positive: for `3 ≤ d`, the map
\(T_C\) with `n = d - 2` sends every positive semidefinite matrix to a
positive semidefinite matrix.

**Scope restriction:** See
`docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`.  This proves
the case `n = d - 2` of the positivity assertion for every `d ≥ 3`, subsuming
the earlier \(d=3,n=1\) case.  The remaining range \(1\le n\le d-3\) is still
open; its classical proof is the variational argument of Yamagami
[Proc. Amer. Math. Soc. 118 (1993), 521–527]. -/
theorem choiTypeMap_isPositiveMap_sub_two (hd : 3 ≤ d) :
    IsPositiveMap (choiTypeMap d (d - 2)) :=
  isPositiveMap_of_forall_vecMulVec_posSemidef _ fun w =>
    choiTypeMap_vecMulVec_posSemidef_sub_two hd w


/-! ## The bottom of Wolf's range: `n = 1`

For `n = 1` the Choi rank-one diagonal weight collapses to
\(a_i = (d-1)x_i + x_{i-1}\) with \(x_i = |v_i|^2\), and the cyclic
reciprocal estimate \(\sum_i x_i/((d-1)x_i + x_{i-1}) \le 1\) holds for
every \(d \ge 2\).  In the interior (all \(x_i > 0\)), writing the
summand as \(1/(y_i + (d-1))\) with \(y_i = x_{i-1}/x_i\) gives
\(\prod_i y_i = 1\); clearing denominators yields a polynomial inequality
whose expansion in elementary symmetric polynomials \(e_k\) of the \(y\)'s
is \(\sum_k (k-1)(d-1)^{d-1-k} e_k \ge 0\).  That estimate follows from
the AM–GM bound \(e_k \ge \binom{d}{k}\) (the product of all
\(k\)-subset monomials is \((\prod_i y_i)^{\binom{d-1}{k-1}} = 1\)) and
the binomial identity \(\sum_k (k-1)(d-1)^{d-k}\binom{d}{k} = 0\).  If
some coordinate vanishes, at most \(d-1\) summands are nonzero and each is at
most \(1/(d-1)\), which proves the boundary case directly.

This is the case \(n = 1\) of the positivity assertion of Wolf Chapter 3,
Example 3.1, equation (3.20) (ch03 lines 357–365); that case is classical
(Tanahashi–Tomiyama, *Indecomposable positive maps in matrix algebras*,
Canad. Math. Bull. 31 (1988), 308–317).  The proof here is the
elementary-symmetric expansion sketched above, not the variational argument
of Yamagami needed for the middle of the range. -/

/-- Each variable appears in the same number of `k`-subsets of the index
type, so the product of all `k`-subset monomials of a product-one family is
one: it is a power of the total product.  This is the geometric-mean
computation behind the AM–GM bound on the elementary symmetric sums. -/
private theorem prod_powersetCard_prod_eq_one {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (hprod : ∏ i, y i = 1) {k : ℕ} :
    ∏ t ∈ Finset.powersetCard k Finset.univ, ∏ j ∈ t, y j = 1 := by
  classical
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [Finset.powersetCard_zero]
  have hmem : ∀ t ∈ Finset.powersetCard k (Finset.univ : Finset ι),
      ∏ j ∈ t, y j = ∏ j ∈ Finset.univ, if j ∈ t then y j else 1 := by
    intro t ht
    rw [Finset.mem_powersetCard] at ht
    have h2 : ∏ j ∈ t, (if j ∈ t then y j else 1) =
        ∏ j ∈ Finset.univ, if j ∈ t then y j else 1 :=
      Finset.prod_subset ht.1 fun j _ hj => by simp [hj]
    rw [← h2]
    exact Finset.prod_congr rfl fun j hj => by simp [hj]
  rw [Finset.prod_congr rfl hmem, Finset.prod_comm]
  -- The fiber of `k`-subsets containing `j` is in bijection with the
  -- `(k - 1)`-subsets of the remaining indices, via erasing `j`.
  have hfiber : ∀ j : ι, ∏ t ∈ Finset.powersetCard k Finset.univ,
        (if j ∈ t then y j else 1) =
      y j ^ ((Fintype.card ι - 1).choose (k - 1)) := by
    intro j
    rw [← Finset.prod_filter, Finset.prod_const]
    congr 1
    have hbij : ((Finset.powersetCard k Finset.univ).filter fun t => j ∈ t).card =
        (Finset.powersetCard (k - 1) (Finset.univ.erase j)).card := by
      refine Finset.card_bij (fun t _ => t.erase j) ?_ ?_ ?_
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_powersetCard] at ht
        obtain ⟨⟨htsub, htc⟩, hjt⟩ := ht
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.erase_subset_erase j htsub,
          by rw [Finset.card_erase_of_mem hjt, htc]⟩
      · intro t₁ ht₁ t₂ ht₂ h
        rw [Finset.mem_filter] at ht₁ ht₂
        have h₁ := Finset.insert_erase ht₁.2
        have h₂ := Finset.insert_erase ht₂.2
        rw [← h₁, h]
        exact h₂
      · intro u hu
        rw [Finset.mem_powersetCard] at hu
        obtain ⟨husub, huc⟩ := hu
        have hju : j ∉ u := fun h => (Finset.mem_erase.1 (husub h)).1 rfl
        refine ⟨insert j u, ?_, Finset.erase_insert hju⟩
        rw [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self j u⟩
        · exact Finset.insert_subset (Finset.mem_univ j) (Finset.subset_univ u)
        · rw [Finset.card_insert_of_notMem hju, huc]
          omega
    rw [hbij, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ]
  rw [Finset.prod_congr rfl fun j _ => hfiber j, Finset.prod_pow, hprod, one_pow]

/-- **AM–GM bound on the elementary symmetric sums.**  For a positive
product-one family, each elementary symmetric sum is bounded below by the
corresponding binomial coefficient: the `k`-subset monomials have geometric
mean `1` by `prod_powersetCard_prod_eq_one`, and there are
`Nat.choose d k` of them. -/
private theorem card_choose_le_sum_powersetCard_prod {ι : Type*} [Fintype ι]
    (y : ι → ℝ) (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = 1) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    (Nat.choose (Fintype.card ι) k : ℝ) ≤
      ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ j ∈ t, y j := by
  classical
  set s := Finset.powersetCard k (Finset.univ : Finset ι) with hs_def
  have hcard : s.card = Nat.choose (Fintype.card ι) k := by
    rw [hs_def, Finset.card_powersetCard, Finset.card_univ]
  have hmpos : 0 < s.card := hcard.symm ▸ Nat.choose_pos hk
  have hnonneg : ∀ t : ↥s, 0 ≤ ∏ j ∈ t.1, y j :=
    fun t => Finset.prod_nonneg fun j _ => (hy j).le
  have hamgm := pow_card_mul_prod_le_sum_pow' (fun t : ↥s => ∏ j ∈ t.1, y j) hnonneg
  simp only [Fintype.card_coe, Finset.univ_eq_attach] at hamgm
  rw [Finset.prod_attach s (fun t => ∏ j ∈ t, y j),
    Finset.sum_attach s (fun t => ∏ j ∈ t, y j),
    prod_powersetCard_prod_eq_one y hprod, mul_one] at hamgm
  have heR : (0 : ℝ) ≤ ∑ t ∈ s, ∏ j ∈ t, y j :=
    Finset.sum_nonneg fun t _ => Finset.prod_nonneg fun j _ => (hy j).le
  have hle : ((s.card : ℝ)) ≤ ∑ t ∈ s, ∏ j ∈ t, y j :=
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) heR hmpos.ne').mp hamgm
  rwa [hcard] at hle

/-- **Master expansion.**  With `s = d - 1` (as a real) and `d` the
cardinality of the index type, the difference of the full product and the sum
of the erased products, scaled by `s`, expands as the signed subset sum
`∑ t, (|t| - 1) s ^ (d - |t|) y^t`: the `t`-coefficient is
`s ^ (d - |t|) - (d - |t|) s ^ (d - 1 - |t|) = (|t| - 1) s ^ (d - |t|)`,
using `s = d - 1`. -/
private theorem mul_prod_add_sub_sum_prod_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) :
    ((Fintype.card ι : ℝ) - 1) *
        (∏ i, (y i + ((Fintype.card ι : ℝ) - 1)) -
          ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + ((Fintype.card ι : ℝ) - 1))) =
      ∑ t ∈ Finset.univ.powerset,
        ((t.card : ℝ) - 1) * ((Fintype.card ι : ℝ) - 1) ^ (Fintype.card ι - t.card) *
          ∏ j ∈ t, y j := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set s : ℝ := (d : ℝ) - 1 with hs
  -- Expansion of the full product over the powerset.
  have hP : ∏ i, (y i + s) =
      ∑ t ∈ Finset.univ.powerset, (∏ j ∈ t, y j) * s ^ (d - t.card) := by
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_powerset] at ht
    rw [Finset.prod_const, Finset.card_sdiff_of_subset ht, Finset.card_univ, ← hd]
  -- Expansion of one erased product over the powerset of the erased index set.
  have hQ : ∀ i : ι, ∏ j ∈ Finset.univ.erase i, (y j + s) =
      ∑ t ∈ (Finset.univ.erase i).powerset, (∏ j ∈ t, y j) * s ^ (d - 1 - t.card) := by
    intro i
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_powerset] at ht
    rw [Finset.prod_const, Finset.card_sdiff_of_subset ht, Finset.card_erase_of_mem
      (Finset.mem_univ i), Finset.card_univ, ← hd]
  -- The erased powersets are the fibers of the full powerset.
  have hps : ∀ i : ι, (Finset.univ.erase i : Finset ι).powerset =
      Finset.univ.powerset.filter fun t => i ∉ t := by
    intro i
    ext t
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨Subset.trans h (Finset.erase_subset _ _), (Finset.subset_erase.1 h).2⟩
    · intro h
      exact Finset.subset_erase.2 ⟨Finset.subset_univ t, h.2⟩
  -- Summing the erased expansions over `i` double-counts each subset by its
  -- complement cardinality.
  have hsum : ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + s) =
      ∑ t ∈ Finset.univ.powerset,
        (((d - t.card : ℕ) : ℝ)) * ((∏ j ∈ t, y j) * s ^ (d - 1 - t.card)) := by
    have step : ∀ i : ι, ∑ t ∈ (Finset.univ.erase i).powerset,
          (∏ j ∈ t, y j) * s ^ (d - 1 - t.card) =
        ∑ t ∈ Finset.univ.powerset,
          (if i ∉ t then (∏ j ∈ t, y j) * s ^ (d - 1 - t.card) else 0) := by
      intro i
      rw [hps i, Finset.sum_filter]
    rw [Finset.sum_congr rfl (fun i _ => hQ i),
      Finset.sum_congr rfl (fun i _ => step i), Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.sum_filter]
    have hfilter : Finset.univ.filter (fun i => i ∉ t) = Finset.univ \ t := by
      ext i
      simp
    rw [hfilter, Finset.sum_const, nsmul_eq_mul,
      Finset.card_sdiff_of_subset (Finset.subset_univ t), Finset.card_univ, ← hd]
  -- Combine and compare subset by subset.
  rw [hP, hsum, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_powerset] at ht
  have htc : t.card ≤ d := by
    have h1 := Finset.card_le_card ht
    rwa [Finset.card_univ, ← hd] at h1
  rcases Nat.eq_or_lt_of_le htc with hteq | htlt
  · have htuniv : t = Finset.univ := by
      have h1 : t.card = (Finset.univ : Finset ι).card := by
        rwa [Finset.card_univ, ← hd]
      exact Finset.eq_univ_of_card t h1
    subst htuniv
    simp [hs, hd]
  · have hexp : d - t.card = (d - 1 - t.card) + 1 := by omega
    have hpow : s ^ (d - t.card) = s ^ (d - 1 - t.card) * s := by
      rw [hexp, pow_succ]
    have hcast : (((d - t.card : ℕ)) : ℝ) = (d : ℝ) - t.card := by
      rw [Nat.cast_sub (le_of_lt htlt)]
    rw [hpow, hcast, hs]
    ring

/-- The powerset sum of the signed monomial terms groups by subset
cardinality into the elementary symmetric sums. -/
private theorem sum_powerset_signed_monomial_eq_sum_range {ι : Type*} [Fintype ι]
    (y : ι → ℝ) :
    ∑ t ∈ Finset.univ.powerset,
        ((t.card : ℝ) - 1) * ((Fintype.card ι : ℝ) - 1) ^ (Fintype.card ι - t.card) *
          ∏ j ∈ t, y j =
      ∑ k ∈ Finset.range (Fintype.card ι + 1),
        ((k : ℝ) - 1) * ((Fintype.card ι : ℝ) - 1) ^ (Fintype.card ι - k) *
          ∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set s : ℝ := (d : ℝ) - 1 with hs
  have hmaps : ∀ t ∈ (Finset.univ : Finset ι).powerset, t.card ∈ Finset.range (d + 1) := by
    intro t ht
    rw [Finset.mem_range]
    have h1 := Finset.card_le_card (Finset.mem_powerset.1 ht)
    rw [Finset.card_univ, ← hd] at h1
    omega
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι).powerset)
    (t := Finset.range (d + 1)) (g := fun t : Finset ι => t.card) hmaps]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.powersetCard_eq_filter]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht2 : t.card = k := (Finset.mem_powersetCard.1 ht).2
  rw [ht2]

/-- **Polynomial form of the product-one reciprocal bound** (interior of the
Tanahashi–Tomiyama slice).  For `d ≥ 2` and strictly positive `y` with
product one, the sum of the erased products is at most the full product:
scaled by `s = d - 1`, the difference expands as
`∑_k (k-1) s ^ (d-k) e_k`, which is `≥ -s ^ d + ∑_k (k-1) s ^ (d-k)
Nat.choose d k = 0` by the AM–GM bound
`card_choose_le_sum_powersetCard_prod` and the binomial identity obtained by
evaluating the same expansion at `y ≡ 1`. -/
private theorem sum_prod_erase_le_prod_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hd2 : 2 ≤ Fintype.card ι) (y : ι → ℝ) (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = 1) :
    ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + ((Fintype.card ι : ℝ) - 1)) ≤
      ∏ i, (y i + ((Fintype.card ι : ℝ) - 1)) := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set s : ℝ := (d : ℝ) - 1 with hs
  have hs_pos : 0 < s := by
    rw [hs]
    have h2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    linarith
  have hsplit : ∀ (g : ℕ → ℝ), ∑ k ∈ Finset.range (d + 1), g k =
      (∑ k ∈ Finset.range 2, g k) + ∑ k ∈ Finset.Ico 2 (d + 1), g k := by
    intro g
    exact (Finset.sum_range_add_sum_Ico g (by omega : (2 : ℕ) ≤ d + 1)).symm
  have hpair : ∀ (g : ℕ → ℝ), ∑ k ∈ Finset.range 2, g k = g 0 + g 1 := by
    intro g
    rw [show Finset.range 2 = {0, 1} from by ext k; simp; omega,
      Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  -- The binomial-coefficient identity, from the master expansion at `y ≡ 1`.
  have hD : ∑ k ∈ Finset.range (d + 1),
      ((k : ℝ) - 1) * s ^ (d - k) * (Nat.choose d k : ℝ) = 0 := by
    have hB := mul_prod_add_sub_sum_prod_erase (fun _ : ι => (1 : ℝ))
    have hC := sum_powerset_signed_monomial_eq_sum_range (fun _ : ι => (1 : ℝ))
    have hBC : s * (∏ _i, ((1 : ℝ) + s) - ∑ i, ∏ _j ∈ Finset.univ.erase i, ((1 : ℝ) + s)) =
        ∑ k ∈ Finset.range (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
          ∑ t ∈ (Finset.univ : Finset ι).powersetCard k, ∏ _j ∈ t, (1 : ℝ) :=
      hB.trans hC
    have he1 : ∀ k : ℕ,
        (∑ t ∈ (Finset.univ : Finset ι).powersetCard k, ∏ _j ∈ t, (1 : ℝ)) =
        (Nat.choose d k : ℝ) := by
      intro k
      simp only [Finset.prod_const_one, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_powersetCard, Finset.card_univ, ← hd]
    have hP1 : ∏ _i : ι, ((1 : ℝ) + s) = (1 + s) ^ d := by
      rw [Finset.prod_const, Finset.card_univ, ← hd]
    have hQ1 : ∀ i : ι, ∏ _j ∈ Finset.univ.erase i, ((1 : ℝ) + s) = (1 + s) ^ (d - 1) := by
      intro i
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, ← hd]
    rw [hP1, Finset.sum_congr rfl (fun i _ => hQ1 i), Finset.sum_const, Finset.card_univ,
      ← hd, nsmul_eq_mul] at hBC
    have hzero : (1 + s) ^ d - (d : ℝ) * (1 + s) ^ (d - 1) = 0 := by
      have h1s : (1 : ℝ) + s = d := by rw [hs]; ring
      have hpow : (1 + s) ^ d = (1 + s) ^ (d - 1) * (1 + s) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpow, h1s]
      ring
    rw [hzero, mul_zero] at hBC
    simp only [he1] at hBC
    exact hBC.symm
  -- The master expansion, grouped, with the `k = 0, 1` slices peeled off.
  have hBy := mul_prod_add_sub_sum_prod_erase y
  have hCy := sum_powerset_signed_monomial_eq_sum_range y
  have hBC : s * (∏ i, (y i + s) - ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + s)) =
      ∑ k ∈ Finset.range (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        ∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j :=
    hBy.trans hCy
  have hrange : (∑ k ∈ Finset.range (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j)) =
      -s ^ d + ∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j) := by
    rw [hsplit, hpair]
    have h0 : (((0 : ℕ) : ℝ) - 1) * s ^ (d - 0) *
        (∑ t ∈ Finset.univ.powersetCard 0, ∏ j ∈ t, y j) = -s ^ d := by
      simp
    have h1 : (((1 : ℕ) : ℝ) - 1) * s ^ (d - 1) *
        (∑ t ∈ Finset.univ.powersetCard 1, ∏ j ∈ t, y j) = 0 := by
      simp
    rw [h0, h1, add_zero]
  have hrangeC : (∑ k ∈ Finset.range (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (Nat.choose d k : ℝ)) =
      -s ^ d + ∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (Nat.choose d k : ℝ) := by
    rw [hsplit, hpair]
    have h0 : (((0 : ℕ) : ℝ) - 1) * s ^ (d - 0) * (Nat.choose d 0 : ℝ) = -s ^ d := by
      simp
    have h1 : (((1 : ℕ) : ℝ) - 1) * s ^ (d - 1) * (Nat.choose d 1 : ℝ) = 0 := by
      simp
    rw [h0, h1, add_zero]
  have hXC : (∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (Nat.choose d k : ℝ)) = s ^ d := by
    linarith [hD, hrangeC]
  have hAmgm : (∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (Nat.choose d k : ℝ)) ≤
      ∑ k ∈ Finset.Ico 2 (d + 1), ((k : ℝ) - 1) * s ^ (d - k) *
        (∑ t ∈ Finset.univ.powersetCard k, ∏ j ∈ t, y j) := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : 2 ≤ k := (Finset.mem_Ico.1 hk).1
    have hkd : k ≤ d := by
      have h2 := (Finset.mem_Ico.1 hk).2
      omega
    have hcoeff : (0 : ℝ) ≤ ((k : ℝ) - 1) * s ^ (d - k) := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
      exact mul_nonneg (by linarith) (pow_nonneg hs_pos.le _)
    exact mul_le_mul_of_nonneg_left
      (card_choose_le_sum_powersetCard_prod y hy hprod (hd ▸ hkd)) hcoeff
  have key : 0 ≤ s * (∏ i, (y i + s) - ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + s)) := by
    rw [hBC, hrange]
    linarith [hXC ▸ hAmgm]
  have hmain : 0 ≤ ∏ i, (y i + s) - ∑ i, ∏ j ∈ Finset.univ.erase i, (y j + s) :=
    nonneg_of_mul_nonneg_left (by rwa [mul_comm] at key) hs_pos
  exact sub_nonneg.mp hmain

/-- **Reciprocal sum bound for product-one families** (interior of the
Tanahashi–Tomiyama slice, reciprocal form).  For `d ≥ 2` and strictly
positive `y` with `∏ y_i = 1`, `∑ i, 1 / (y_i + (d - 1)) ≤ 1`. -/
private theorem sum_inv_add_card_sub_one_le_one {ι : Type*} [Fintype ι]
    (hd2 : 2 ≤ Fintype.card ι) (y : ι → ℝ) (hy : ∀ i, 0 < y i) (hprod : ∏ i, y i = 1) :
    ∑ i, 1 / (y i + ((Fintype.card ι : ℝ) - 1)) ≤ 1 := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set s : ℝ := (d : ℝ) - 1 with hs
  have hs_pos : 0 < s := by
    rw [hs]
    have h2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
    linarith
  have hD : ∀ i : ι, 0 < y i + s := fun i => add_pos (hy i) hs_pos
  have hP : 0 < ∏ i, (y i + s) := Finset.prod_pos (fun i _ => hD i)
  have hEpoly := sum_prod_erase_le_prod_add hd2 y hy hprod
  have hdiv : ∀ i : ι, 1 / (y i + s) =
      (∏ j ∈ Finset.univ.erase i, (y j + s)) / ∏ j, (y j + s) := by
    intro i
    have h1 : y i + s ≠ 0 := (hD i).ne'
    have h2 : (∏ j ∈ Finset.univ.erase i, (y j + s)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j _ => (hD j).ne'
    rw [← Finset.mul_prod_erase Finset.univ (fun j => y j + s) (Finset.mem_univ i)]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => hdiv i, ← Finset.sum_div]
  exact (div_le_one hP).2 hEpoly

/-- Interior of the first cyclic reciprocal estimate: for `d ≥ 2` and
strictly positive `x` on `ZMod d`,
`∑ i, x i / ((d - 1) * x i + x (i - 1)) ≤ 1`.  With `y_i = x_{i-1} / x_i`
the product of the `y`'s telescopes to `1` by cyclic shift invariance, and
the summand becomes `1 / (y_i + (d - 1))`, so the claim reduces to the
product-one reciprocal bound. -/
theorem choiType_cyclic_reciprocal_one_of_pos (hd : 2 ≤ d) (x : ZMod d → ℝ)
    (hx : ∀ i, 0 < x i) :
    ∑ i, x i / (((d : ℝ) - 1) * x i + x (i - 1)) ≤ 1 := by
  classical
  set y : ZMod d → ℝ := fun i => x (i - 1) / x i with hy_def
  have hy : ∀ i, 0 < y i := fun i => div_pos (hx _) (hx _)
  have hprod : ∏ i, y i = 1 := by
    have hshift : ∏ i, x (i - 1) = ∏ i, x i :=
      Equiv.prod_comp (Equiv.subRight (1 : ZMod d)) x
    rw [hy_def, Finset.prod_div_distrib, hshift,
      div_self (Finset.prod_pos (fun i _ => hx i)).ne']
  have hcard : Fintype.card (ZMod d) = d := ZMod.card d
  have hrecip := sum_inv_add_card_sub_one_le_one (ι := ZMod d) (by rwa [hcard]) y hy hprod
  rw [hcard] at hrecip
  refine le_trans (Finset.sum_le_sum fun i _ => le_of_eq ?_) hrecip
  have hxi : x i ≠ 0 := (hx i).ne'
  have hyi : y i = x (i - 1) / x i := rfl
  have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
    have h2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hDpos : (((d : ℝ) - 1) * x i + x (i - 1)) ≠ 0 :=
    (add_pos (mul_pos hd1 (hx i)) (hx _)).ne'
  have hEpos : (x (i - 1) / x i + ((d : ℝ) - 1)) ≠ 0 :=
    (add_pos (div_pos (hx _) (hx _)) hd1).ne'
  rw [hyi]
  field_simp
  ring

/-- **The first cyclic reciprocal estimate, including boundary points.**  For
`d ≥ 2` and nonnegative `x` on `ZMod d`,
`∑ i, x i / ((d - 1) * x i + x (i - 1)) ≤ 1`.

In the interior this is `choiType_cyclic_reciprocal_one_of_pos`.  If some
coordinate vanishes, only at most `d - 1` summands are nonzero, and each is at
most `1 / (d - 1)`.

This is the scalar inequality for the case `n = 1` of Wolf Chapter 3,
Example 3.1, equation (3.20) (ch03 lines 357–365).

**Scope restriction:** See
`docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`.  The theorem
covers the full bottom slice `n = 1`, not the middle range `2 ≤ n ≤ d - 3`. -/
theorem choiType_cyclic_reciprocal_one_of_nonneg (hd : 2 ≤ d) (x : ZMod d → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i / (((d : ℝ) - 1) * x i + x (i - 1)) ≤ 1 := by
  classical
  by_cases hpos : ∀ i, 0 < x i
  · exact choiType_cyclic_reciprocal_one_of_pos hd x hpos
  · push Not at hpos
    obtain ⟨i₀, hi₀⟩ := hpos
    have hxi₀ : x i₀ = 0 := le_antisymm hi₀ (hx i₀)
    let s : Finset (ZMod d) := Finset.univ.filter fun i => x i ≠ 0
    have hslt : s.card < d := by
      calc
        s.card < (Finset.univ : Finset (ZMod d)).card :=
          Finset.card_lt_card
            (Finset.filter_ssubset.2 ⟨i₀, Finset.mem_univ _, fun h => h hxi₀⟩)
        _ = d := ZMod.card d
    have hscard : s.card ≤ d - 1 := by omega
    have hd1pos : (0 : ℝ) < (d : ℝ) - 1 := by
      have h2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      linarith
    have hterm : ∀ i ∈ s,
        x i / (((d : ℝ) - 1) * x i + x (i - 1)) ≤ 1 / ((d : ℝ) - 1) := by
      intro i hi
      have hxi : 0 < x i := lt_of_le_of_ne (hx i) (Finset.mem_filter.1 hi).2.symm
      have hden : 0 < ((d : ℝ) - 1) * x i + x (i - 1) :=
        add_pos_of_pos_of_nonneg (mul_pos hd1pos hxi) (hx _)
      rw [div_le_div_iff₀ hden hd1pos]
      nlinarith [hx (i - 1)]
    calc
      ∑ i, x i / (((d : ℝ) - 1) * x i + x (i - 1)) =
          ∑ i ∈ s, x i / (((d : ℝ) - 1) * x i + x (i - 1)) := by
            rw [Finset.sum_subset (Finset.subset_univ s)]
            intro i _ hi
            simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hi
            have hzero : x i = 0 := not_ne_iff.mp hi
            simp [hzero]
      _ ≤ ∑ _i ∈ s, 1 / ((d : ℝ) - 1) := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) / ((d : ℝ) - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ((d : ℝ) - 1) / ((d : ℝ) - 1) := by
        rw [div_le_div_iff_of_pos_right hd1pos]
        have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
          norm_num [Nat.cast_sub (by omega : 1 ≤ d)]
        rw [← hcast]
        exact_mod_cast hscard
      _ = 1 := div_self hd1pos.ne'

/-- **Wolf Chapter 3, Example 3.1, equation (3.20), case `n = 1`.**  The
rank-one diagonal weight is
\(a_i=(d-1)|v_i|^2+|v_{i-1}|^2\). -/
theorem choiTypeRankOneWeight_one (v : ZMod d → ℂ) (i : ZMod d) :
    choiTypeRankOneWeight d 1 v i =
      ((d : ℝ) - 1) * ‖v i‖ ^ 2 + ‖v (i - 1)‖ ^ 2 := by
  simp [choiTypeRankOneWeight]

/-- The reciprocal sum of the rank-one diagonal weights is at most one for
the bottom slice `n = 1` of Wolf's range. -/
theorem choiTypeRankOneWeight_reciprocal_sum_one (hd : 2 ≤ d) (v : ZMod d → ℂ) :
    ∑ i, ‖v i‖ ^ 2 / choiTypeRankOneWeight d 1 v i ≤ 1 := by
  simp_rw [choiTypeRankOneWeight_one]
  exact choiType_cyclic_reciprocal_one_of_nonneg hd (fun i => ‖v i‖ ^ 2)
    fun i => sq_nonneg _

/-- Rank-one positivity for the Choi-type map at the bottom of Wolf's range:
for `3 ≤ d`, the image \(T_C(|v\rangle\langle v|)\) with `n = 1` is
positive semidefinite (Wolf Chapter 3, Example 3.1, equation (3.20), ch03
lines 357–365). -/
theorem choiTypeMap_vecMulVec_posSemidef_one (hd : 3 ≤ d) (v : ZMod d → ℂ) :
    (choiTypeMap d 1 (vecMulVec v (star v))).PosSemidef := by
  refine choiTypeMap_vecMulVec_posSemidef_of_weight_sum_le_one 1 v (by omega) ?_
  exact choiTypeRankOneWeight_reciprocal_sum_one (by omega) v

/-- **Wolf Chapter 3, Example 3.1, equation (3.20), case `n = 1`.**  For
`3 ≤ d`, the first Choi-type map sends every positive semidefinite matrix to a
positive semidefinite matrix.

**Scope restriction:** See
`docs/paper-gaps/wolf_ex3_1_choi_positivity_subcase_scope.tex`.  This proves
the complete bottom slice `n = 1` of Wolf's positivity assertion, including
boundary vectors.  The middle range `2 ≤ n ≤ d - 3` remains open. -/
theorem choiTypeMap_isPositiveMap_one (hd : 3 ≤ d) :
    IsPositiveMap (choiTypeMap d 1) :=
  isPositiveMap_of_forall_vecMulVec_posSemidef _ fun v =>
    choiTypeMap_vecMulVec_posSemidef_one hd v

end Matrix
