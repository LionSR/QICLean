/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PerronFrobenius.RankOne
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Primitive matrices with stationary powers

This module proves a finite-dimensional Perron--Frobenius lemma for a primitive
nonnegative real matrix whose second and third powers agree. Its square is a
strictly positive idempotent, and the fixed space of such an idempotent is
one-dimensional. Consequently the square has rank one.

The results support the rank-one trace factorization sought at
arXiv:1606.00608, Appendix C.2, line 1613.  In addition to the rank statement,
the square is factored as $a b^{\mathsf T}$ for real vectors satisfying
$a \mathbin{\cdot} b=1$.  These are source-independent matrix lemmas, not
statements asserted in that paper: applying them to the sector trace matrix
still requires a separate, non-circular proof of primitivity.

## Main results

* `Matrix.IsIrreducible.isPrimitive_of_pow_two_diagonal_pos_of_pow_three_diagonal_pos`: primitivity
  from returns of lengths two and three.
* `Matrix.IsIrreducible.pow_two_pos_of_pow_two_support_eq_pow_three_support`: stabilization of the
  positive support of matrix powers.
-/

section Idempotent

open scoped BigOperators Matrix

namespace Matrix

variable {n : Type*} [Fintype n]

/-- A strictly positive idempotent real matrix on a nonempty finite index set
has rank one. -/
theorem rank_eq_one_of_pos_of_mul_self_eq_self [Nonempty n]
    {P : Matrix n n ℝ} (hP : ∀ i j, 0 < P i j) (hidem : P * P = P) :
    P.rank = 1 := by
  classical
  let f : (n → ℝ) →ₗ[ℝ] (n → ℝ) := Matrix.toLin' P
  let u : n → ℝ := f 1
  have hu_pos (i : n) : 0 < u i := by
    simp only [u, f, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.one_apply,
      mul_one]
    exact Finset.sum_pos (fun j _ ↦ hP i j) Finset.univ_nonempty
  have hf : f ∘ₗ f = f := by
    change Matrix.toLin' P ∘ₗ Matrix.toLin' P = Matrix.toLin' P
    rw [← Matrix.toLin'_mul, hidem]
  have hu_fix : f u = u := by
    simpa only [u, LinearMap.comp_apply] using LinearMap.congr_fun hf 1
  have hfixed (x : n → ℝ) (hx : f x = x) : ∃ c : ℝ, c • u = x := by
    obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ
      (fun i ↦ x i / u i) Finset.univ_nonempty
    let c : ℝ := x k / u k
    let y : n → ℝ := c • u - x
    have hy_nonneg (i : n) : 0 ≤ y i := by
      have hratio : x i / u i ≤ c := hk i (Finset.mem_univ i)
      have hxi : x i ≤ c * u i := (div_le_iff₀ (hu_pos i)).mp hratio
      exact sub_nonneg.mpr hxi
    have hyk : y k = 0 := by
      simp only [y, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, c]
      rw [div_mul_cancel₀ (x k) (ne_of_gt (hu_pos k)), sub_self]
    have hy_fix : f y = y := by
      simp only [y, map_sub, map_smul, hu_fix, hx]
    have hsum : ∑ j, P k j * y j = 0 := by
      have hky := congrFun hy_fix k
      rw [hyk] at hky
      simpa only [f, Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hky
    have hy_zero : y = 0 := by
      funext i
      have hterm : P k i * y i = 0 := congrFun
        ((Fintype.sum_eq_zero_iff_of_nonneg fun j ↦
          mul_nonneg (hP k j).le (hy_nonneg j)).mp hsum) i
      exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hP k i))
    refine ⟨c, sub_eq_zero.mp ?_⟩
    simpa only [y] using hy_zero
  have hu_mem : u ∈ LinearMap.range f := ⟨1, rfl⟩
  have hu_ne : u ≠ 0 := by
    intro hu
    have := hu_pos (Classical.choice inferInstance)
    rw [hu, Pi.zero_apply] at this
    exact lt_irrefl 0 this
  have hrank_le : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    refine finrank_le_one ⟨u, hu_mem⟩ fun x ↦ ?_
    rcases x.property with ⟨z, hz⟩
    have hx : f x.1 = x.1 := by
      rw [← hz]
      exact LinearMap.congr_fun hf z
    obtain ⟨c, hc⟩ := hfixed x.1 hx
    refine ⟨c, Subtype.ext ?_⟩
    exact hc
  have hrank_pos : 0 < Module.finrank ℝ (LinearMap.range f) := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨u, hu_mem⟩, ?_⟩
    intro hzero
    apply hu_ne
    exact congrArg Subtype.val hzero
  have hrange : Module.finrank ℝ (LinearMap.range f) = 1 := by omega
  rw [Matrix.rank_eq_finrank_range_toLin P (Pi.basisFun ℝ n) (Pi.basisFun ℝ n),
    Matrix.toLin_eq_toLin']
  simpa only [f] using hrange

/-- Multiplication by a positive scalar preserves primitivity. -/
theorem IsPrimitive.smul_of_pos [DecidableEq n]
    {T : Matrix n n ℝ} (hT : T.IsPrimitive)
    {c : ℝ} (hc : 0 < c) : (c • T).IsPrimitive := by
  obtain ⟨m, hm, hpos⟩ := hT.exists_pos_pow
  refine ⟨fun i j ↦ mul_nonneg hc.le (hT.nonneg i j), m, hm, ?_⟩
  intro i j
  rw [smul_pow, Matrix.smul_apply]
  exact mul_pos (pow_pos hc m) (hpos i j)

/-- If a primitive real matrix has equal second and third powers, then its
square is strictly positive entrywise. -/
theorem IsPrimitive.pow_two_pos_of_pow_two_eq_pow_three
    [DecidableEq n] [Nonempty n] {T : Matrix n n ℝ}
    (hT : T.IsPrimitive) (h : T ^ 2 = T ^ 3) (i j : n) :
    0 < (T ^ 2) i j := by
  obtain ⟨m, _, hpos⟩ := hT.exists_pos_pow
  have htwom_pos : 0 < (T ^ (m + m)) i j := by
    rw [pow_add, Matrix.mul_apply]
    exact Finset.sum_pos (fun k _ ↦ mul_pos (hpos i k) (hpos k j))
      Finset.univ_nonempty
  rw [← pow_eq_pow_two_of_pow_two_eq_pow_three h (m + m) (by omega)]
  exact htwom_pos

/-- If a primitive nonnegative real matrix has equal second and third powers,
then its square has rank one.

This is the finite-dimensional Perron-projection lemma supporting the proposed
argument at arXiv:1606.00608, Appendix C.2, line 1613; it is not itself a
claim of that source. Nonemptiness of the finite index type is necessary:
primitivity is vacuous for the empty matrix, whose square has rank zero. -/
theorem IsPrimitive.rank_pow_two_eq_one_of_pow_two_eq_pow_three
    [DecidableEq n] [Nonempty n] {T : Matrix n n ℝ}
    (hT : T.IsPrimitive) (h : T ^ 2 = T ^ 3) :
    (T ^ 2).rank = 1 := by
  have hsq_idem : T ^ 2 * T ^ 2 = T ^ 2 := by
    rw [← pow_add]
    exact pow_eq_pow_two_of_pow_two_eq_pow_three h 4 (by omega)
  exact rank_eq_one_of_pos_of_mul_self_eq_self
    (hT.pow_two_pos_of_pow_two_eq_pow_three h) hsq_idem

/-- If a primitive nonnegative real matrix has equal second and third powers,
then its square has the form $a b^{\mathsf T}$ for real vectors satisfying
$a \mathbin{\cdot} b=1$.

This is the normalized factorization needed for the corrected two-step
coefficient in arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines
1606--1616.  It factors `T ^ 2`, not the one-step matrix `T` printed at
line 1613. -/
theorem IsPrimitive.exists_pow_two_eq_vecMulVec_of_pow_two_eq_pow_three
    [DecidableEq n] [Nonempty n] {T : Matrix n n ℝ}
    (hT : T.IsPrimitive) (h : T ^ 2 = T ^ 3) :
    ∃ a b : n → ℝ, T ^ 2 = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 := by
  have hsq_idem : T ^ 2 * T ^ 2 = T ^ 2 := by
    rw [← pow_add]
    exact pow_eq_pow_two_of_pow_two_eq_pow_three h 4 (by omega)
  have hrank := hT.rank_pow_two_eq_one_of_pow_two_eq_pow_three h
  let f : (n → ℝ) →ₗ[ℝ] (n → ℝ) := Matrix.toLin' (T ^ 2)
  have hf : IsIdempotentElem f := by
    change Matrix.toLin' (T ^ 2) ∘ₗ Matrix.toLin' (T ^ 2) = Matrix.toLin' (T ^ 2)
    rw [← Matrix.toLin'_mul, hsq_idem]
  have hrange : Module.finrank ℝ (LinearMap.range f) = 1 := by
    rw [Matrix.rank_eq_finrank_range_toLin (T ^ 2)
      (Pi.basisFun ℝ n) (Pi.basisFun ℝ n), Matrix.toLin_eq_toLin'] at hrank
    exact hrank
  have htrace : Matrix.trace (T ^ 2) = 1 := by
    have hproj := (LinearMap.isProj_range_iff_isIdempotentElem f).2 hf |>.trace
    rw [Matrix.trace_toLin'_eq] at hproj
    rw [hrange] at hproj
    exact_mod_cast hproj
  obtain ⟨a, b, hab⟩ :=
    Matrix.hasRankOneFactorization_of_mul_self_eq_self hsq_idem htrace
  refine ⟨a, b, hab, ?_⟩
  rw [← Matrix.trace_vecMulVec, ← hab]
  exact htrace

/-- If a primitive nonnegative real matrix has equal second and third powers,
then its square factors as an outer product of two strictly positive vectors
whose dot product is one. -/
theorem IsPrimitive.exists_pos_pow_two_eq_vecMulVec_of_pow_two_eq_pow_three
    [DecidableEq n] [Nonempty n] {T : Matrix n n ℝ}
    (hT : T.IsPrimitive) (h : T ^ 2 = T ^ 3) :
    ∃ a b : n → ℝ, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      T ^ 2 = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1 := by
  obtain ⟨a, b, hab, hdot⟩ :=
    hT.exists_pow_two_eq_vecMulVec_of_pow_two_eq_pow_three h
  have htrace : Matrix.trace (T ^ 2) = 1 := by
    rw [hab, Matrix.trace_vecMulVec]
    exact hdot
  exact Matrix.HasRankOneFactorization.exists_pos_factorization_of_pos_of_trace_eq_one
    (T := T ^ 2) ⟨a, b, hab⟩
    (hT.pow_two_pos_of_pow_two_eq_pow_three h) htrace

end Matrix

end Idempotent

namespace Matrix

section PrimitiveAperiodic

/-!
## Primitivity from returns of lengths two and three

An irreducible nonnegative finite matrix is primitive if every vertex of its
positive support has closed walks of lengths two and three. The proof chooses
one positive path between each ordered pair, bounds their lengths uniformly,
and pads every path to a common length using the two coprime return lengths.

This is an auxiliary finite-matrix lemma. For the active sector trace matrix,
it implements the marked local replacement of the source's removal of periodic
components by blocking; it is not an argument stated in the source.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem exists_two_mul_add_three_mul (N : ℕ) (hN : 2 ≤ N) :
    ∃ a b : ℕ, N = 2 * a + 3 * b := by
  rcases Nat.even_or_odd N with ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, 0, by omega⟩
  · exact ⟨a - 1, 1, by omega⟩

private theorem pow_add_apply_pos_of_pos {T : Matrix n n ℝ}
    (hT : ∀ i j, 0 ≤ T i j) {a b : ℕ} {i j k : n}
    (ha : 0 < (T ^ a) i k) (hb : 0 < (T ^ b) k j) :
    0 < (T ^ (a + b)) i j := by
  rw [pow_add, Matrix.mul_apply]
  exact (Finset.sum_pos_iff_of_nonneg (fun l _ ↦
    mul_nonneg (Matrix.pow_apply_nonneg hT a i l)
      (Matrix.pow_apply_nonneg hT b l j))).2
    ⟨k, Finset.mem_univ k, mul_pos ha hb⟩

private theorem diagonal_two_mul_add_three_mul_pos {T : Matrix n n ℝ}
    (hT : ∀ i j, 0 ≤ T i j)
    (h2 : ∀ i, 0 < (T ^ 2) i i) (h3 : ∀ i, 0 < (T ^ 3) i i)
    (a b : ℕ) (i : n) :
    0 < (T ^ (2 * a + 3 * b)) i i := by
  have htwo : ∀ c : ℕ, 0 < (T ^ (2 * c)) i i := by
    intro c
    induction c with
    | zero => simp
    | succ c hc =>
        rw [Nat.mul_succ]
        exact pow_add_apply_pos_of_pos hT hc (h2 i)
  have hthree : ∀ c : ℕ, 0 < (T ^ (3 * c)) i i := by
    intro c
    induction c with
    | zero => simp
    | succ c hc =>
        rw [Nat.mul_succ]
        exact pow_add_apply_pos_of_pos hT hc (h3 i)
  exact pow_add_apply_pos_of_pos hT (htwo a) (hthree b)

/-- An irreducible nonnegative finite matrix with positive length-two and
length-three returns at every index is primitive. -/
theorem IsIrreducible.isPrimitive_of_pow_two_diagonal_pos_of_pow_three_diagonal_pos
    {T : Matrix n n ℝ} (hT : IsIrreducible T)
    (h2 : ∀ i, 0 < (T ^ 2) i i) (h3 : ∀ i, 0 < (T ^ 3) i i) :
    IsPrimitive T := by
  classical
  have hexists : ∀ i j : n, ∃ m : ℕ, 0 < m ∧ 0 < (T ^ m) i j :=
    (isIrreducible_iff_exists_pow_pos hT.nonneg).1 hT
  let m : n × n → ℕ := fun q ↦ Classical.choose (hexists q.1 q.2)
  have hmpos : ∀ i j : n, 0 < (T ^ m (i, j)) i j := fun i j ↦
    (Classical.choose_spec (hexists i j)).2
  let L : ℕ := ∑ q : n × n, m q
  refine ⟨hT.nonneg, 2 * L + 2, by omega, fun i j ↦ ?_⟩
  have hmL : m (i, j) ≤ L := by
    exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le (m q))
      (Finset.mem_univ (i, j))
  let r := 2 * L + 2 - m (i, j)
  have hmr : m (i, j) + r = 2 * L + 2 := by
    dsimp [r]
    exact Nat.add_sub_of_le (by omega)
  have hr : 2 ≤ r := by
    dsimp [r]
    omega
  obtain ⟨a, b, hab⟩ := exists_two_mul_add_three_mul r hr
  have hreturn : 0 < (T ^ r) j j := by
    rw [hab]
    exact diagonal_two_mul_add_three_mul_pos hT.nonneg h2 h3 a b j
  have hpositive : 0 < (T ^ (m (i, j) + r)) i j :=
    pow_add_apply_pos_of_pos hT.nonneg (hmpos i j) hreturn
  rwa [hmr] at hpositive

end PrimitiveAperiodic

section SupportStabilization

/-!
## Stabilization of the positive support of matrix powers

This file records an elementary aperiodicity criterion for finite
nonnegative matrices. If an irreducible matrix has the same positive support
at powers two and three, then its square is strictly positive.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem pow_support_succ
    {T : Matrix n n ℝ} (hT : ∀ i j, 0 ≤ T i j) {m : ℕ}
    (hm : ∀ i j, 0 < (T ^ m) i j ↔ 0 < (T ^ (m + 1)) i j) :
    ∀ i j, 0 < (T ^ (m + 1)) i j ↔ 0 < (T ^ (m + 2)) i j := by
  intro i j
  rw [show T ^ (m + 1) = T ^ m * T by rw [pow_succ],
    show T ^ (m + 2) = T ^ (m + 1) * T by rw [show m + 2 = (m + 1) + 1 by omega,
      pow_succ], Matrix.mul_apply, Matrix.mul_apply]
  constructor
  · intro h
    obtain ⟨k, hk, hik⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun k _ ↦
        mul_nonneg (Matrix.pow_apply_nonneg hT m i k) (hT k j))).1 h
    have hkj : 0 < T k j := pos_of_mul_pos_right hik
      (Matrix.pow_apply_nonneg hT m i k)
    exact (Finset.sum_pos_iff_of_nonneg (fun k _ ↦
      mul_nonneg (Matrix.pow_apply_nonneg hT (m + 1) i k) (hT k j))).2
      ⟨k, hk, mul_pos ((hm i k).1 (pos_of_mul_pos_left hik (hT k j))) hkj⟩
  · intro h
    obtain ⟨k, hk, hik⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun k _ ↦
        mul_nonneg (Matrix.pow_apply_nonneg hT (m + 1) i k) (hT k j))).1 h
    have hkj : 0 < T k j := pos_of_mul_pos_right hik
      (Matrix.pow_apply_nonneg hT (m + 1) i k)
    exact (Finset.sum_pos_iff_of_nonneg (fun k _ ↦
      mul_nonneg (Matrix.pow_apply_nonneg hT m i k) (hT k j))).2
      ⟨k, hk, mul_pos ((hm i k).2 (pos_of_mul_pos_left hik (hT k j))) hkj⟩

/-- Let \(T\) be a finite irreducible nonnegative matrix. If \(T^2\) and
\(T^3\) have the same positive support, then every entry of \(T^2\) is
strictly positive.

Indeed, right multiplication by \(T\) propagates equality of consecutive
supports to all powers from the second onward. Irreducibility supplies a
positive path between each ordered pair; if this path has length one, append
a nonempty return path at its endpoint. The resulting path has length at
least two and may therefore be shortened, at the level of support, to length
two. -/
theorem IsIrreducible.pow_two_pos_of_pow_two_support_eq_pow_three_support
    {T : Matrix n n ℝ} (hT : IsIrreducible T)
    (hsupport : ∀ i j, 0 < (T ^ 2) i j ↔ 0 < (T ^ 3) i j) :
    ∀ i j, 0 < (T ^ 2) i j := by
  have hstep : ∀ m : ℕ, 2 ≤ m →
      ∀ i j, 0 < (T ^ m) i j ↔ 0 < (T ^ (m + 1)) i j := by
    intro m hm
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction r with
    | zero =>
        simpa using hsupport
    | succ r ih =>
        simpa [Nat.add_assoc] using pow_support_succ hT.nonneg (ih (by omega))
  have hcollapse : ∀ m : ℕ, 2 ≤ m →
      ∀ i j, 0 < (T ^ m) i j → 0 < (T ^ 2) i j := by
    intro m hm
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
    intro i j hij
    induction r with
    | zero =>
        simpa using hij
    | succ r ih =>
        apply ih (by omega)
        exact (hstep (2 + r) (by omega) i j).2 (by simpa [Nat.add_assoc] using hij)
  have hexists : ∀ i j : n, ∃ m > 0, 0 < (T ^ m) i j :=
    (isIrreducible_iff_exists_pow_pos hT.nonneg).1 hT
  intro i j
  obtain ⟨m, hm, hij⟩ := hexists i j
  by_cases hmone : m = 1
  · obtain ⟨r, hr, hjj⟩ := hexists j j
    have hpath : 0 < (T ^ (m + r)) i j :=
      pow_add_apply_pos_of_pos hT.nonneg hij hjj
    exact hcollapse (m + r) (by omega) i j hpath
  · exact hcollapse m (by omega) i j hij

end SupportStabilization

end Matrix
