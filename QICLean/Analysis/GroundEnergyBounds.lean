/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Positive matrices and ground energies

Normalized eigenvectors and positive lower bounds determine their common ground energy. Order
sandwiches preserve vectors at their common lower energy, and positive connecting interactions
bound the increase above an attained ground energy.

These are supporting results for ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines873–886, and the proof of `t:ais`, lines1010–1024.
-/

section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker

namespace Matrix.PosSemidef

/-- A real eigenvalue of a positive matrix is nonnegative when its supplied
vector has raw dot-product normalization one. Auxiliary to the energy budget
in ALVV, arXiv:1602.08828v2, Theorem t:ais, lines 1010–1024.
No simplicity, spectral gap or nonempty-index premise is imposed. -/
theorem nonneg_of_normalized_eigenvector
    {n : Type*} [Fintype n] {A : Matrix n n ℂ} (hA : A.PosSemidef)
    (e : ℝ) (x : n → ℂ) (hx : A *ᵥ x = (e : ℂ) • x)
    (hunit : star x ⬝ᵥ x = 1) : 0 ≤ e := by
  have hnonneg := hA.dotProduct_mulVec_nonneg x
  rw [hx, dotProduct_smul, hunit, smul_eq_mul, mul_one] at hnonneg
  exact Complex.zero_le_real.mp hnonneg
end Matrix.PosSemidef

namespace Matrix

/-- Two normalized eigenvectors attaining positive-semidefinite lower bounds
for the same matrix determine the same real ground energy. Auxiliary to the
successive truncations in ALVV, arXiv:1602.08828v2,
Corollary c:goodagsphardtrunc, lines 979–1005.
No common eigenvector, simple ground space or spectral gap is assumed. -/
theorem groundEnergy_eq_of_normalized_eigenvectors
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    (e e' : ℝ) (x y : n → ℂ)
    (hx : A *ᵥ x = (e : ℂ) • x) (hxunit : star x ⬝ᵥ x = 1)
    (hy : A *ᵥ y = (e' : ℂ) • y) (hyunit : star y ⬝ᵥ y = 1)
    (he : (A - (e : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (he' : (A - (e' : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) : e = e' := by
  have hle (a b : ℝ) (v : n → ℂ)
      (hpos : (A - (a : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
      (hv : A *ᵥ v = (b : ℂ) • v) (hunit : star v ⬝ᵥ v = 1) : a ≤ b := by
    have hshift : (A - (a : ℂ) • (1 : Matrix n n ℂ)) *ᵥ v =
        ((b - a : ℝ) : ℂ) • v := by
      rw [sub_mulVec, smul_mulVec, one_mulVec, hv, Complex.ofReal_sub, sub_smul]
    exact sub_nonneg.mp
      (hpos.nonneg_of_normalized_eigenvector (b - a) v hshift hunit)
  exact le_antisymm (hle e e' y he hy hyunit) (hle e' e x he' hx hxunit)
end Matrix

section

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- An order sandwich preserves a vector at the common lower energy.
This is auxiliary to the hard-truncation argument in ALVV,
arXiv:1602.08828v2, Theorem t:ais, lines 1010–1024.
It asserts no particular functional-calculus formula for the middle operator. -/
theorem mulVec_eq_smul_of_order_sandwich
    {n : Type*} [Fintype n] [DecidableEq n]
    (A F : Matrix n n ℂ) (e : ℝ) (x : n → ℂ)
    (hEF : (e : ℂ) • (1 : Matrix n n ℂ) ≤ F) (hFA : F ≤ A)
    (hx : A *ᵥ x = (e : ℂ) • x) : F *ᵥ x = (e : ℂ) • x := by
  have hlow : (F - (e : ℂ) • (1 : Matrix n n ℂ)).PosSemidef :=
    le_iff.mp hEF
  have hhigh : (A - F).PosSemidef := le_iff.mp hFA
  have hsum : (F - (e : ℂ) • (1 : Matrix n n ℂ)) + (A - F) =
      A - (e : ℂ) • (1 : Matrix n n ℂ) := by abel
  have hsumx : ((F - (e : ℂ) • (1 : Matrix n n ℂ)) + (A - F)) *ᵥ x = 0 := by
    rw [hsum, sub_mulVec, smul_mulVec, one_mulVec, hx, sub_self]
  have hFx := hlow.mulVec_eq_zero_left hhigh x hsumx
  simpa only [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] using hFx
end Matrix
end

section

open scoped ComplexOrder MatrixOrder

namespace Matrix

/-- A common regional zero-energy test vector bounds the ground energy
after adding a positive connecting interaction. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and Theorem `t:ais`,
lines 1010–1024. The test vector and the ground vector may be different;
no uniqueness or spectral gap is assumed. -/
theorem groundEnergy_bounds_of_positive_boundary_and_zero_test
    {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) (C e : ℝ)
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (hYC : Y ≤ (C : ℂ) • (1 : Matrix n n ℂ))
    (x z : n → ℂ) (hx : X *ᵥ x = 0) (hxunit : star x ⬝ᵥ x = 1)
    (hz : (X + Y) *ᵥ z = (e : ℂ) • z) (hzunit : star z ⬝ᵥ z = 1)
    (helow : (X + Y - (e : ℂ) • (1 : Matrix n n ℂ)).PosSemidef) :
    0 ≤ e ∧ e ≤ C := by
  have he0 : 0 ≤ e := (hX.add hY).nonneg_of_normalized_eigenvector e z hz hzunit
  have hpos := helow.add (le_iff.mp hYC)
  have hev : ((X + Y - (e : ℂ) • (1 : Matrix n n ℂ)) +
      ((C : ℂ) • (1 : Matrix n n ℂ) - Y)) *ᵥ x = ((C - e : ℝ) : ℂ) • x := by
    simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, hx, zero_add,
      Complex.ofReal_sub, sub_smul]
    abel
  exact ⟨he0, sub_nonneg.mp (hpos.nonneg_of_normalized_eigenvector
    (C - e) x hev hxunit)⟩
end Matrix
end
end

section

open scoped BigOperators ComplexOrder MatrixOrder

namespace Matrix

/-- A sum of original positive unit bonds is positive and bounded above by
the number of bonds. Auxiliary to the five-region decomposition in ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and Theorem `t:ais`,
lines 1010–1024. Empty bond sets and zero-dimensional matrix algebras are included. -/
theorem sum_posSemidef_and_le_card_of_positive_unit_terms
    {ι n : Type*} [Finite n] [DecidableEq n]
    (s : Finset ι) (h : ι → Matrix n n ℂ)
    (h0 : ∀ i ∈ s, 0 ≤ h i) (h1 : ∀ i ∈ s, h i ≤ 1) :
    (∑ i ∈ s, h i).PosSemidef ∧
      (∑ i ∈ s, h i) ≤ (s.card : ℝ) • (1 : Matrix n n ℂ) := by
  let := Fintype.ofFinite n
  refine ⟨nonneg_iff_posSemidef.mp (Finset.sum_nonneg h0), ?_⟩
  rw [Nat.cast_smul_eq_nsmul ℝ]
  exact Finset.sum_le_card_nsmul s h 1 h1
end Matrix
end
