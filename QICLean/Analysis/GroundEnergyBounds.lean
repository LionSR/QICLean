/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixAux
import QICLean.Algebra.HermitianHelpers
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Matrix.Spectrum

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


section

section

section

open scoped ComplexOrder

open scoped ComplexOrder MatrixOrder

namespace Matrix

/-- A genuine normalized minimum of a centered matrix identifies the original
canonical minimum after adding back the scalar shift. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005,
and Theorem t:ais, lines 1010–1024.
No simple ground space, spectral gap or prescribed canonical basis is assumed. -/
theorem IsHermitian.minEigenvalue_eq_add_of_centered_ground
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (S E : ℝ) (x : n → ℂ)
    (hunit : star x ⬝ᵥ x = 1)
    (hx : (H - (S : ℂ) • 1) *ᵥ x = (E : ℂ) • x)
    (hlow : ((H - (S : ℂ) • 1) - (E : ℂ) • 1).PosSemidef) :
    minEigenvalue hH = E + S := by
  obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
  let u : n → ℂ := ⇑(hH.eigenvectorBasis i)
  have huunit : star u ⬝ᵥ u = 1 := by
    have h := hH.eigenvectorBasis.inner_eq_one i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa only [u, dotProduct_comm] using h
  have hueigen : H *ᵥ u = (minEigenvalue hH : ℂ) • u := by
    change H *ᵥ ⇑(hH.eigenvectorBasis i) =
      (minEigenvalue hH : ℂ) • ⇑(hH.eigenvectorBasis i)
    rw [hH.mulVec_eigenvectorBasis, hi, Complex.coe_smul]
  have hxeigen : H *ᵥ x = ((E + S : ℝ) : ℂ) • x := by
    have h := hx
    rw [sub_mulVec, smul_mulVec, one_mulVec] at h
    rw [Complex.ofReal_add, add_smul]
    exact sub_eq_iff_eq_add.mp h
  have hsplit : H - ((E + S : ℝ) : ℂ) • (1 : Matrix n n ℂ) =
      (H - (S : ℂ) • 1) - (E : ℂ) • 1 := by
    rw [Complex.ofReal_add, add_smul]
    abel
  have hlowH : (H - ((E + S : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef := by
    rw [hsplit]
    exact hlow
  exact groundEnergy_eq_of_normalized_eigenvectors H (minEigenvalue hH) (E + S)
    u x hueigen huunit hxeigen hunit (sub_minEigenvalue_smul_one_posSemidef hH) hlowH
end Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- The original canonical eigenbasis supplies the centered ground-space gap
without any basis or eigenvalue classification supplied independently of the
original spectrum. Auxiliary to ALVV, arXiv:1602.08828v2,
Assumption (DG), lines 267–280, and Theorem t:ais, lines 1010–1024.
The ground eigenspace may have arbitrary multiplicity. -/
theorem IsHermitian.original_basis_centered_gap_data
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (mu g S E0 : ℝ)
    (hmu : mu ∈ spectrum ℝ H)
    (hgap : ∀ lam ∈ spectrum ℝ H, lam = mu ∨ mu + g ≤ lam) (hg : 0 < g)
    (z : n → ℂ) (hzunit : star z ⬝ᵥ z = 1)
    (hzeigen : (H - (S : ℂ) • 1) *ᵥ z = (E0 : ℂ) • z)
    (hlow : ((H - (S : ℂ) • 1) - (E0 : ℂ) • 1).PosSemidef) :
    mu = E0 + S ∧
      (∀ i, Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (H - (S : ℂ) • 1)
        (hH.eigenvectorBasis i) = ((hH.eigenvalues i - S : ℝ) : ℂ) •
          hH.eigenvectorBasis i) ∧
      ∀ i, hH.eigenvalues i - S = E0 ∨ E0 + g ≤ hH.eigenvalues i - S := by
  have hmurange : mu ∈ Set.range hH.eigenvalues := by
    rw [← hH.spectrum_real_eq_range_eigenvalues]
    exact hmu
  obtain ⟨j, hj⟩ := hmurange
  have hminle : minEigenvalue hH ≤ mu := by
    simpa only [hj] using minEigenvalue_le hH j
  obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
  have hminmu : minEigenvalue hH = mu := by
    rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with heq | hle
    · exact hi.symm.trans heq
    · rw [hi] at hle
      exfalso
      linarith
  have hmuE : mu = E0 + S := hminmu.symm.trans
    (hH.minEigenvalue_eq_add_of_centered_ground S E0 z hzunit hzeigen hlow)
  refine ⟨hmuE, ?_, ?_⟩
  · intro i
    apply (WithLp.ofLp_injective 2)
    simp only [ofLp_toEuclideanCLM, WithLp.ofLp_sub, WithLp.ofLp_smul, sub_mulVec, smul_mulVec,
      one_mulVec, hH.mulVec_eigenvectorBasis, Complex.ofReal_sub, sub_smul,
      Complex.coe_smul]
  · intro i
    rcases hgap _ (hH.eigenvalues_mem_spectrum_real i) with heq | hle
    · left
      linarith
    · right
      linarith
end Matrix
end
end
end
