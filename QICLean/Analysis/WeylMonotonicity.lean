/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Interval.Finset.Fin

/-!
# Weyl monotonicity for finite Hermitian matrices

For Hermitian matrices in the Loewner order, the decreasingly ordered
eigenvalues are ordered term by term.  This is the consequence of Weyl's
monotonicity theorem used immediately before Wolf's Proposition 5.3:

`A ≤ B → λⱼ↓(A) ≤ λⱼ↓(B)`.

The proof uses the finite-dimensional variational argument.  The span of the
first `j + 1` eigenvectors of `A` and the span of the last `d - j`
eigenvectors of `B` have dimensions summing to `d + 1`, hence contain a common
nonzero vector.  The two ordered spectral expansions bound its quadratic form
from below and above, while positivity of `B - A` compares the two forms.

## Main results

* `LinearMap.IsSymmetric.eigenvalues_le_of_sub_isPositive` compares the ordered
  eigenvalues of symmetric endomorphisms when their difference is positive.
* `Matrix.IsHermitian.eigenvalues₀_mono` is Weyl monotonicity for the canonical
  `Fin (Fintype.card n)` indexing.
* `Matrix.IsHermitian.eigenvalues_mono` gives the corresponding statement for
  Mathlib's matrix-indexed eigenvalue family.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5,
  Equation (5.56)][Wolf2012QChannels]
* [R. Bhatia, *Matrix Analysis*][bhatia1997]
-/

open scoped ComplexOrder InnerProductSpace MatrixOrder

private theorem symmetric_quadraticForm_eq_sum_eigenvalues_mul_norm_sq
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    (inner ℂ (T x) x).re =
      ∑ j : Fin n, hT.eigenvalues hn j *
        ‖(hT.eigenvectorBasis hn).repr x j‖ ^ 2 := by
  let b := hT.eigenvectorBasis hn
  rw [← b.sum_inner_mul_inner (T x) x, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hT x (b j), hT.apply_eigenvectorBasis]
  rw [inner_smul_right]
  rw [← inner_conj_symm]
  rw [← b.repr_apply_apply]
  rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  change ((↑(hT.eigenvalues hn j) : ℂ) * (↑(‖b.repr x j‖ ^ 2) : ℂ)).re =
    hT.eigenvalues hn j * ‖b.repr x j‖ ^ 2
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  change hT.eigenvalues hn j * ‖b.repr x j‖ ^ 2 - 0 * 0 =
    hT.eigenvalues hn j * ‖b.repr x j‖ ^ 2
  ring

private theorem exists_nonzero_mem_span_Iic_inter_span_Ici
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (b c : Module.Basis (Fin n) ℂ E)
    (hn : Module.finrank ℂ E = n) (i : Fin n) :
    ∃ x : E, x ≠ 0 ∧
      x ∈ Submodule.span ℂ (b '' Set.Iic i) ∧
      x ∈ Submodule.span ℂ (c '' Set.Ici i) := by
  let P := Submodule.span ℂ (b '' Set.Iic i)
  let Q := Submodule.span ℂ (c '' Set.Ici i)
  have hliP : LinearIndependent ℂ (fun j : Set.Iic i ↦ b j.1) :=
    b.linearIndependent.comp (fun j : Set.Iic i ↦ j.1) Subtype.val_injective
  have hrangeP : Set.range (fun j : Set.Iic i ↦ b j.1) = b '' Set.Iic i := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hdimP : Module.finrank ℂ P = i.1 + 1 := by
    change Module.finrank ℂ (Submodule.span ℂ (b '' Set.Iic i)) = i.1 + 1
    rw [← hrangeP, finrank_span_eq_card hliP]
    simp
  have hliQ : LinearIndependent ℂ (fun j : Set.Ici i ↦ c j.1) :=
    c.linearIndependent.comp (fun j : Set.Ici i ↦ j.1) Subtype.val_injective
  have hrangeQ : Set.range (fun j : Set.Ici i ↦ c j.1) = c '' Set.Ici i := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hdimQ : Module.finrank ℂ Q = n - i.1 := by
    change Module.finrank ℂ (Submodule.span ℂ (c '' Set.Ici i)) = n - i.1
    rw [← hrangeQ, finrank_span_eq_card hliQ]
    simp
  have hnotdisjoint : ¬ Disjoint P Q := by
    intro hdisjoint
    have hdim := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
    rw [hdimP, hdimQ, hn] at hdim
    omega
  have hinf : ⊥ < P ⊓ Q := by
    rw [bot_lt_iff_ne_bot]
    intro heq
    apply hnotdisjoint
    rw [disjoint_iff]
    exact heq
  obtain ⟨x, hx⟩ := Submodule.nonzero_mem_of_bot_lt hinf
  refine ⟨x, ?_, x.2.1, x.2.2⟩
  intro hzero
  apply hx
  exact Subtype.ext hzero

namespace LinearMap.IsSymmetric

/-- **Weyl monotonicity for symmetric endomorphisms.** If `T - S` is positive,
then every decreasingly ordered eigenvalue of `S` is at most the eigenvalue of
`T` with the same index. -/
theorem eigenvalues_le_of_sub_isPositive
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {S T : E →ₗ[ℂ] E}
    (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (hST : (T - S).IsPositive)
    (i : Fin n) : hS.eigenvalues hn i ≤ hT.eigenvalues hn i := by
  let bS := hS.eigenvectorBasis hn
  let bT := hT.eigenvectorBasis hn
  obtain ⟨x, hx, hxS, hxT⟩ :=
    exists_nonzero_mem_span_Iic_inter_span_Ici bS.toBasis bT.toBasis hn i
  have hsuppS : ↑(bS.toBasis.repr x).support ⊆ Set.Iic i :=
    bS.toBasis.repr_support_subset_of_mem_span (Set.Iic i) hxS
  have hsuppT : ↑(bT.toBasis.repr x).support ⊆ Set.Ici i :=
    bT.toBasis.repr_support_subset_of_mem_span (Set.Ici i) hxT
  have hzeroS (j : Fin n) (hj : ¬ j ≤ i) : bS.repr x j = 0 := by
    by_contra hne
    have hjmem : j ∈ (bS.toBasis.repr x).support := by
      rw [Finsupp.mem_support_iff, bS.coe_toBasis_repr_apply]
      exact hne
    exact hj (hsuppS hjmem)
  have hzeroT (j : Fin n) (hj : ¬ i ≤ j) : bT.repr x j = 0 := by
    by_contra hne
    have hjmem : j ∈ (bT.toBasis.repr x).support := by
      rw [Finsupp.mem_support_iff, bT.coe_toBasis_repr_apply]
      exact hne
    exact hj (hsuppT hjmem)
  have hnormS : ∑ j : Fin n, ‖bS.repr x j‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa [bS.repr_apply_apply] using bS.sum_sq_norm_inner_right x
  have hnormT : ∑ j : Fin n, ‖bT.repr x j‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa [bT.repr_apply_apply] using bT.sum_sq_norm_inner_right x
  have hSlower : hS.eigenvalues hn i * ‖x‖ ^ 2 ≤ (inner ℂ (S x) x).re := by
    rw [symmetric_quadraticForm_eq_sum_eigenvalues_mul_norm_sq hS hn,
      ← hnormS, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ i
    · exact mul_le_mul_of_nonneg_right (hS.eigenvalues_antitone hn hj) (sq_nonneg _)
    · rw [hzeroS j hj, norm_zero, zero_pow (by omega), mul_zero, mul_zero]
  have hTupper : (inner ℂ (T x) x).re ≤ hT.eigenvalues hn i * ‖x‖ ^ 2 := by
    rw [symmetric_quadraticForm_eq_sum_eigenvalues_mul_norm_sq hT hn,
      ← hnormT, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : i ≤ j
    · exact mul_le_mul_of_nonneg_right (hT.eigenvalues_antitone hn hj) (sq_nonneg _)
    · rw [hzeroT j hj, norm_zero, zero_pow (by omega), mul_zero, mul_zero]
  have hmiddle : (inner ℂ (S x) x).re ≤ (inner ℂ (T x) x).re := by
    have hnonneg := hST.re_inner_nonneg_left x
    simpa [sub_apply, inner_sub_left] using hnonneg
  have hnormpos : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  nlinarith [hSlower.trans (hmiddle.trans hTupper)]

end LinearMap.IsSymmetric

namespace Matrix.IsHermitian

/-- **Weyl monotonicity for Hermitian matrices.** Loewner order compares the
decreasingly ordered eigenvalues term by term, using the canonical
`Fin (Fintype.card n)` indexing.  This is the cross-matrix spectral input used
in Wolf, Chapter 5, Equation (5.56). -/
theorem eigenvalues₀_mono
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A ≤ B) (i : Fin (Fintype.card n)) :
    hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i := by
  have hpos :
      (Matrix.toEuclideanLin B - Matrix.toEuclideanLin A).IsPositive := by
    have hsub : (B - A).PosSemidef := Matrix.le_iff.mp hAB
    simpa using (Matrix.isPositive_toEuclideanLin_iff.mpr hsub)
  exact LinearMap.IsSymmetric.eigenvalues_le_of_sub_isPositive
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
    finrank_euclideanSpace hpos i

/-- Matrix-indexed form of `Matrix.IsHermitian.eigenvalues₀_mono`. -/
theorem eigenvalues_mono
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A ≤ B) (i : n) : hA.eigenvalues i ≤ hB.eigenvalues i := by
  exact hA.eigenvalues₀_mono hB hAB
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm i)

end Matrix.IsHermitian
