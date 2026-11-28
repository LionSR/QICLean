/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import QICLean.Analysis.Order.LowEnergyPerturbation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Data.List.GetD

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
* `Matrix.IsHermitian.eigenvalues₀_le_add_of_norm_domRestrict_low_le` compares
  the low ordered eigenvalues from an operator error on the actual closed
  low-energy spectral span.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5,
  Equation (5.56)][Wolf2012QChannels]
* [R. Bhatia, *Matrix Analysis*][bhatia1997]

Moved from TNLean, `TNLean/MPS/Tensor/HalfChain/HalfChainSpectralComparison.lean` at commit
`021ba0bd19` (Apache-2.0).
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

/-- A residual bound on the actual closed low-energy span of `F` compares every
ordered eigenvalue of `H` whose corresponding eigenvalue of `F` is in that span.
The canonical eigenbasis is derived from `F`, and repeated eigenvalues and an
arbitrary real cutoff are allowed. This is the finite-dimensional min--max step
used with the restricted perturbation estimate in ALVV, arXiv:1602.08828v2,
`lem:hard-trunc`, source lines 955–968. -/
theorem eigenvalues₀_le_add_of_norm_domRestrict_low_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {H F : Matrix n n ℂ} (hH : H.IsHermitian) (hF : F.IsHermitian)
    (c ξ : ℝ)
    (hres :
      let bF := (isSymmetric_toEuclideanLin_iff.mpr hF).eigenvectorBasis
        finrank_euclideanSpace
      let G := Submodule.spectralSpanLE bF hF.eigenvalues₀ c
      ‖((toEuclideanCLM (n := n) (𝕜 := ℂ)) H -
          (toEuclideanCLM (n := n) (𝕜 := ℂ)) F).domRestrict G‖ ≤ ξ)
    (i : Fin (Fintype.card n)) (hic : hF.eigenvalues₀ i ≤ c) :
    hH.eigenvalues₀ i ≤ hF.eigenvalues₀ i + ξ := by
  classical
  let S := toEuclideanLin H
  let T := toEuclideanLin F
  let hS : S.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hH
  let hT : T.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hF
  let bS := hS.eigenvectorBasis finrank_euclideanSpace
  let bT := hT.eigenvectorBasis finrank_euclideanSpace
  let G := Submodule.spectralSpanLE bT hF.eigenvalues₀ c
  let D : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
    (toEuclideanCLM (n := n) (𝕜 := ℂ)) H - (toEuclideanCLM (n := n) (𝕜 := ℂ)) F
  obtain ⟨x, hx, hxS, hxT⟩ := exists_nonzero_mem_span_Iic_inter_span_Ici
    bS.toBasis bT.toBasis finrank_euclideanSpace i
  have hsuppS : ↑(bS.toBasis.repr x).support ⊆ Set.Iic i :=
    bS.toBasis.repr_support_subset_of_mem_span (Set.Iic i) hxS
  have hsuppT : ↑(bT.toBasis.repr x).support ⊆ Set.Ici i :=
    bT.toBasis.repr_support_subset_of_mem_span (Set.Ici i) hxT
  have hzeroS (j : Fin (Fintype.card n)) (hj : ¬ j ≤ i) : bS.repr x j = 0 := by
    by_contra hne
    have hjmem : j ∈ (bS.toBasis.repr x).support := by
      rw [Finsupp.mem_support_iff, bS.coe_toBasis_repr_apply]
      exact hne
    exact hj (hsuppS hjmem)
  have hzeroT (j : Fin (Fintype.card n)) (hj : ¬ i ≤ j) : bT.repr x j = 0 := by
    by_contra hne
    have hjmem : j ∈ (bT.toBasis.repr x).support := by
      rw [Finsupp.mem_support_iff, bT.coe_toBasis_repr_apply]
      exact hne
    exact hj (hsuppT hjmem)
  have hnormS : ∑ j : Fin (Fintype.card n), ‖bS.repr x j‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa [bS.repr_apply_apply] using bS.sum_sq_norm_inner_right x
  have hnormT : ∑ j : Fin (Fintype.card n), ‖bT.repr x j‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa [bT.repr_apply_apply] using bT.sum_sq_norm_inner_right x
  have hSlower : hH.eigenvalues₀ i * ‖x‖ ^ 2 ≤ (inner ℂ (S x) x).re := by
    change hS.eigenvalues finrank_euclideanSpace i * ‖x‖ ^ 2 ≤ _
    rw [symmetric_quadraticForm_eq_sum_eigenvalues_mul_norm_sq hS finrank_euclideanSpace,
      ← hnormS, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ≤ i
    · exact mul_le_mul_of_nonneg_right
        (hS.eigenvalues_antitone finrank_euclideanSpace hj) (sq_nonneg _)
    · rw [hzeroS j hj, norm_zero, zero_pow (by omega), mul_zero, mul_zero]
  have hTupper : (inner ℂ (T x) x).re ≤ hF.eigenvalues₀ i * ‖x‖ ^ 2 := by
    change _ ≤ hT.eigenvalues finrank_euclideanSpace i * ‖x‖ ^ 2
    rw [symmetric_quadraticForm_eq_sum_eigenvalues_mul_norm_sq hT finrank_euclideanSpace,
      ← hnormT, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : i ≤ j
    · exact mul_le_mul_of_nonneg_right
        (hT.eigenvalues_antitone finrank_euclideanSpace hj) (sq_nonneg _)
    · rw [hzeroT j hj, norm_zero, zero_pow (by omega), mul_zero, mul_zero]
  have hxG : x ∈ G := by
    apply (show Submodule.span ℂ (bT.toBasis '' Set.Ici i) ≤ G from ?_) hxT
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    exact Submodule.subset_span ⟨j, (hF.eigenvalues₀_antitone hj).trans hic, rfl⟩
  have hnorm : ‖D x‖ ≤ ξ * ‖x‖ := by
    have h := (D.domRestrict G).le_opNorm ⟨x, hxG⟩
    exact h.trans (mul_le_mul_of_nonneg_right hres (norm_nonneg x))
  have hmiddle : (inner ℂ (S x) x).re - (inner ℂ (T x) x).re ≤ ξ * ‖x‖ ^ 2 := by
    calc
      _ = (inner ℂ (D x) x).re := by
        simp only [D, _root_.sub_apply, inner_sub_left, Complex.sub_re]
        rfl
      _ ≤ ‖D x‖ * ‖x‖ := by
        rw [← RCLike.re_to_complex]
        exact re_inner_le_norm _ _
      _ ≤ (ξ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)
      _ = ξ * ‖x‖ ^ 2 := by ring
  have hprod : hH.eigenvalues₀ i * ‖x‖ ^ 2 ≤ (hF.eigenvalues₀ i + ξ) * ‖x‖ ^ 2 := by
    nlinarith only [hSlower, hTupper, hmiddle]
  exact le_of_mul_le_mul_right hprod (sq_pos_of_pos (norm_pos_iff.mpr hx))

end Matrix.IsHermitian

section

open scoped MatrixOrder ComplexOrder Topology

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

namespace IsHermitian

variable {A : Matrix n n ℂ}

/-- An increasing scalar function acts termwise on the decreasing eigenvalues. -/
theorem eigenvalues₀_cfc_monotone (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : Monotone f) (i : Fin (Fintype.card n)) :
    (IsSelfAdjoint.cfc (f := f) (a := A)).isHermitian.eigenvalues₀ i =
      f (hA.eigenvalues₀ i) := by
  have hroots : (cfc f A).charpoly.roots =
      Multiset.map (Complex.ofReal ∘ f ∘ hA.eigenvalues₀) Finset.univ.val := by
    have hroots' : (cfc f A).charpoly.roots =
        Multiset.map (Complex.ofReal ∘ f ∘ hA.eigenvalues) Finset.univ.val := by
      rw [hA.charpoly_cfc_eq, Polynomial.roots_prod]
      · simp
      · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
    rw [hroots']
    change Multiset.map ((Complex.ofReal ∘ f ∘ hA.eigenvalues₀) ∘
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))).symm)
      Finset.univ.val = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  have heq : List.ofFn (IsSelfAdjoint.cfc (f := f) (a := A)).isHermitian.eigenvalues₀ =
      List.ofFn (fun j ↦ f (hA.eigenvalues₀ j)) := by
    rw [← sort_roots_charpoly_eq_eigenvalues₀, hroots]
    simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact (hf.comp_antitone hA.eigenvalues₀_antitone).sortedGE_ofFn
  exact congrFun (List.ofFn_inj.mp heq) i

/-- Adding a scalar multiple of the identity translates every ordered eigenvalue. -/
theorem eigenvalues₀_add_algebraMap (hA : A.IsHermitian) (r : ℝ)
    (i : Fin (Fintype.card n)) :
    (hA.add ((IsSelfAdjoint.all r).algebraMap (Matrix n n ℂ)).isHermitian).eigenvalues₀ i =
      hA.eigenvalues₀ i + r := by
  have heq : cfc (fun x : ℝ ↦ x + r) A = A + algebraMap ℝ (Matrix n n ℂ) r := by
    rw [cfc_add_const r (fun x : ℝ ↦ x) A continuousOn_id hA.isSelfAdjoint,
      cfc_id' ℝ A hA.isSelfAdjoint]
  simpa only [heq] using hA.eigenvalues₀_cfc_monotone (fun x ↦ x + r)
    (fun _ _ h ↦ by dsimp; linarith) i

/-- A nonnegative scalar multiplies the ordered eigenvalues term by term. -/
theorem eigenvalues₀_smul (hA : A.IsHermitian) {r : ℝ} (hr : 0 ≤ r)
    (i : Fin (Fintype.card n)) :
    (hA.smul (IsSelfAdjoint.all r)).eigenvalues₀ i = r * hA.eigenvalues₀ i := by
  have heq : cfc (fun x : ℝ ↦ r * x) A = r • A :=
    cfc_const_mul_id r A hA.isSelfAdjoint
  simpa only [heq] using hA.eigenvalues₀_cfc_monotone (fun x ↦ r * x)
    (fun _ _ h ↦ mul_le_mul_of_nonneg_left h hr) i

open scoped Matrix.Norms.L2Operator in
/-- Weyl's perturbation bound for a fixed ordered eigenvalue, in operator norm. -/
theorem abs_eigenvalues₀_sub_le (hA : A.IsHermitian) {B : Matrix n n ℂ}
    (hB : B.IsHermitian) (i : Fin (Fintype.card n)) :
    |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ‖A - B‖ := by
  have hupper : hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i + ‖A - B‖ := by
    rw [← hB.eigenvalues₀_add_algebraMap]
    apply hA.eigenvalues₀_mono
    exact sub_le_iff_le_add'.mp
      (IsSelfAdjoint.le_algebraMap_norm_self (A - B) (hA.sub hB).isSelfAdjoint)
  have hlower : hB.eigenvalues₀ i ≤ hA.eigenvalues₀ i + ‖A - B‖ := by
    rw [← norm_sub_rev B A, ← hA.eigenvalues₀_add_algebraMap]
    apply hB.eigenvalues₀_mono
    exact sub_le_iff_le_add'.mp
      (IsSelfAdjoint.le_algebraMap_norm_self (B - A) (hB.sub hA).isSelfAdjoint)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

open scoped Matrix.Norms.L2Operator in
/-- Ordered eigenvalues converge when Hermitian matrices converge in fixed dimension. -/
theorem eigenvalues₀_tendsto {α : Type*} {l : Filter α}
    {M : α → Matrix n n ℂ} {B : Matrix n n ℂ}
    (hM : ∀ k, (M k).IsHermitian) (hB : B.IsHermitian)
    (h : Filter.Tendsto M l (𝓝 B)) (i : Fin (Fintype.card n)) :
    Filter.Tendsto (fun k ↦ (hM k).eigenvalues₀ i) l (𝓝 (hB.eigenvalues₀ i)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (g := fun k ↦ ‖M k - B‖)
    (fun k ↦ norm_nonneg _) (fun k ↦ ?_) ?_
  · simpa only [Real.norm_eq_abs] using (hM k).abs_eigenvalues₀_sub_le hB i
  · simpa using (h.sub_const B).norm

/-- The decreasing eigenvalues, followed by zeros after the matrix dimension. -/
noncomputable def paddedEigenvalues (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  (List.ofFn hA.eigenvalues₀).getD k 0

@[simp]
theorem paddedEigenvalues_fin (hA : A.IsHermitian) (i : Fin (Fintype.card n)) :
    hA.paddedEigenvalues i = hA.eigenvalues₀ i := by
  simp [paddedEigenvalues]

/-- Every position past the matrix dimension in the extended spectrum is zero. -/
theorem paddedEigenvalues_eq_zero (hA : A.IsHermitian) {k : ℕ}
    (hk : Fintype.card n ≤ k) : hA.paddedEigenvalues k = 0 := by
  exact List.getD_eq_default _ _ (by simpa using hk)

/-- Multiplication by a nonnegative scalar commutes with zero extension. -/
theorem paddedEigenvalues_smul (hA : A.IsHermitian) {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    (hA.smul (IsSelfAdjoint.all r)).paddedEigenvalues k = r * hA.paddedEigenvalues k := by
  by_cases hk : k < Fintype.card n
  · simpa [paddedEigenvalues, hk] using hA.eigenvalues₀_smul hr ⟨k, hk⟩
  · simp only [paddedEigenvalues_eq_zero _ (Nat.le_of_not_lt hk), mul_zero]

/-- Fixed-dimensional convergence of the zero-extended ordered eigenvalues. -/
theorem paddedEigenvalues_tendsto {α : Type*} {l : Filter α}
    {M : α → Matrix n n ℂ} {B : Matrix n n ℂ}
    (hM : ∀ k, (M k).IsHermitian) (hB : B.IsHermitian)
    (h : Filter.Tendsto M l (𝓝 B)) (i : ℕ) :
    Filter.Tendsto (fun k ↦ (hM k).paddedEigenvalues i) l
      (𝓝 (hB.paddedEigenvalues i)) := by
  by_cases hi : i < Fintype.card n
  · simpa [paddedEigenvalues, hi] using eigenvalues₀_tendsto hM hB h ⟨i, hi⟩
  · simp only [paddedEigenvalues_eq_zero _ (Nat.le_of_not_lt hi)]
    exact tendsto_const_nhds

end IsHermitian

namespace PosSemidef

variable {A : Matrix n n ℂ} {B : Matrix m m ℂ}

/-- Positivity of the canonically indexed eigenvalues. -/
theorem eigenvalues₀_nonneg (hA : A.PosSemidef) (i : Fin (Fintype.card n)) :
    0 ≤ hA.isHermitian.eigenvalues₀ i := by
  simpa [IsHermitian.eigenvalues] using hA.eigenvalues_nonneg
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))) i)

private theorem sort_padded_roots (hA : A.PosSemidef) (k : ℕ) :
    (((Polynomial.X ^ k * A.charpoly).roots.map Complex.re).sort (· ≥ ·)) =
      List.ofFn hA.isHermitian.eigenvalues₀ ++ List.replicate k 0 := by
  have hroots : (Polynomial.X ^ k * A.charpoly).roots.map Complex.re =
      ((List.ofFn hA.isHermitian.eigenvalues₀ ++ List.replicate k 0 : List ℝ) :
        Multiset ℝ) := by
    rw [Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
      A.charpoly_monic.ne_zero), Polynomial.roots_X_pow,
      hA.isHermitian.roots_charpoly_eq_eigenvalues₀]
    simp [Multiset.map_add, Fin.univ_val_map, Function.comp_def,
      ← Multiset.coe_add, Multiset.coe_replicate, Multiset.nsmul_singleton, add_comm]
  rw [hroots, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise, List.sortedGE_append]
  refine ⟨hA.isHermitian.eigenvalues₀_antitone.sortedGE_ofFn, ?_, ?_⟩
  · simp [List.sortedGE_iff_pairwise]
  · intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    have : b = 0 := (List.mem_replicate.mp hb).2
    simpa [this] using hA.eigenvalues₀_nonneg i

private theorem getD_append_zeros (l : List ℝ) (k i : ℕ) :
    (l ++ List.replicate k 0).getD i 0 = l.getD i 0 := by
  by_cases hi : i < l.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    simp [List.getD_eq_getElem?_getD]

/-- Equality of characteristic polynomials after zero padding identifies the
actual decreasing eigenvalue sequences, with zeros beyond their dimensions. -/
theorem paddedEigenvalues_eq_of_charpoly (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : Polynomial.X ^ Fintype.card m * A.charpoly =
      Polynomial.X ^ Fintype.card n * B.charpoly) :
    hA.isHermitian.paddedEigenvalues = hB.isHermitian.paddedEigenvalues := by
  have heq : List.ofFn hA.isHermitian.eigenvalues₀ ++ List.replicate (Fintype.card m) 0 =
      List.ofFn hB.isHermitian.eigenvalues₀ ++ List.replicate (Fintype.card n) 0 := by
    rw [← hA.sort_padded_roots, ← hB.sort_padded_roots, h]
  funext k
  have := congrArg (fun l : List ℝ ↦ l.getD k 0) heq
  simpa only [getD_append_zeros, IsHermitian.paddedEigenvalues] using this

end PosSemidef

end Matrix

end
