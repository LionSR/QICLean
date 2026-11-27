/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt.Bounds
import QICLean.Algebra.Word.TwoMarkerWordCoefficients
import QICLean.Algebra.Polynomial.CommutingPolynomialGaps
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import QICLean.Algebra.Word.WordMultiplicity
import QICLean.Algebra.Word.OneMarkerFullCounts
import QICLean.Algebra.Polynomial.FiniteMonomialInterpolation

/-!
# Weighted frequency sums of tripartite operators

Fix two distinguished labels in a finite family of tripartite operators.
Every ordinary operator is a sum of three single-factor operators, while the
two distinguished operators cross the left and right boundaries respectively.
On any fixed pair of frequencies, an arbitrary scalar-weighted sum of the
original word coefficients has middle-versus-exterior operator Schmidt rank
bounded by one full-slice cardinality times the two boundary rank bounds.
The scalar recovery uses the same evaluation points for both boundaries.
Empty frequency slices and factors of dimension zero are included.

**Local fix (count):** The binomial factors retain the additional `+1` in
AKLV's exponent-tuple count, as recorded in
`docs/paper-gaps/aklv13_interpolation_and_word_count.tex`.

It also contains the following results.

* `Matrix.operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le`: operator Schmidt rank of a commuting-gap
  coefficient.
* `Matrix.operatorSchmidtRank_sum_smul_one_marker_counts_le`: one-marker weighted frequency sums.

## Main results

* `Matrix.operatorSchmidtRank_sum_le_of_monomial_evaluations`,
  `Matrix.operatorSchmidtRank_sum_smul_le_of_injective_monomial_evaluations`: operator Schmidt rank
  of selected monomial coefficients.

## References

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`),
lines 626–662, and ALVV, arXiv:1602.08828v2, Proposition 5.7
(`prop:Cheby-AGSP-eff`), lines 1324–1332. The displayed local tensor forms
are explicit hypotheses of this auxiliary. Identifying them with physical
Hamiltonian terms, selecting low frequencies, counting the physical variable
sets, moving the cuts and constructing matrix product operators are separate
steps; the full statements of those source results are not asserted here.
-/

section MonomialEvaluationSchmidtRank

/-!
## Operator Schmidt rank of selected monomial coefficients

Suppose every evaluation of a finite operator-valued monomial sum has
operator Schmidt rank at most `r`. Every selected sum of its coefficients
then has rank at most the number of prescribed monomials times `r`.

The scalar recovery points and coefficients depend only on the monomial
support. Summing the recovery formulas combines the selected coefficients
at those same points before applying the finite-sum rank bound.
The operator coefficients may vanish or coincide.

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 626–644.
The Hamiltonian generating-polynomial identification and the locality bound
for its evaluated operators are separate statements.
-/

open scoped BigOperators

namespace Matrix

open Classical in
/-- A selected sum of coefficient operators inherits a finite interpolation rank bound.
Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 626–644.
The evaluated family need only span; the coefficient operators may be dependent.
This does not identify Hamiltonian coefficients or prove a locality estimate. -/
theorem operatorSchmidtRank_sum_le_of_monomial_evaluations
    {σ l n : Type*} [Fintype l] [Finite n]
    (S : Finset (σ →₀ ℕ)) :
    ∀ (f : (σ →₀ ℕ) → Matrix (l × n) (l × n) ℂ)
      (U : Finset (σ →₀ ℕ)), U ⊆ S → ∀ r : ℕ,
      (∀ z : σ → ℂ, operatorSchmidtRank
        (∑ α ∈ S, MvPolynomial.eval z
          (MvPolynomial.monomial α (1 : ℂ)) • f α) ≤ r) →
      operatorSchmidtRank (∑ α ∈ U, f α) ≤ S.card * r := by
  obtain ⟨z, c, hrec⟩ := MvPolynomial.exists_monomial_evaluation_recovery S
  intro f U hU r heval
  have hsum :
      (∑ α : U, ∑ i : Fin S.card, c ⟨α.val, hU α.property⟩ i •
        (∑ β : S, MvPolynomial.eval (z i)
          (MvPolynomial.monomial β.val (1 : ℂ)) • f β.val)) =
        ∑ α : U, f α.val :=
    Finset.sum_congr rfl fun α _ ↦
      MvPolynomial.monomial_evaluation_recovery_smul S z c hrec
        (fun β : S ↦ f β.val) ⟨α.val, hU α.property⟩
  rw [Finset.sum_comm] at hsum
  simp_rw [← Finset.sum_smul] at hsum
  rw [← Finset.sum_coe_sort U f, ← hsum]
  refine (operatorSchmidtRank_sum_le Finset.univ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin S.card, r := Finset.sum_le_sum fun i _ ↦
      (operatorSchmidtRank_smul_le _ _).trans
        (by simpa only [← Finset.sum_coe_sort S (fun α ↦
          MvPolynomial.eval (z i) (MvPolynomial.monomial α (1 : ℂ)) • f α)]
          using heval (z i))
    _ = _ := by simp

/-- A scalar-weighted sum of an injectively indexed finite monomial family has rank
at most its cardinality times the common evaluation-rank bound. Zero and dependent
operator coefficients are allowed. AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`),
lines 626--644. -/
theorem operatorSchmidtRank_sum_smul_le_of_injective_monomial_evaluations
    {σ τ l n : Type*} [Fintype l] [Finite n]
    (T : Finset τ) (ρ : τ → (σ →₀ ℕ)) (hρ : Set.InjOn ρ T)
    (f : τ → Matrix (l × n) (l × n) ℂ) (weight : τ → ℂ) (r : ℕ)
    (heval : ∀ z : σ → ℂ, operatorSchmidtRank
      (∑ α ∈ T, MvPolynomial.eval z
        (MvPolynomial.monomial (ρ α) (1 : ℂ)) • f α) ≤ r) :
    operatorSchmidtRank (∑ α ∈ T, weight α • f α) ≤ T.card * r := by
  classical
  let S := T.image ρ
  let lift : T → S := fun α ↦ ⟨ρ α.val, Finset.mem_image_of_mem ρ α.property⟩
  have hlift : Function.Bijective lift := by
    constructor
    · intro α β h
      exact Subtype.ext (hρ α.property β.property (congrArg Subtype.val h))
    · intro β
      obtain ⟨α, hα, hρα⟩ := Finset.mem_image.mp β.property
      exact ⟨⟨α, hα⟩, Subtype.ext hρα⟩
  let e : T ≃ S := Equiv.ofBijective lift hlift
  let g : S → Matrix (l × n) (l × n) ℂ := fun β ↦ f (e.symm β).val
  let w : S → ℂ := fun β ↦ weight (e.symm β).val
  let E (z : σ → ℂ) :=
    ∑ β : S, MvPolynomial.eval z (MvPolynomial.monomial β.val (1 : ℂ)) • g β
  have hE (z : σ → ℂ) : operatorSchmidtRank (E z) ≤ r := by
    have hsum :
        (∑ α : T, MvPolynomial.eval z
          (MvPolynomial.monomial (ρ α.val) (1 : ℂ)) • f α.val) = E z := by
      refine Fintype.sum_equiv e _ _ ?_
      intro α
      change MvPolynomial.eval z
          (MvPolynomial.monomial (ρ α.val) (1 : ℂ)) • f α.val =
        MvPolynomial.eval z (MvPolynomial.monomial (e α).val (1 : ℂ)) •
          f (e.symm (e α)).val
      rw [e.symm_apply_apply]
      rfl
    have hz : operatorSchmidtRank
        (∑ α : T, MvPolynomial.eval z
          (MvPolynomial.monomial (ρ α.val) (1 : ℂ)) • f α.val) ≤ r := by
      simpa only [← Finset.sum_coe_sort T (fun α ↦
        MvPolynomial.eval z (MvPolynomial.monomial (ρ α) (1 : ℂ)) • f α)]
        using heval z
    exact hsum ▸ hz
  obtain ⟨z, c, hrec⟩ := MvPolynomial.exists_monomial_evaluation_recovery S
  have hrecover (β : S) :
      (∑ t : Fin S.card, c β t • E (z t)) = g β :=
    MvPolynomial.monomial_evaluation_recovery_smul S z c hrec g β
  have hweighted : (∑ α ∈ T, weight α • f α) = ∑ β : S, w β • g β := by
    rw [← Finset.sum_coe_sort T (fun α ↦ weight α • f α)]
    refine Fintype.sum_equiv e _ _ ?_
    intro α
    simp only [w, g, e.symm_apply_apply]
  have hcontract :
      (∑ t : Fin S.card, (∑ β : S, w β * c β t) • E (z t)) =
        ∑ β : S, w β • g β := by
    simp_rw [Finset.sum_smul, mul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.smul_sum, hrecover]
  have hcard : S.card = T.card := Finset.card_image_of_injOn hρ
  rw [hweighted, ← hcontract]
  refine (operatorSchmidtRank_sum_le Finset.univ _).trans ?_
  calc
    _ ≤ ∑ _ : Fin S.card, r := Finset.sum_le_sum fun t _ ↦
      (operatorSchmidtRank_smul_le _ _).trans (hE (z t))
    _ = T.card * r := by simp [hcard]


end Matrix

end MonomialEvaluationSchmidtRank

section WeightedFrequencySchmidtRank

open scoped BigOperators Kronecker

namespace Matrix

section WeightedFrequencySchmidtRank

open Classical in
/-- A weighted sum of the original full-frequency coefficients on one fixed
slice has one interpolation cardinality factor and simultaneous middle-cut control.

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`),
lines 626–662, and ALVV, arXiv:1602.08828v2, Proposition 5.7
(`prop:Cheby-AGSP-eff`), lines 1324–1332. -/
theorem operatorSchmidtRank_middle_sum_smul_full_counts_le
    {ι l m n : Type*} [Fintype ι] [Fintype l] [Fintype m] [Fintype n]
    (H : ι → Matrix ((l × m) × n) ((l × m) × n) ℂ)
    (HL : ι → Matrix l l ℂ) (HM : ι → Matrix m m ℂ)
    (HR : ι → Matrix n n ℂ)
    (u v : ι) (huv : u ≠ v)
    (U : Matrix (l × m) (l × m) ℂ)
    (V : Matrix (m × n) (m × n) ℂ)
    (hlocal : ∀ a, a ≠ u → a ≠ v →
      H a = (HL a ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix n n ℂ) +
        ((1 : Matrix l l ℂ) ⊗ₖ HM a) ⊗ₖ (1 : Matrix n n ℂ) +
        (1 : Matrix (l × m) (l × m) ℂ) ⊗ₖ HR a)
    (hu : H u = U ⊗ₖ (1 : Matrix n n ℂ))
    (hv : H v = ((1 : Matrix l l ℂ) ⊗ₖ V).reindex
      (Equiv.prodAssoc l m n).symm (Equiv.prodAssoc l m n).symm)
    {rU rV : ℕ}
    (hU : operatorSchmidtRank U ≤ rU)
    (hV : operatorSchmidtRank V ≤ rV)
    (k i j : ℕ) (weight : (ι → ℕ) → ℂ) :
    let a := Equiv.prodAssoc l m n
    let e := a.trans ((Equiv.prodComm l (m × n)).trans
      ((Equiv.prodAssoc m n l).trans
        (Equiv.prodCongr (Equiv.refl m) (Equiv.prodComm n l))))
    let T := (Finset.piAntidiag (Finset.univ : Finset ι) k).filter
      (fun α ↦ α u = i ∧ α v = j)
    let coefficient : (ι → ℕ) → Matrix ((l × m) × n) ((l × m) × n) ℂ := fun α ↦
      ∑ w ∈ (Finset.univ : Finset (Fin k → ι)).filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = α),
        (List.ofFn (fun t ↦ H (w t))).prod
    operatorSchmidtRank
        ((∑ α ∈ T, weight α • coefficient α).reindex e e) ≤
      T.card * ((k + i + 1).choose (2 * i + 1) *
        (k + j + 1).choose (2 * j + 1) * rU ^ i * rV ^ j) := by
  classical
  intro a e T coefficient
  let O := ((Finset.univ : Finset ι).erase u).erase v
  let residual (α : ι → ℕ) : ι →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun b ↦ if b ∈ O then α b else 0)
  have hresidual : Set.InjOn residual T := by
    intro α hα β hβ h
    funext b
    by_cases hbu : b = u
    · subst b
      exact (Finset.mem_filter.mp hα).2.1.trans
        (Finset.mem_filter.mp hβ).2.1.symm
    by_cases hbv : b = v
    · subst b
      exact (Finset.mem_filter.mp hα).2.2.trans
        (Finset.mem_filter.mp hβ).2.2.symm
    have hbO : b ∈ O := by simp [O, hbu, hbv]
    have hb := congrArg (fun t : ι →₀ ℕ ↦ t b) h
    simpa [residual, hbO] using hb
  have hmonomial (z : ι → ℂ) (α : ι → ℕ) :
      MvPolynomial.eval z (MvPolynomial.monomial (residual α) (1 : ℂ)) =
        ∏ b ∈ O, z b ^ α b := by
    rw [MvPolynomial.eval_monomial, one_mul,
      Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
    change (∏ b, z b ^ (if b ∈ O then α b else 0)) = _
    calc
      _ = ∏ b, if b ∈ O then z b ^ α b else 1 := by
        refine Finset.prod_congr rfl fun b _ ↦ ?_
        by_cases hb : b ∈ O <;> simp [hb]
      _ = _ := Finset.prod_ite_mem_eq O (fun b ↦ z b ^ α b)
  have hD (z : ι → ℂ) :
      (∑ b ∈ O, z b • H b) =
        ((∑ b ∈ O, z b • HL b) ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ
            (1 : Matrix n n ℂ) +
          ((1 : Matrix l l ℂ) ⊗ₖ (∑ b ∈ O, z b • HM b)) ⊗ₖ
            (1 : Matrix n n ℂ) +
          (1 : Matrix (l × m) (l × m) ℂ) ⊗ₖ
            (∑ b ∈ O, z b • HR b) := by
    calc
      _ = ∑ b ∈ O, z b •
          ((HL b ⊗ₖ (1 : Matrix m m ℂ)) ⊗ₖ (1 : Matrix n n ℂ) +
            ((1 : Matrix l l ℂ) ⊗ₖ HM b) ⊗ₖ (1 : Matrix n n ℂ) +
            (1 : Matrix (l × m) (l × m) ℂ) ⊗ₖ HR b) := by
        refine Finset.sum_congr rfl fun b hb ↦ ?_
        have hbv : b ≠ v := (Finset.mem_erase.mp hb).1
        have hbu : b ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
        rw [hlocal b hbu hbv]
      _ = _ := by
        ext ⟨⟨x, y⟩, z'⟩ ⟨⟨x', y'⟩, z''⟩
        simp [Matrix.sum_apply, Finset.sum_add_distrib, Finset.mul_sum,
          mul_assoc, mul_comm, mul_left_comm]
  have hlinear :
      ((∑ α ∈ T, weight α • coefficient α).reindex e e) =
        ∑ α ∈ T, weight α • (coefficient α).reindex e e := by
    ext x y
    simp [Matrix.reindex_apply, Matrix.sum_apply]
  rw [hlinear]
  by_cases hij : i + j ≤ k
  · have hi : i ≤ k := (Nat.le_add_right i j).trans hij
    have hj : j ≤ k := (Nat.le_add_left j i).trans hij
    apply operatorSchmidtRank_sum_smul_le_of_injective_monomial_evaluations T residual hresidual
      (fun α ↦ (coefficient α).reindex e e) weight
    intro z
    let Fz : Polynomial (Polynomial
        (Matrix ((l × m) × n) ((l × m) × n) ℂ)) :=
      Polynomial.C (Polynomial.C (∑ b ∈ O, z b • H b) +
          Polynomial.C (H v) * Polynomial.X) +
        Polynomial.C (Polynomial.C (H u)) * Polynomial.X
    have hgenerate : ((Fz ^ k).coeff i).coeff j =
        ∑ α ∈ T, (∏ b ∈ O, z b ^ α b) • coefficient α := by
      simpa only [Fz, O, T, coefficient] using
        Polynomial.coeff_coeff_pow_two_markers_eq_sum_full_counts H u v huv z k i j
    have hmiddle : operatorSchmidtRank
        ((((Fz ^ k).coeff i).coeff j).reindex e e) ≤
          (k + i + 1).choose (2 * i + 1) *
            (k + j + 1).choose (2 * j + 1) * rU ^ i * rV ^ j := by
      simpa only [Fz, hu, hv, hD z, a, e] using
        operatorSchmidtRank_middle_coeff_coeff_pow_le
          (∑ b ∈ O, z b • HL b) (∑ b ∈ O, z b • HM b)
          (∑ b ∈ O, z b • HR b) U V hU hV hi hj
    calc
      operatorSchmidtRank
          (∑ α ∈ T, MvPolynomial.eval z
            (MvPolynomial.monomial (residual α) (1 : ℂ)) •
              (coefficient α).reindex e e) =
          operatorSchmidtRank
            ((∑ α ∈ T, (∏ b ∈ O, z b ^ α b) • coefficient α).reindex e e) := by
        congr 1
        ext x y
        simp only [hmonomial, Matrix.reindex_apply, Matrix.submatrix_apply,
          Matrix.sum_apply, Matrix.smul_apply]
      _ = operatorSchmidtRank ((((Fz ^ k).coeff i).coeff j).reindex e e) := by
        rw [← hgenerate]
      _ ≤ _ := hmiddle
  · have hT : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro α hα
      rcases Finset.mem_filter.mp hα with ⟨hαE, hαu, hαv⟩
      have hsum : (∑ b, α b) = k := (Finset.mem_piAntidiag.mp hαE).1
      have htwo : α u + α v ≤ ∑ b, α b :=
        Finset.add_le_sum (fun _ _ ↦ Nat.zero_le _)
          (Finset.mem_univ u) (Finset.mem_univ v) huv
      exact hij (by simpa only [hαu, hαv, hsum] using htwo)
    simpa only [hT, Finset.sum_empty, Finset.card_empty, zero_mul] using
      operatorSchmidtRank_sum_le (∅ : Finset (ι → ℕ))
        (fun α ↦ weight α • (coefficient α).reindex e e)

end WeightedFrequencySchmidtRank

section CommutingPolynomialSchmidtRank

/-!
## Operator Schmidt rank of a commuting-gap coefficient

For commuting bipartite operators `A` and `B` whose ranks are at most one,
and an operator `T` of rank at most `r`, the coefficient of degree `k` in
`(C (A + B) + C T * X)^(m + k)` has operator Schmidt rank at most
`choose (m + 2 * k + 1) (2 * k + 1) * r^k`.

The coefficient belongs to the span of the ordered commuting-gap forms.
Every form has `k` distinguished factors and hence rank at most `r^k`.
Subadditivity and the scalar rank inequality bound the whole coefficient by
this common rank bound times the size of the indexed family.

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 604–617 and 646–657. The Hamiltonian coefficient identification,
local supports, and geometric movement of the chain cut are separate steps.

**Local fix (count):** The count includes the additional `+1` omitted in the source.
See `docs/paper-gaps/aklv13_interpolation_and_word_count.tex`:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
-/

private theorem rank_one_le {l n : Type*} [Fintype l] [Finite n]
    [DecidableEq (l × n)] : operatorSchmidtRank (1 : Matrix (l × n) (l × n) ℂ) ≤ 1 := by
  classical
  exact operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨fun _ : Fin 1 ↦ (1 : Matrix l l ℂ), fun _ : Fin 1 ↦ (1 : Matrix n n ℂ),
      by ext i j; simp [Matrix.one_apply]⟩

private theorem rank_pow_le_one {l n : Type*} [Fintype l] [Fintype n]
    [DecidableEq (l × n)] (A : Matrix (l × n) (l × n) ℂ)
    (hA : operatorSchmidtRank A ≤ 1) (a : ℕ) : operatorSchmidtRank (A ^ a) ≤ 1 := by
  induction a with
  | zero => simpa only [pow_zero] using (rank_one_le (l := l) (n := n))
  | succ a ih =>
    rw [pow_succ]
    exact (operatorSchmidtRank_mul_le _ _).trans (Nat.mul_le_mul ih hA)

private theorem rank_commuting_gap_form_le {l n : Type*} [Fintype l] [Fintype n]
    [DecidableEq (l × n)] (A B T : Matrix (l × n) (l × n) ℂ)
    (hA : operatorSchmidtRank A ≤ 1) (hB : operatorSchmidtRank B ≤ 1)
    {r : ℕ} (hT : operatorSchmidtRank T ≤ r)
    (k : ℕ) (d : Fin (k + 1) × Bool → ℕ) :
    operatorSchmidtRank
      ((List.ofFn (fun j : Fin k ↦
        A ^ d (j.castSucc, false) * B ^ d (j.castSucc, true) * T)).prod *
        (A ^ d (Fin.last k, false) * B ^ d (Fin.last k, true))) ≤ r ^ k := by
  induction k with
  | zero =>
    simpa only [List.ofFn_zero, List.prod_nil, one_mul, pow_zero, Nat.one_mul] using
      (operatorSchmidtRank_mul_le (A ^ d (Fin.last 0, false))
        (B ^ d (Fin.last 0, true))).trans
        (Nat.mul_le_mul (rank_pow_le_one A hA _) (rank_pow_le_one B hB _))
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, mul_assoc]
    have hfirst : operatorSchmidtRank
        (A ^ d (0, false) * B ^ d (0, true) * T) ≤ r := by
      simpa only [Nat.one_mul] using
        (operatorSchmidtRank_mul_le (A ^ d (0, false) * B ^ d (0, true)) T).trans
          (Nat.mul_le_mul
            ((operatorSchmidtRank_mul_le (A ^ d (0, false)) (B ^ d (0, true))).trans
              (Nat.mul_le_mul (rank_pow_le_one A hA _) (rank_pow_le_one B hB _))) hT)
    refine (operatorSchmidtRank_mul_le _ _).trans ?_
    simpa only [pow_succ', Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last] using
      Nat.mul_le_mul hfirst (ih (fun jb ↦ d (jb.1.succ, jb.2)))

/-- The operator Schmidt rank of a distinguished-letter coefficient with commuting
gap factors whose ranks are at most one. Supporting algebra for AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 604–617 and 646–657. The exponent-tuple count uses the
correction in docs/paper-gaps/aklv13_interpolation_and_word_count.tex. -/
theorem operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le
    {l n : Type*} [Fintype l] [Fintype n] [DecidableEq (l × n)]
    (A B T : Matrix (l × n) (l × n) ℂ)
    (hAB : Commute A B)
    (hA : operatorSchmidtRank A ≤ 1)
    (hB : operatorSchmidtRank B ≤ 1)
    {r : ℕ} (hT : operatorSchmidtRank T ≤ r) (m k : ℕ) :
    operatorSchmidtRank
      (((Polynomial.C (A + B) + Polynomial.C T * Polynomial.X) ^ (m + k)).coeff k) ≤
        (m + 2 * k + 1).choose (2 * k + 1) * r ^ k := by
  let E := Finset.piAntidiag (Finset.univ : Finset (Fin (k + 1) × Bool)) m
  let G : E → Matrix (l × n) (l × n) ℂ := fun d ↦
    (List.ofFn (fun j : Fin k ↦
      A ^ d.val (j.castSucc, false) * B ^ d.val (j.castSucc, true) * T)).prod *
      (A ^ d.val (Fin.last k, false) * B ^ d.val (Fin.last k, true))
  have hspan :
      ((Polynomial.C (A + B) + Polynomial.C T * Polynomial.X) ^ (m + k)).coeff k ∈
        Submodule.span ℂ (Set.range G) :=
    Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps (𝕜 := ℂ) A B T hAB m k
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan
  rw [← hc]
  refine (operatorSchmidtRank_sum_le Finset.univ (fun d ↦ c d • G d)).trans ?_
  calc
    _ ≤ ∑ _ : E, r ^ k := Finset.sum_le_sum fun d _ ↦
      (operatorSchmidtRank_smul_le (c d) (G d)).trans
        (rank_commuting_gap_form_le A B T hA hB hT k d.val)
    _ = _ := by simp [E, Finset.card_piAntidiag_univ_fin_prod_bool]

end CommutingPolynomialSchmidtRank

section OneMarkerWeightedSchmidtRank

/-!
## One-marker weighted frequency sums

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

end OneMarkerWeightedSchmidtRank

end Matrix

end WeightedFrequencySchmidtRank
