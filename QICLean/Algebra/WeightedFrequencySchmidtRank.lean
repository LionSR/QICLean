/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TripartitePolynomialSchmidtRank
import QICLean.Algebra.MonomialEvaluationSchmidtRank
import QICLean.Algebra.TwoMarkerWordCoefficients

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

## References

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma 4.2 (`l:agsp`),
lines 626–662, and ALVV, arXiv:1602.08828v2, Proposition 5.7
(`prop:Cheby-AGSP-eff`), lines 1324–1332. The displayed local tensor forms
are explicit hypotheses of this auxiliary. Identifying them with physical
Hamiltonian terms, selecting low frequencies, counting the physical variable
sets, moving the cuts and constructing matrix product operators are separate
steps; the full statements of those source results are not asserted here.
-/

open scoped BigOperators Kronecker

namespace Matrix


/-- Contract arbitrary scalar weights with the existing recovery coefficients
at one common set of evaluation points. This is a private finite-sum consequence
of the actual monomial recovery theorem, not a new interpolation construction. -/
private theorem rank_weighted_sum_of_injective_monomials
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
    apply rank_weighted_sum_of_injective_monomials T residual hresidual
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

end Matrix
