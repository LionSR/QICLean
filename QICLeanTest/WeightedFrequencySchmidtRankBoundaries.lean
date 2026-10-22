import QICLean.Algebra.WeightedFrequencySchmidtRank

/-!
# Boundary applications for weighted original-frequency sums

Each bound retains the actual conclusion of the imported theorem. No separate
frequency coefficient or middle-coordinate definition is introduced.
-/

open scoped BigOperators Kronecker

namespace WeightedFrequencyBoundary

private abbrev One := Fin 1
private abbrev Three := (One × One) × One

noncomputable local instance : DecidableEq Bool := Classical.decEq Bool

private def identityFamily (_ : Bool) : Matrix Three Three ℂ := 1

private theorem one_dimensional_rank_le_one
    (X : Matrix (One × One) (One × One) ℂ) :
    Matrix.operatorSchmidtRank X ≤ 1 := by
  simpa [Matrix.operatorSchmidtRank, Module.finrank_matrix] using
    LinearMap.finrank_range_le (Matrix.operatorSchmidtMap X)

open Classical in
private theorem zero_rank_le_zero {a b : Type*} [Fintype a] [Fintype b] :
    Matrix.operatorSchmidtRank (0 : Matrix (a × b) (a × b) ℂ) ≤ 0 := by
  exact Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨Fin.elim0, Fin.elim0, by simp⟩

-- Its inferred type is the actual public conclusion, including its equality instances.
open Classical in
private noncomputable abbrev identityBound (k i j : ℕ)
    (weight : (Bool → ℕ) → ℂ) :=
  Matrix.operatorSchmidtRank_middle_sum_smul_full_counts_le
    identityFamily (fun _ ↦ (0 : Matrix One One ℂ))
    (fun _ ↦ (0 : Matrix One One ℂ)) (fun _ ↦ (0 : Matrix One One ℂ))
    false true (by intro h; cases h)
    (1 : Matrix (One × One) (One × One) ℂ)
    (1 : Matrix (One × One) (One × One) ℂ)
    (by intro b hb0 hb1; cases b <;> contradiction)
    (by
      ext x y
      have hxy : x = y := Subsingleton.elim _ _
      subst y
      simp [identityFamily])
    (by
      ext x y
      have hxy : x = y := Subsingleton.elim _ _
      subst y
      simp [identityFamily, Matrix.reindex_apply])
    (rU := 1) (rV := 1)
    (one_dimensional_rank_le_one _)
    (one_dimensional_rank_le_one _) k i j weight

-- Nonzero identity letters at k=0. Only the numerical right side is simplified.
open Classical in
private noncomputable abbrev zeroPowerBound :=
  Nat.le_trans (identityBound 0 0 0 (fun _ ↦ 1))
    (show _ ≤ 1 from by
      norm_num [Finset.piAntidiag_zero, Finset.filter_singleton])

-- All impossible count pairs on the same actual nonzero family, with arbitrary weights.
open Classical in
private noncomputable abbrev impossibleCountsBound (k i j : ℕ)
    (hbad : k < i + j) (weight : (Bool → ℕ) → ℂ) :=
  Nat.le_trans (identityBound k i j weight)
    (show _ ≤ 0 from by
      calc
        _ ≤ 0 * _ := Nat.mul_le_mul_right _ (by
          apply Nat.le_of_eq
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro α hα
          rcases Finset.mem_filter.mp hα with ⟨hαE, hα0, hα1⟩
          have hsum : (∑ b, α b) = k := (Finset.mem_piAntidiag.mp hαE).1
          have htwo : α false + α true ≤ ∑ b, α b :=
            Finset.add_le_sum (fun _ _ ↦ Nat.zero_le _)
              (Finset.mem_univ false) (Finset.mem_univ true) (by intro h; cases h)
          have hle : i + j ≤ k := by simpa only [hα0, hα1, hsum] using htwo
          exact (Nat.not_le_of_gt hbad) hle)
        _ = 0 := Nat.zero_mul _)

-- Bool consists of precisely the two distinguished labels: the ordinary alphabet is empty.
-- At k=2,i=j=1, the actual full slice has at most one member and the rank bound is 16.
open Classical in
private noncomputable abbrev mixedWordBound :=
  Nat.le_trans (identityBound 2 1 1 (fun _ ↦ 1))
    (show _ ≤ 16 from by
      norm_num only [one_pow, mul_one, Nat.choose]
      calc
        _ ≤ 1 * 16 := Nat.mul_le_mul_right 16 (by
          apply Finset.card_le_one.mpr
          intro α hα β hβ
          have ha := (Finset.mem_filter.mp hα).2
          have hb := (Finset.mem_filter.mp hβ).2
          funext b
          cases b with
          | false => exact ha.1.trans hb.1.symm
          | true => exact ha.2.trans hb.2.symm)
        _ = 16 := rfl)

-- Empty left factor, positive word length, rU=rV=0, including the factor 0^0.
-- The entire public conclusion is inferred directly, without reconstructing its sum.
open Classical in
private noncomputable abbrev emptyFactorBound :=
  Nat.le_trans
    (Matrix.operatorSchmidtRank_middle_sum_smul_full_counts_le
      (l := Fin 0) (m := One) (n := One)
      (fun _ : Bool ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0)
      false true (by intro h; cases h) 0 0
      (by intro b _ _; exact Subsingleton.elim _ _)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
      (rU := 0) (rV := 0)
      (zero_rank_le_zero (a := Fin 0) (b := One))
      (zero_rank_le_zero (a := One) (b := One)) 1 1 0 (fun _ ↦ 1))
    (show _ ≤ 0 from by simp only [pow_one, pow_zero, mul_zero, zero_mul, le_refl])

end WeightedFrequencyBoundary
