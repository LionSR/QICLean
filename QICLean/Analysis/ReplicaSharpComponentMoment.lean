/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationReduction
import QICLean.Analysis.ReplicaGoodConfigurationLabelMoment
import QICLean.Analysis.WeightedTraceHolder
import Mathlib.Tactic.Module

/-!
# A sharp exponential estimate for an excitation component

The actual good-copy density retains all five tensor factors, including the
middle physical factor. Two equal half-sum merge terms and three signed physical
label observables give an exponential estimate with the literal component mass.
The only analytic hypothesis concerns the three actual one-copy marginals of the
unit ground vector. No component normalization or nonzero-mass assumption is used.

This is the auxiliary exponential estimate preceding the inverse metric and the
good auxiliary scalar. It does not assert the full component inverse comparison.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, Section 7, `comparator:mgf-data`, `comparator:signed-label-moments`,
  `comparator:merge-moments`, and `comparator:component-inverse`,
  `07-comparators.tex`, lines 75–85, 227–238 and 501–569, at manuscript commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.Operator

namespace TensorPower

/-- The seven actual label regions used in the component estimate form a
laminar family. OpenAI area-law manuscript, Section 7,
`comparator:merge-decomposition`, lines 501–513. -/
private theorem componentLabelRegions_laminar :
    let A : Fin 7 → Finset (Fin 5) := ![{0}, {3}, {0, 3}, {2}, {4}, {2, 4}, {1}]
    ∀ i j, A i ⊆ A j ∨ A j ⊆ A i ∨ Disjoint (A i) (A j) := by
  decide

/-- The five terms used in the weighted Holder estimate are formed from the
actual seven label regions. OpenAI area-law manuscript, Section 7,
`comparator:merge-decomposition`, lines 501–513. -/
private theorem commute_half_sum_labelEntropy_components
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (m : ℕ) :
    let F := fun A => labelEntropy (subsystemPerm m ι A)
    let H := F {0} + F {3} - F {0, 3} + (F {2} + F {4} - F {2, 4})
    let A : Fin 5 → Matrix (Config m ι) (Config m ι) ℂ :=
      ![(1 / 2 : ℂ) • H, (1 / 2 : ℂ) • H, -F {0}, -F {2}, F {1}]
    ∀ i j, Commute (A i) (A j) := by
  intro F H A i j
  let E : Fin 7 → Finset (Fin 5) := ![{0}, {3}, {0, 3}, {2}, {4}, {2, 4}, {1}]
  have hF (s t : Fin 7) : Commute (F (E s)) (F (E t)) :=
    commute_labelObservables_subsystemPerm_of_laminar ι m _ _
      (componentLabelRegions_laminar s t) _ _
  have hH (t : Fin 7) : Commute H (F (E t)) :=
    (((hF 0 t).add_left (hF 1 t)).sub_left (hF 2 t)).add_left
      (((hF 3 t).add_left (hF 4 t)).sub_left (hF 5 t))
  have hrow (s : Fin 5) (t : Fin 7) : Commute (A s) (F (E t)) := by
    fin_cases s
    · exact (hH t).smul_left (1 / 2 : ℂ)
    · exact (hH t).smul_left (1 / 2 : ℂ)
    · exact (hF 0 t).neg_left
    · exact (hF 3 t).neg_left
    · exact hF 6 t
  have hcol : Commute (A i) H :=
    (((hrow i 0).add_right (hrow i 1)).sub_right (hrow i 2)).add_right
      (((hrow i 3).add_right (hrow i 4)).sub_right (hrow i 5))
  fin_cases j
  · exact hcol.smul_right (1 / 2 : ℂ)
  · exact hcol.smul_right (1 / 2 : ℂ)
  · exact (hrow i 0).neg_right
  · exact (hrow i 3).neg_right
  · exact hrow i 6

end TensorPower

namespace Matrix

-- Scalar centering for an arbitrary trace weight; no normalization is used.
set_option backward.isDefEq.respectTransparency false in
private theorem re_trace_exp_centered {n : Type*} [Fintype n] [DecidableEq n]
    (ρ A : Matrix n n ℂ) (s t : ℝ) :
    (ρ * NormedSpace.exp ((t : ℂ) • (A - (s : ℂ) • 1))).trace.re =
      Real.exp (-t * s) * (ρ * NormedSpace.exp ((t : ℂ) • A)).trace.re := by
  have hc : Commute ((t : ℂ) • A) (((-t * s : ℝ) : ℂ) • (1 : Matrix n n ℂ)) := by
    exact (Commute.one_right _).smul_right _
  have he : NormedSpace.exp (((-t * s : ℝ) : ℂ) • (1 : Matrix n n ℂ)) =
      (Real.exp (-t * s) : ℂ) • (1 : Matrix n n ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one,
      ← NormedSpace.ofReal_exp_ℝ_ℝ, ← Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)
        ((-t * s : ℝ) : ℂ)).symm
  have hsplit : (t : ℂ) • (A - (s : ℂ) • 1) =
      (t : ℂ) • A + (((-t * s : ℝ) : ℂ) • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg,
      neg_smul, sub_eq_add_neg, neg_mul]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hc, he]
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

-- A scalar simplification used after five-factor Holder. In particular M may be zero.
private theorem five_moment_majorant {M : ℝ} (hM : 0 ≤ M) (b : Fin 5 → ℝ) :
    (∏ i, (M * Real.exp (b i)) ^ (1 / 5 : ℝ)) =
      M * Real.exp ((∑ i, b i) / 5) := by
  have hp : (M ^ (1 / 5 : ℝ)) ^ 5 = M := by
    convert Real.rpow_inv_natCast_pow (n := 5) hM (by decide) using 1
    norm_num
  simp_rw [Real.mul_rpow hM (Real.exp_pos _).le, ← Real.exp_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [hp, ← Real.exp_sum, ← Finset.sum_mul]
  congr 1
  ring

private theorem re_trace_exp_le_of_five_moment_bounds
    {n : Type*} [Fintype n] [DecidableEq n]
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (A : Fin 5 → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : ∀ i j, Commute (A i) (A j)) (a : ℝ)
    {M : ℝ} (hM : 0 ≤ M) (b : Fin 5 → ℝ)
    (hb : ∀ i,
      (ρ * NormedSpace.exp (((5 * a : ℝ) : ℂ) • A i)).trace.re ≤
        M * Real.exp (b i)) :
    (ρ * NormedSpace.exp ((a : ℂ) • ∑ i, A i)).trace.re ≤
      M * Real.exp ((∑ i, b i) / 5) := by
  have h := hρ.re_trace_mul_exp_sum_le_prod 4 A hA hcomm a
  refine h.trans ?_
  rw [← five_moment_majorant hM b]
  apply Finset.prod_le_prod₀
  · intro i _
    exact Real.rpow_nonneg (hρ.re_trace_mul_exp_nonneg
      ((hA i).smul (by simp [IsSelfAdjoint]))) _
  · intro i _
    exact Real.rpow_le_rpow (hρ.re_trace_mul_exp_nonneg
      ((hA i).smul (by simp [IsSelfAdjoint]))) (hb i) (by norm_num)


/-- The exponential component estimate obtained from the actual good-copy
density, the two merge estimates, and the one-copy surprisal bounds for the
three physical marginals. All three physical tensor factors are retained. The one-copy vector may
be entangled across these factors.

References: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 7, `comparator:mgf-data`,
`comparator:signed-label-moments`, and `comparator:component-inverse`,
`07-comparators.tex`, lines 75–85, 227–238 and 501–569.

This is an auxiliary exponential estimate before the inverse metric and the
good auxiliary scalar are introduced. Its explicit polynomial uses the
arithmetic-mean two-merge bound and five-factor Hölder with two equal
half-sum merge terms. The component mass is retained literally;
there is no normalization or nonzero-mass hypothesis. -/
theorem replicaGoodConfigurationMarginal_exp_mergeDeficits_le_of_surprisalMoment
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (hu : ∀ p : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) p ⊗ₖ
        (permOp (copyPerm (ι 3) k) p ⊗ₖ permOp (copyPerm (ι 4) k) p)) *ᵥ u = u)
    (C₀ c₀ ℬ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) (hℬ : 1 ≤ ℬ) :
    let Ωr := fun r : Fin 3 =>
      fun x : (((s : {s : Fin 3 // s ≠ r}) → ι s.1.castSucc.castSucc) ×
          ι r.castSucc.castSucc) =>
        let q := (Equiv.piSplitAt r (fun s : Fin 3 => ι s.castSucc.castSucc)).symm
          (x.2, x.1)
        Ω (q 0, (q 1, q 2))
    let σ := fun r => partialTraceLeft (vecMulVec (Ωr r) (star (Ωr r)))
    let hσ := fun r => (posSemidef_vecMulVec_self_star (Ωr r)).partialTraceLeft
    let S := fun r => vonNeumannEntropy (σ r) (hσ r).isHermitian
    let m := Bᶜ.card
    let Γ := replicaGoodConfigurationMarginal ι Ω k B u
    let F := fun A => labelEntropy (subsystemPerm m ι A)
    let DC := F {0} + F {3} - F {0, 3}
    let DR := F {2} + F {4} - F {2, 4}
    let K :=
      ((((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ)) / 2
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (∀ (r : Fin 3) (s : ℝ), |s| ≤ c₀ / Real.sqrt ℬ →
      Real.log (Entropy.surprisalMoment (hσ r).isHermitian.eigenvalues s) ≤
        s * S r + C₀ * ℬ * s ^ 2) →
    ∀ a : ℝ, 0 ≤ a → 5 * a ≤ ((min c₀ 1) / 2) / Real.sqrt ℬ →
      (Γ * NormedSpace.exp ((a : ℂ) •
        (DC + DR - physicalMergeDeficit ι m))).trace.re ≤
      ‖WithLp.toLp 2 w‖ ^ 2 * K ^ (2 / 5 : ℝ) * Real.exp
        (-a * m * (S 0 + S 2 - S 1) + 30 * C₀ * m * ℬ * a ^ 2 +
          (((Fintype.card (ι 0) : ℝ) ^ 2 + (Fintype.card (ι 1) : ℝ) ^ 2 +
            (Fintype.card (ι 2) : ℝ) ^ 2) / 10) * Real.log (m + 1)) := by
  classical
  intro Ωr σ hσ S m Γ F DC DR K w hmgf a ha hsize
  let M : ℝ := ‖WithLp.toLp 2 w‖ ^ 2
  let bp (r : Fin 3) (t : ℝ) :=
    t * m * S r + 2 * C₀ * m * ℬ * t ^ 2 +
      ((Fintype.card (ι r.castSucc.castSucc) : ℝ) ^ 2 / 2) * Real.log (m + 1)
  let A : Fin 5 → Matrix (Config m ι) (Config m ι) ℂ :=
    ![(1 / 2 : ℂ) • (DC + DR), (1 / 2 : ℂ) • (DC + DR), -F {0}, -F {2}, F {1}]
  let b : Fin 5 → ℝ :=
    ![Real.log K, Real.log K, bp 0 (-(5 * a)), bp 2 (-(5 * a)), bp 1 (5 * a)]
  have hΓ : Γ.PosSemidef :=
    (posSemidef_vecMulVec_self_star (R := ℂ) _).partialTraceRight
  have hM : 0 ≤ M := sq_nonneg _
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hsqrt : 1 ≤ Real.sqrt ℬ := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hℬ
  have hsqrtPos : 0 < Real.sqrt ℬ := lt_of_lt_of_le (by norm_num) hsqrt
  have hsmall : ((min c₀ 1) / 2) / Real.sqrt ℬ ≤ 1 / 2 :=
    (div_le_iff₀ hsqrtPos).mpr (by nlinarith [min_le_right c₀ (1 : ℝ)])
  have ha5 : 0 ≤ 5 * a := mul_nonneg (by norm_num) ha
  have ha5le : 5 * a ≤ 1 := (hsize.trans hsmall).trans (by norm_num)
  have htPos : |5 * a| ≤ ((min c₀ 1) / 2) / Real.sqrt ℬ := by
    rwa [abs_of_nonneg ha5]
  have htNeg : |-(5 * a)| ≤ ((min c₀ 1) / 2) / Real.sqrt ℬ := by
    rwa [abs_neg]
  have hphys (r : Fin 3) (t : ℝ)
      (ht : |t| ≤ ((min c₀ 1) / 2) / Real.sqrt ℬ) :
      (Γ * NormedSpace.exp ((t : ℂ) • F {r.castSucc.castSucc})).trace.re ≤
        M * Real.exp (bp r t) := by
    have h := re_trace_mul_exp_centered_labelEntropy_replicaGoodConfigurationMarginal_le
      ι Ω hΩ k B u r C₀ c₀ ℬ hC hc hℬ (hmgf r) t ht
    change (Γ * NormedSpace.exp ((t : ℂ) •
      (F {r.castSucc.castSucc} - ((m : ℝ) * S r : ℂ) • 1))).trace.re ≤
        M * Real.exp (2 * C₀ * m * ℬ * t ^ 2 +
          ((Fintype.card (ι r.castSucc.castSucc) : ℝ) ^ 2 / 2) * Real.log (m + 1)) at h
    rw [← Complex.ofReal_mul, re_trace_exp_centered] at h
    have he : Real.exp (t * (m * S r)) * Real.exp (-t * (m * S r)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      _ = Real.exp (t * (m * S r)) *
          (Real.exp (-t * (m * S r)) *
            (Γ * NormedSpace.exp ((t : ℂ) • F {r.castSucc.castSucc})).trace.re) := by
        rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (t * (m * S r)) * (M * Real.exp
          (2 * C₀ * m * ℬ * t ^ 2 +
            ((Fintype.card (ι r.castSucc.castSucc) : ℝ) ^ 2 / 2) * Real.log (m + 1))) :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = M * (Real.exp (t * (m * S r)) * Real.exp
          (2 * C₀ * m * ℬ * t ^ 2 +
            ((Fintype.card (ι r.castSucc.castSucc) : ℝ) ^ 2 / 2) * Real.log (m + 1))) := by
        ring
      _ = M * Real.exp (t * (m * S r) +
          (2 * C₀ * m * ℬ * t ^ 2 +
            ((Fintype.card (ι r.castSucc.castSucc) : ℝ) ^ 2 / 2) * Real.log (m + 1))) := by
        simp only [Real.exp_add]
      _ = _ := by
        dsimp only [bp]
        congr 2
        ring
  have hhalf : ((5 * a : ℝ) : ℂ) • ((1 / 2 : ℂ) • (DC + DR)) =
      ((5 * a / 2 : ℝ) : ℂ) • (DC + DR) := by
    rw [smul_smul]
    congr 1
    push_cast
    ring
  have hmerge :
      (Γ * NormedSpace.exp (((5 * a : ℝ) : ℂ) • ((1 / 2 : ℂ) • (DC + DR)))).trace.re ≤
        M * Real.exp (Real.log K) := by
    rw [hhalf, Real.exp_log hK]
    simpa only [M, mul_comm] using
      (replicaGoodConfigurationMarginal_exp_sum_mergeDeficit_le
        ι Ω hΩ k B u hu (5 * a / 2) (by linarith))
  have hF (T : Finset (Fin 5)) : (F T).IsHermitian := isHermitian_labelObservable _ _
  have hH : (DC + DR).IsHermitian :=
    (((hF {0}).add (hF {3})).sub (hF {0, 3})).add
      (((hF {2}).add (hF {4})).sub (hF {2, 4}))
  have hA : ∀ i, (A i).IsHermitian := by
    intro i
    fin_cases i
    · simpa [A] using hH.smul
        (show IsSelfAdjoint (1 / 2 : ℂ) from by simp [IsSelfAdjoint])
    · simpa [A] using hH.smul
        (show IsSelfAdjoint (1 / 2 : ℂ) from by simp [IsSelfAdjoint])
    · simpa [A] using (hF {0}).neg
    · simpa [A] using (hF {2}).neg
    · simpa [A] using hF {1}
  -- All seven regions are nested or disjoint, so the five observables commute.
  have hcomm : ∀ i j, Commute (A i) (A j) :=
    TensorPower.commute_half_sum_labelEntropy_components ι m
  have hb : ∀ i, (Γ * NormedSpace.exp (((5 * a : ℝ) : ℂ) • A i)).trace.re ≤
      M * Real.exp (b i) := by
    intro i
    fin_cases i
    · simpa [A, b] using hmerge
    · simpa [A, b] using hmerge
    · simpa [A, b, smul_neg, Complex.ofReal_neg, neg_smul] using hphys 0 (-(5 * a)) htNeg
    · simpa [A, b, smul_neg, Complex.ofReal_neg, neg_smul] using hphys 2 (-(5 * a)) htNeg
    · simpa [A, b] using hphys 1 (5 * a) htPos
  have hsum : ∑ i, A i = DC + DR - physicalMergeDeficit ι m := by
    simp [A, Fin.sum_univ_succ, physicalMergeDeficit, F]
    module
  have h := re_trace_exp_le_of_five_moment_bounds hΓ A hA hcomm a hM b hb
  rw [hsum] at h
  have hbsum : (∑ i, b i) / 5 = (2 / 5) * Real.log K +
      (-a * m * (S 0 + S 2 - S 1) + 30 * C₀ * m * ℬ * a ^ 2 +
        (((Fintype.card (ι 0) : ℝ) ^ 2 + (Fintype.card (ι 1) : ℝ) ^ 2 +
          (Fintype.card (ι 2) : ℝ) ^ 2) / 10) * Real.log (m + 1)) := by
    simp [b, bp, Fin.sum_univ_succ]
    ring
  have hpow : Real.exp ((2 / 5) * Real.log K) = K ^ (2 / 5 : ℝ) := by
    rw [Real.rpow_def_of_pos hK]
    congr 1
    ring
  rw [hbsum, Real.exp_add, hpow] at h
  simpa only [M, mul_assoc] using h

end Matrix
