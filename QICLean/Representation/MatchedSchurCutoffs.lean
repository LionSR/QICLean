/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SupportedSubsystemLabelDimension
import QICLean.Representation.MergeDimensions
import QICLean.Entropy.MarginalTails
import Mathlib.Data.Finset.SymmDiff

/-!
# Transferring the cutoff from one matched physical region

For two regions comparable by inclusion, the compatible-label dimension
inequalities bound either logarithmic label by the other plus the copy
number times the logarithmic dimension of their difference. Consequently
the actual closed cutoff on the matched region is contained in the actual
cutoff on the target region at the enlarged threshold.

Only the two matched regions occur in this argument. In particular, the
target label is not assumed to commute with all the other cutoffs used to
construct a vector. An arbitrary spectator factor may be retained, so the
result applies to the same Bell-range common-cutoff vector without changing
that vector or its selected auxiliary label.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, Lemma 6.1(3), lines 105–111,
  and `07-comparators.tex`, lines 356–365, `comparator:actual-cutoffs`,
  manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix Kronecker symmDiff
open Matrix PermutationRepresentation

noncomputable section

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (k : ℕ)

/-- On every nonzero joint block of nested regions, either label is bounded
by the other and the actual difference-region dimension. The difference
label is obtained by the identity resolution, not supplied as a premise. -/
private theorem log_dim_bounds_of_subset {S U : Finset F} (hSU : S ⊆ U)
    {l ν : IrrepLabel (Equiv.Perm (Fin k))}
    (hp : labelProj (subsystemPerm k ι S) l *
      labelProj (subsystemPerm k ι U) ν ≠ 0) :
    Real.log ν.dim ≤ Real.log l.dim +
        (k : ℝ) * Real.log (Fintype.card (FiniteProduct.Configuration ι (U \ S))) ∧
      Real.log l.dim ≤ Real.log ν.dim +
        (k : ℝ) * Real.log (Fintype.card (FiniteProduct.Configuration ι (U \ S))) := by
  classical
  have hsum : (∑ μ : IrrepLabel (Equiv.Perm (Fin k)),
      labelProj (subsystemPerm k ι S) l * labelProj (subsystemPerm k ι (U \ S)) μ *
        labelProj (subsystemPerm k ι U) ν) =
      labelProj (subsystemPerm k ι S) l * labelProj (subsystemPerm k ι U) ν := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_labelProj, mul_one]
  obtain ⟨μ, hμ⟩ : ∃ μ : IrrepLabel (Equiv.Perm (Fin k)),
      labelProj (subsystemPerm k ι S) l * labelProj (subsystemPerm k ι (U \ S)) μ *
        labelProj (subsystemPerm k ι U) ν ≠ 0 := by
    by_contra! hzero
    apply hp
    rw [← hsum]
    exact Finset.sum_eq_zero fun μ _ ↦ hzero μ
  have hμproj : labelProj (subsystemPerm k ι (U \ S)) μ ≠ 0 := by
    intro hzero
    exact hμ (by rw [hzero, mul_zero, zero_mul])
  have hdim := merge_dim_le (ι := ι) (k := k)
    (Q := S) (E := U \ S) Finset.disjoint_sdiff
    (l := l) (μ := μ) (ν := ν)
    (by simpa only [Finset.union_sdiff_of_subset hSU] using hμ)
  have hl : (0 : ℝ) < l.dim := Nat.cast_pos.mpr l.dim_pos
  have hm : (0 : ℝ) < μ.dim := Nat.cast_pos.mpr μ.dim_pos
  have hn : (0 : ℝ) < ν.dim := Nat.cast_pos.mpr ν.dim_pos
  have hμlog : Real.log μ.dim ≤
      (k : ℝ) * Real.log (Fintype.card (FiniteProduct.Configuration ι (U \ S))) := by
    have hd : (μ.dim : ℝ) ≤
        (Fintype.card (FiniteProduct.Configuration ι (U \ S)) : ℝ) ^ k := by
      exact_mod_cast dim_le_pow_card_of_subsystem_labelProj_ne_zero ι k (U \ S) μ hμproj
    simpa only [Real.log_pow] using Real.log_le_log hm hd
  have hlarge := Real.log_le_log hn
    (show (ν.dim : ℝ) ≤ (l.dim : ℝ) * μ.dim by exact_mod_cast hdim.1)
  have hsmall := Real.log_le_log hl
    (show (l.dim : ℝ) ≤ (ν.dim : ℝ) * μ.dim by exact_mod_cast hdim.2)
  rw [Real.log_mul hl.ne' hm.ne'] at hlarge
  rw [Real.log_mul hn.ne' hm.ne'] at hsmall
  constructor <;> linarith

/-- For comparable physical regions, the actual cutoff of the matched
region is contained in the target cutoff after the explicit difference
dimension is added to its threshold. No commutation with other regions is
assumed. Source: `07-comparators.tex`, lines 356–365,
`comparator:actual-cutoffs`. -/
theorem labelCutoff_subsystemPerm_mul_of_nested {B Q : Finset F}
    (hnested : B ⊆ Q ∨ Q ⊆ B) {a t : ℝ}
    (ht : a + (k : ℝ) *
      Real.log (Fintype.card (FiniteProduct.Configuration ι (B ∆ Q))) ≤ t) :
    labelCutoff (subsystemPerm k ι Q) t * labelCutoff (subsystemPerm k ι B) a =
      labelCutoff (subsystemPerm k ι B) a := by
  classical
  have hc : ∀ l ν : IrrepLabel (Equiv.Perm (Fin k)),
      Commute (labelProj (subsystemPerm k ι B) l)
        (labelProj (subsystemPerm k ι Q) ν) := by
    intro l ν
    exact hnested.elim
      (fun h ↦ commute_labelProj_subsystemPerm_of_subset ι k h l ν)
      (fun h ↦ (commute_labelProj_subsystemPerm_of_subset ι k h ν l).symm)
  have hlog : ∀ l ν : IrrepLabel (Equiv.Perm (Fin k)),
      labelProj (subsystemPerm k ι B) l * labelProj (subsystemPerm k ι Q) ν ≠ 0 →
      Real.log ν.dim ≤ Real.log l.dim + (k : ℝ) *
        Real.log (Fintype.card (FiniteProduct.Configuration ι (B ∆ Q))) := by
    intro l ν hp
    rcases hnested with h | h
    · have hd : B ∆ Q = Q \ B := by
        rw [Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.empty_union]
      simpa only [hd] using (log_dim_bounds_of_subset ι k h hp).1
    · have hd : B ∆ Q = B \ Q := by
        rw [Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.union_empty]
      have hp' : labelProj (subsystemPerm k ι Q) ν *
          labelProj (subsystemPerm k ι B) l ≠ 0 := by
        rw [← (hc l ν).eq]
        exact hp
      simpa only [hd] using (log_dim_bounds_of_subset ι k h hp').2
  have hfix : ∀ l : IrrepLabel (Equiv.Perm (Fin k)), Real.log l.dim ≤ a →
      labelCutoff (subsystemPerm k ι Q) t * labelProj (subsystemPerm k ι B) l =
        labelProj (subsystemPerm k ι B) l := by
    intro l hl
    calc
      labelCutoff (subsystemPerm k ι Q) t * labelProj (subsystemPerm k ι B) l =
          ∑ ν : IrrepLabel (Equiv.Perm (Fin k)),
            labelProj (subsystemPerm k ι Q) ν * labelProj (subsystemPerm k ι B) l := by
        rw [labelCutoff, labelObservable, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ν _
        rw [smul_mul_assoc]
        by_cases hp : labelProj (subsystemPerm k ι Q) ν *
            labelProj (subsystemPerm k ι B) l = 0
        · simp only [hp, smul_zero]
        · have hp' : labelProj (subsystemPerm k ι B) l *
              labelProj (subsystemPerm k ι Q) ν ≠ 0 := by
            rw [(hc l ν).eq]
            exact hp
          have hν : Real.log ν.dim ≤ t :=
            (hlog l ν hp').trans ((add_le_add hl le_rfl).trans ht)
          simp only [ite_eq_left hν, Complex.ofReal_one, one_smul]
      _ = labelProj (subsystemPerm k ι B) l := by
        rw [← Finset.sum_mul, sum_labelProj, one_mul]
  rw [show labelCutoff (subsystemPerm k ι B) a =
    ∑ l : IrrepLabel (Equiv.Perm (Fin k)),
      ((if Real.log l.dim ≤ a then 1 else 0 : ℝ) : ℂ) •
        labelProj (subsystemPerm k ι B) l from rfl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_smul_comm]
  by_cases hl : Real.log l.dim ≤ a
  · simpa only [ite_eq_left hl, Complex.ofReal_one, one_smul] using hfix l hl
  · simp only [ite_eq_right hl, Complex.ofReal_zero, zero_smul]

/-- The same vector fixed by a matched physical cutoff is fixed by the
actual enlarged target cutoff. An arbitrary unchanged spectator factor
includes the selected Bell system. The two scalar bounds are exactly
those used in `comparator:actual-cutoffs`, `07-comparators.tex`, lines
356–365. No relation with any other imposed cutoff is required. -/
theorem toEuclideanLin_labelCutoff_of_matched
    {D : Type*} [Fintype D] [DecidableEq D] {B Q : Finset F}
    (hnested : B ⊆ Q ∨ Q ⊆ B) {s z Bsh Bexc : ℝ}
    (hz : 0 < z) (hsh : s ≤ Bsh)
    (hexc : 1 + Real.log (Fintype.card (FiniteProduct.Configuration ι (B ∆ Q))) ≤ Bexc)
    (φ : EuclideanSpace ℂ (D × Config k ι))
    (hφ : toEuclideanLin
      ((1 : Matrix D D ℂ) ⊗ₖ labelCutoff (subsystemPerm k ι B) ((k : ℝ) * (s / z + 1)))
        φ = φ) :
    toEuclideanLin
      ((1 : Matrix D D ℂ) ⊗ₖ
        labelCutoff (subsystemPerm k ι Q) ((k : ℝ) * (Bsh / z + Bexc))) φ = φ := by
  have hthreshold : (k : ℝ) * (s / z + 1) + (k : ℝ) *
      Real.log (Fintype.card (FiniteProduct.Configuration ι (B ∆ Q))) ≤
        (k : ℝ) * (Bsh / z + Bexc) := by
    calc
      _ = (k : ℝ) * (s / z +
          (1 + Real.log (Fintype.card (FiniteProduct.Configuration ι (B ∆ Q))))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_right hsh hz.le) hexc) (Nat.cast_nonneg k)
  have hmul := labelCutoff_subsystemPerm_mul_of_nested ι k hnested hthreshold
  have hmul' :
      ((1 : Matrix D D ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι Q) ((k : ℝ) * (Bsh / z + Bexc))) *
        ((1 : Matrix D D ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι B) ((k : ℝ) * (s / z + 1))) =
        (1 : Matrix D D ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι B) ((k : ℝ) * (s / z + 1)) := by
    rw [← mul_kronecker_mul, one_mul, hmul]
  calc
    _ = toEuclideanLin
        ((1 : Matrix D D ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι Q) ((k : ℝ) * (Bsh / z + Bexc)))
        (toEuclideanLin
          ((1 : Matrix D D ℂ) ⊗ₖ
            labelCutoff (subsystemPerm k ι B) ((k : ℝ) * (s / z + 1))) φ) := by rw [hφ]
    _ = φ := by rw [← Entropy.toEuclideanLin_mul_apply, hmul', hφ]

end TensorPower
