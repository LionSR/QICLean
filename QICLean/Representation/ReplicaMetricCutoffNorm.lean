/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSimilarity
import QICLean.Representation.SchurLabelTails

/-!
# Replica metrics on a Schur-label cutoff

The replica weights are those of the original full system. Their existing
labelwise logarithmic comparison bounds the metric by a polynomial in the
copy number. On the closed cutoff F_Q ≤ T, the inverse metric has the same
polynomial bound multiplied by exp(t T). The threshold is arbitrary and the
copy number may be zero.

The finite coordinate set of each original register is assumed nonempty.
No vector, normalization, coefficient estimate, or metric estimate is supplied
as a hypothesis. The polynomial exponent is derived from the actual replica
weights and is uniform in the subsystem and cutoff threshold. In particular,
restricting a later argument to Bell coordinates does not replace these
weights by weights padded to a smaller system dimension.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, Lemma 6.2,
  `replicas:W-comparison`, lines 305–316; and `07-comparators.tex`,
  lines 367–373, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Matrix PermutationRepresentation
open scoped Matrix.Norms.L2Operator

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)]

/-- A single polynomial bounds the actual replica metric and its inverse on
every closed Schur-label cutoff. The exponent depends on the original full
system and on t, but not on the copy number, subsystem, or cutoff threshold.
The case of zero copies and negative thresholds is included.

Source: OpenAI area-law manuscript, Lemma 6.2, `replicas:W-comparison`,
`05-replicas.tex`, lines 305–316; rough upper comparison,
`07-comparators.tex`, lines 367–373. -/
theorem exists_replicaMetric_cutoff_norm_bound {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (Q : Finset F),
      ‖replicaMetric ι t k Q‖ ≤ ((k : ℝ) + 2) ^ C ∧
      ∀ T : ℝ,
        ‖(replicaMetric ι t k Q)⁻¹ * labelCutoff (subsystemPerm k ι Q) T‖ ≤
          ((k : ℝ) + 2) ^ C * Real.exp (t * T) := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_abs_log_replicaLabelWeight_add_le ι ht
  refine ⟨C, hC0, fun k Q ↦ ?_⟩
  let R := isOrthogonalResolution_labelProj (subsystemPerm k ι Q)
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι t
  have hw (l) : 0 < w l := replicaLabelWeight_pos ι ht.le l
  have hk2 : 0 < (k : ℝ) + 2 := by positivity
  have hpoly : 0 ≤ ((k : ℝ) + 2) ^ C := Real.rpow_nonneg hk2.le _
  have hweight (l) (hl : labelProj (subsystemPerm k ι Q) l ≠ 0) :
      w l ≤ ((k : ℝ) + 2) ^ C ∧
      ∀ T : ℝ, Real.log l.dim ≤ T →
        (w l)⁻¹ ≤ ((k : ℝ) + 2) ^ C * Real.exp (t * T) := by
    have hlog : |Real.log (w l) + t * Real.log l.dim| ≤
        C * Real.log ((k : ℝ) + 2) := hC k Q l hl
    obtain ⟨hlo, hhi⟩ := abs_le.mp hlog
    have hdim : 0 ≤ Real.log (l.dim : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (Nat.succ_le_iff.mpr l.dim_pos))
    constructor
    · rw [← Real.exp_log (hw l), Real.rpow_def_of_pos hk2]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_nonneg ht.le hdim])
    · intro T hT
      calc
        (w l)⁻¹ = Real.exp (-Real.log (w l)) := by
          rw [Real.exp_neg, Real.exp_log (hw l)]
        _ ≤ Real.exp (Real.log ((k : ℝ) + 2) * C + t * T) :=
          Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hT ht.le])
        _ = ((k : ℝ) + 2) ^ C * Real.exp (t * T) := by
          rw [Real.exp_add, Real.rpow_def_of_pos hk2]
  constructor
  · rw [replicaMetric_eq_hom]
    change ‖R.hom (fun l ↦ (w l : ℂ))‖ ≤ ((k : ℝ) + 2) ^ C
    refine R.l2_opNorm_hom_le (isHermitian_labelProj _) hpoly fun l hl ↦ ?_
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw l)] using
      (hweight l hl).1
  · intro T
    have hinv : (replicaMetric ι t k Q)⁻¹ =
        R.hom (fun l ↦ (((w l)⁻¹ : ℝ) : ℂ)) := by
      change (labelObservable (subsystemPerm k ι Q) w)⁻¹ = _
      rw [labelObservable_inv _ (fun l ↦ (hw l).ne'), labelObservable_eq_hom]
    have hcut : labelCutoff (subsystemPerm k ι Q) T =
        R.hom (fun l ↦ ((if Real.log l.dim ≤ T then 1 else 0 : ℝ) : ℂ)) :=
      labelObservable_eq_hom _ _
    rw [hinv, hcut, ← map_mul]
    refine R.l2_opNorm_hom_le (isHermitian_labelProj _)
      (mul_nonneg hpoly (Real.exp_pos _).le) fun l hl ↦ ?_
    change ‖(((w l)⁻¹ : ℝ) : ℂ) *
      ((if Real.log l.dim ≤ T then 1 else 0 : ℝ) : ℂ)‖ ≤ _
    by_cases h : Real.log l.dim ≤ T
    · simpa only [ite_eq_left h, Complex.ofReal_one, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hw l))] using
        (hweight l hl).2 T h
    · simp only [ite_eq_right h, Complex.ofReal_zero, mul_zero, norm_zero]
      exact mul_nonneg hpoly (Real.exp_pos _).le

end TensorPower
