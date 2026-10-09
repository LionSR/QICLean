/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.StretchedBallKernel

/-! Literal shell amplitudes, anchor multiplicity, and the calibrated row estimate. -/

open scoped BigOperators ENNReal NNReal

namespace StretchedBallKernelTest

example {ι κ : Type*} [Fintype ι] [PseudoEMetricSpace κ]
    (anchor : ι → κ) (c α : ℝ) (y z : κ) :
    Metric.stretchedBallKernel anchor 0 c α y z = 0 := by
  simp [Metric.stretchedBallKernel]

-- Three coincident labels contribute three copies, including the radius-zero term.
example (C c α : ℝ) :
    Metric.stretchedBallKernel (fun _ : Fin 3 ↦ ()) C c α () () =
      (3 * C) * ∑' n : ℕ, Real.exp (-c * (n : ℝ) ^ α) := by
  rw [Metric.stretchedBallKernel, ← tsum_mul_left]
  congr 1
  funext n
  have h : Metric.ballIncidenceKernel (fun _ : Fin 3 ↦ ()) (n : ℝ≥0) () () = 3 := by
    simp [Metric.ballIncidenceKernel]
  rw [h]
  ring

-- The concrete small positive weight leaves exactly half of the radial decay rate.
example {C c α : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hα : 0 < α) :
    0 < c / (2 * 2 ^ α) ∧
      Metric.stretchedBallKernel (fun _ : Fin 3 ↦ ()) C c α () () ≤
        3 * C * ∑' n : ℕ, (1 + (n : ℝ)) ^ 4 *
          Real.exp (-(c / 2) * (n : ℝ) ^ α) := by
  have hbase (n : ℕ) : (1 : ℝ) ≤ (1 + (n : ℝ)) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
  have h := Metric.sum_stretchedBallKernel_mul_exp_half_rate_le
    (fun _ : Fin 3 ↦ ()) hC hc hα (B := 3) (V := 1) (by norm_num) (by norm_num)
    (by
      intro n y
      cases y
      simpa using mul_le_mul_of_nonneg_left (hbase n) (by norm_num : (0 : ℝ) ≤ 3))
    (fun n _ ↦ by simpa using hbase n)
  refine ⟨h.1, ?_⟩
  simpa [Real.zero_rpow hα.ne', mul_comm] using h.2 ()

-- Empty labels give a zero row bound on every finite site space, for nonzero amplitude.
example {κ : Type*} [Fintype κ] [PseudoEMetricSpace κ] {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α) :
    0 < c / (2 * 2 ^ α) ∧ ∀ y : κ,
      (∑ z : κ, Metric.stretchedBallKernel (fun i : Fin 0 ↦ (Fin.elim0 i : κ)) 7 c α y z *
        Real.exp ((c / (2 * 2 ^ α)) * (edist y z).toReal ^ α)) ≤ 0 := by
  have h := Metric.sum_stretchedBallKernel_mul_exp_half_rate_le
    (fun i : Fin 0 ↦ (Fin.elim0 i : κ)) (C := 7) (B := 0) (V := 0)
    (by norm_num) hc hα le_rfl le_rfl
    (fun _ _ ↦ by simp) (fun _ i ↦ Fin.elim0 i)
  simpa using h

end StretchedBallKernelTest
