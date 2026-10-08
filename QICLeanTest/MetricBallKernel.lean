/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MetricBallKernel

/-! Label multiplicity, zero-radius pseudometrics, empty families, and sharp diameter. -/

open scoped BigOperators ENNReal NNReal

namespace MetricBallKernelTest

private noncomputable abbrev collapsedSpace : PseudoEMetricSpace Bool :=
  PseudoEMetricSpace.induced (fun _ : Bool ↦ (0 : ℝ)) inferInstance

private def separatedDistance (x y : Bool) : ℝ≥0∞ := if x = y then 0 else ∞

private noncomputable abbrev separatedSpace : PseudoEMetricSpace Bool :=
  PseudoEMetricSpace.ofEDist separatedDistance
    (fun x ↦ by simp [separatedDistance])
    (fun x y ↦ by simp [separatedDistance, eq_comm])
    (fun x y z ↦ by cases x <;> cases y <;> cases z <;> simp [separatedDistance])

-- Three coincident anchors are three labels, including at radius zero.
example :
    Metric.ballIncidenceKernel (fun _ : Fin 3 ↦ ()) 0 () () = 3 ∧
      (∑ z : Unit, Metric.ballIncidenceKernel (fun _ : Fin 3 ↦ ()) 0 () z *
        Real.exp (1 * (edist () z).toReal ^ (1 : ℝ))) ≤ 3 := by
  constructor
  · simp [Metric.ballIncidenceKernel]
  · have h := Metric.sum_ballIncidenceKernel_mul_exp_le
      (fun _ : Fin 3 ↦ ()) 0 (a := 1) (α := 1) (B := 3) (V := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) ()
      (by simp) (fun _ ↦ by simp)
    simpa using h

-- Distinct sites at zero pseudodistance belong to the same radius-zero ball.
example :
    letI := collapsedSpace
    0 ≤ Metric.ballIncidenceKernel (fun _ : Unit ↦ false) 0 false true ∧
      Metric.ballIncidenceKernel (fun _ : Unit ↦ false) 0 false true = 1 := by
  let _ := collapsedSpace
  have hdist (x y : Bool) : edist x y = 0 := by
    change edist (0 : ℝ) 0 = 0
    exact edist_self _
  exact ⟨Metric.ballIncidenceKernel_nonneg _ _ _ _, by
    simp [Metric.ballIncidenceKernel, hdist]⟩

-- Empty anchor families vanish on arbitrary pseudoemetric spaces.
example {κ : Type*} [PseudoEMetricSpace κ] (r : ℝ≥0) (y z : κ) :
    Metric.ballIncidenceKernel (fun i : Fin 0 ↦ Fin.elim0 i) r y z = 0 := by
  simp [Metric.ballIncidenceKernel]

-- The entry estimate counts coincident labels, not distinct anchor positions.
example :
    Metric.ballIncidenceKernel (fun _ : Fin 3 ↦ ()) 0 () () ≤ 3 := by
  simpa using
    Metric.ballIncidenceKernel_le_card_labels (fun _ : Fin 3 ↦ ()) 0 () ()

-- The endpoints -1 and 1 are in the radius-one ball about zero and are distance two apart.
example :
    edist (-1 : ℝ) 1 ≠ ∞ ∧ (edist (-1 : ℝ) 1).toReal = 2 ∧
      (edist (-1 : ℝ) 1).toReal ≤ 2 * (1 : ℝ) := by
  have h := Metric.edist_ne_top_and_toReal_le_two_mul_of_ball_bounds
    (x := (0 : ℝ)) (y := (-1 : ℝ)) (z := (1 : ℝ)) (r := 1)
    (by norm_num [edist_dist, Real.dist_eq])
    (by norm_num [edist_dist, Real.dist_eq])
  exact ⟨h.1, by norm_num [edist_dist, Real.dist_eq], h.2⟩

-- An infinite-distance component is never joined by a finite-radius ball.
example (r : ℝ≥0) :
    letI := separatedSpace
    Metric.ballIncidenceKernel (fun b : Bool ↦ b) r false true = 0 := by
  let _ := separatedSpace
  apply Metric.ballIncidenceKernel_eq_zero_of_edist_eq_top
  rfl

-- At radius zero the alpha-zero weight is exp(2), whereas alpha-one gives one.
example :
    (∑ z : Unit, Metric.ballIncidenceKernel (fun _ : Fin 3 ↦ ()) 0 () z *
      Real.exp (2 * (edist () z).toReal ^ (0 : ℝ))) = 3 * Real.exp 2 ∧
      (∑ z : Unit, Metric.ballIncidenceKernel (fun _ : Fin 3 ↦ ()) 0 () z *
        Real.exp (2 * (edist () z).toReal ^ (1 : ℝ))) = 3 := by
  simp [Metric.ballIncidenceKernel]

end MetricBallKernelTest
