/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PhysicalPowerFilterLowerGap

/-!
# Axiom checks and boundary cases for the lower-gap power estimate

The first application includes power zero. The second supplies an actual empty
interaction family on a one-dimensional Hilbert space and a gap lower bound
strictly larger than N-E₀=1, at every natural power.
-/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.power_filter_exp_spec_of_posSemidef_terms'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.power_filter_exp_spec_of_posSemidef_terms

/-- info:
'Matrix.norm_power_filter_sub_ground_le_of_lower_gap_log_threshold'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_power_filter_sub_ground_le_of_lower_gap_log_threshold

/-- info:
'Matrix.norm_power_filter_sub_ground_le_at_lower_gap_ceil'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.norm_power_filter_sub_ground_le_at_lower_gap_ceil

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

/-- The zero power satisfies the error bound one, including when the lower gap
exceeds the entire available spectral interval. -/
private theorem zero_power_boundary
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (h : κ → Matrix ι ι ℂ)
    (hpos : ∀ i, (h i).PosSemidef) (hupper : ∀ i, h i ≤ 1)
    {E0 Δ : ℝ} {Ω : EuclideanSpace ℂ ι}
    (hΩ : ‖Ω‖ = 1)
    (hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (E0 : ℂ) • WithLp.ofLp Ω)
    (hgap : ((∑ i, h i) - (E0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hΔ : 0 < Δ) :
    ‖(1 : Matrix ι ι ℂ) - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤ 1 := by
  simpa using (power_filter_exp_spec_of_posSemidef_terms h hpos hupper
    hΩ hHΩ hgap hΔ 0).2.2.2.1

/-- An empty interaction family on a one-dimensional state space admits every
positive gap lower bound. In particular, a gap greater than N-E0=1 is allowed. -/
private theorem empty_terms_large_gap_boundary
    (Δ : ℝ) (hΔ : 1 < Δ) (m : ℕ) :
    let Ω : EuclideanSpace ℂ Unit := PiLp.single 2 () 1
    ‖(1 : Matrix Unit Unit ℂ) ^ m -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
        Real.exp (-(m : ℝ) * Δ) := by
  let Ω : EuclideanSpace ℂ Unit := PiLp.single 2 () 1
  let h : Empty → Matrix Unit Unit ℂ := fun i => nomatch i
  have hΩ : ‖Ω‖ = 1 := by simp [Ω]
  have hP : vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) =
      (1 : Matrix Unit Unit ℂ) := by
    ext i j
    cases i
    cases j
    simp [Ω, vecMulVec]
  have hHΩ : (∑ i, h i) *ᵥ WithLp.ofLp Ω = (0 : ℂ) • WithLp.ofLp Ω := by
    simp
  have hgap : ((∑ i, h i) - (0 : ℂ) • 1 - (Δ : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    simpa [hP] using (PosSemidef.zero : (0 : Matrix Unit Unit ℂ).PosSemidef)
  have result := (power_filter_exp_spec_of_posSemidef_terms h
    (fun i => nomatch i) (fun i => nomatch i) hΩ hHΩ hgap
    (lt_trans zero_lt_one hΔ) m).2.2.2.1
  simpa [h, Ω] using result

end Matrix
