/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GroundProjection
import QICLean.Analysis.PowerSpectralFilter

/-! # Axiom guards for power approximations and the global-gap ground projection -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.IsHermitian.power_approximates_isolated_energy_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsHermitian.power_approximates_isolated_energy_projection

/-- info:
'Matrix.IsHermitian.norm_power_sub_projection_le_of_log_threshold'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsHermitian.norm_power_sub_projection_le_of_log_threshold

/-- info:
'Matrix.IsHermitian.complement_spectralProjectionGE_eq_rankOne'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.IsHermitian.complement_spectralProjectionGE_eq_rankOne
