/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PolarUnitaryCorrectionKronecker

/-! Axiom dependencies of spectator-preserving polar correction. -/

set_option linter.hashCommand false

/--
info: 'Matrix.unitary_polar_correction_kronecker_one' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.unitary_polar_correction_kronecker_one
