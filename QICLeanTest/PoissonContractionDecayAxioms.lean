/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PoissonContractionDecay

/-! Standard-axiom guards for the actual Poissonized decay assembly. -/

/-- info: 'Matrix.poissonContractionWordEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
#print axioms Matrix.poissonContractionWordEnergy

/-- info: 'Matrix.poissonContractionWordEnergy_integrable_and_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
#print axioms Matrix.poissonContractionWordEnergy_integrable_and_le

/-- info: 'Matrix.poissonContractionWord_excitedProjection_decay' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
#print axioms Matrix.poissonContractionWord_excitedProjection_decay
