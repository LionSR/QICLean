/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.LeafMeasure

/-! Stock-axiom regression expectations for the literal transport measures. -/

namespace TensorPower

/--
info: 'TensorPower.coherentSphereMap'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms coherentSphereMap

/--
info: 'TensorPower.coherentMeasure'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms coherentMeasure

/--
info: 'TensorPower.isFiniteMeasure_coherentMeasure'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms isFiniteMeasure_coherentMeasure

/--
info: 'TensorPower.integral_coherentMeasure'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integral_coherentMeasure

/--
info: 'TensorPower.coherentMeasure_real_univ'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms coherentMeasure_real_univ

/--
info: 'TensorPower.coherentMeasure_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms coherentMeasure_zero

namespace ReplicaTransport.TransportData

/--
info: 'TensorPower.ReplicaTransport.TransportData.transportLeafMeasure'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms transportLeafMeasure

/--
info: 'TensorPower.ReplicaTransport.TransportData.measurable_transportLeafDensity'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms measurable_transportLeafDensity

/--
info: 'TensorPower.ReplicaTransport.TransportData.integrable_transportLeafDensity_mul'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrable_transportLeafDensity_mul

/--
info: 'TensorPower.ReplicaTransport.TransportData.integrable_transportLeafDensity'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integrable_transportLeafDensity

/--
info: 'TensorPower.ReplicaTransport.TransportData.isFiniteMeasure_transportLeafMeasure'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms isFiniteMeasure_transportLeafMeasure

/--
info: 'TensorPower.ReplicaTransport.TransportData.transportLeafDensity_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms transportLeafDensity_nonneg

/--
info: 'TensorPower.ReplicaTransport.TransportData.integral_transportLeafMeasure'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms integral_transportLeafMeasure

/--
info: 'TensorPower.ReplicaTransport.TransportData.transportLeafMeasure_zero_pre'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms transportLeafMeasure_zero_pre

/--
info: 'TensorPower.ReplicaTransport.TransportData.transportLeafMeasure_new_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms transportLeafMeasure_new_zero

/--
info: 'TensorPower.ReplicaTransport.TransportData.transportLeafMeasure_old_one'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms transportLeafMeasure_old_one

/--
info: 'TensorPower.ReplicaTransport.TransportData.transportLeafMeasure_real_univ'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms transportLeafMeasure_real_univ

/--
info: 'TensorPower.ReplicaTransport.TransportData.transportLeafMeasure_real_univ_eq_ite'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms transportLeafMeasure_real_univ_eq_ite

end ReplicaTransport.TransportData

end TensorPower
