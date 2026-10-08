/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TaggedInterleavings

/-! Foundational-axiom guards for every public tagged-interleaving declaration. -/

/--
info: 'TaggedInterleavings.taggedInterleavings' depends on axioms:
[propext]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaggedInterleavings.taggedInterleavings

/--
info: 'TaggedInterleavings.mem_taggedInterleavings_iff' depends on axioms:
[propext, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaggedInterleavings.mem_taggedInterleavings_iff

/--
info: 'TaggedInterleavings.nodup_taggedInterleavings' depends on axioms:
[propext, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaggedInterleavings.nodup_taggedInterleavings

/--
info: 'TaggedInterleavings.length_taggedInterleavings' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaggedInterleavings.length_taggedInterleavings

/--
info: 'TaggedInterleavings.length_filterMap_add' depends on axioms:
[propext]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaggedInterleavings.length_filterMap_add

/--
info: 'TaggedInterleavings.length_of_mem_taggedInterleavings' depends on axioms:
[propext, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TaggedInterleavings.length_of_mem_taggedInterleavings
