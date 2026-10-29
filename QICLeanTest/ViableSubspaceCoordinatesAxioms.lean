/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceCoordinates

/-! # Axiom check for viable subspaces in coordinates -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Submodule.isCloseTo_map_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Submodule.isCloseTo_map_iff

/-- info:
'Submodule.prodExt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Submodule.prodExt

/-- info:
'Submodule.euclideanTensorEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Submodule.euclideanTensorEquiv

/-- info:
'Submodule.map_prodExt_euclideanTensorEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Submodule.map_prodExt_euclideanTensorEquiv

/-- info:
'Submodule.isCloseTo_prodExt_iff_isViable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Submodule.isCloseTo_prodExt_iff_isViable
