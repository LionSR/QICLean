/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.FiniteProductOperatorSchmidt

/-! # Axiom audits for finite partition comparisons -/

/-- info:
'Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_le

/-- info:
'Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_finset_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.operatorSchmidtRank_reindex_piEquivPiSubtypeProd_finset_le

/-- info:
'FiniteProduct.operatorSchmidtRank_splitEquiv_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms FiniteProduct.operatorSchmidtRank_splitEquiv_le
