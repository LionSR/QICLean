/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtReindex

/-! # Axiom audit for separate local coordinate changes -/

/-- info:
'Matrix.operatorSchmidtRank_reindex_prodCongr' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.operatorSchmidtRank_reindex_prodCongr

/-- info:
'Matrix.operatorSchmidtRank_reindex_prodProdProdComm_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option linter.hashCommand false in
#print axioms Matrix.operatorSchmidtRank_reindex_prodProdProdComm_le
