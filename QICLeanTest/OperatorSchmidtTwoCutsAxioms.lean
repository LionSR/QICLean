/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtTwoCuts

/-! # Axiom check and empty and one-dimensional factor applications -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.operatorSchmidtRank_middle_le_mul'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.operatorSchmidtRank_middle_le_mul

namespace Matrix

private def middleCut {l m n : Type*}
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) :
    Matrix (m × (l × n)) (m × (l × n)) ℂ :=
  fun i j ↦ ρ ((i.2.1, i.1), i.2.2) ((j.2.1, j.1), j.2.2)

example {l n : Type*} [Fintype l] [Finite n]
    (ρ : Matrix ((l × Empty) × n) ((l × Empty) × n) ℂ) :
    operatorSchmidtRank (middleCut ρ) ≤
      operatorSchmidtRank (ρ.reindex (Equiv.prodAssoc l Empty n)
        (Equiv.prodAssoc l Empty n)) * operatorSchmidtRank ρ :=
  operatorSchmidtRank_middle_le_mul ρ

example {l n : Type*} [Fintype l] [Finite n]
    (ρ : Matrix ((l × PUnit) × n) ((l × PUnit) × n) ℂ) :
    operatorSchmidtRank (middleCut ρ) ≤
      operatorSchmidtRank (ρ.reindex (Equiv.prodAssoc l PUnit n)
        (Equiv.prodAssoc l PUnit n)) * operatorSchmidtRank ρ :=
  operatorSchmidtRank_middle_le_mul ρ

example {l m : Type*} [Fintype l] [Fintype m]
    (ρ : Matrix ((l × m) × Empty) ((l × m) × Empty) ℂ) :
    operatorSchmidtRank (middleCut ρ) ≤
      operatorSchmidtRank (ρ.reindex (Equiv.prodAssoc l m Empty)
        (Equiv.prodAssoc l m Empty)) * operatorSchmidtRank ρ :=
  operatorSchmidtRank_middle_le_mul ρ

end Matrix
