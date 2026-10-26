/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtReindex

/-! # Local permutations and empty tensor factors -/

/-- Independent nontrivial coordinate permutations on both factors. -/
example (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    Matrix.operatorSchmidtRank
        (ρ.reindex
          ((Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.swap (0 : Fin 3) 2))
          ((Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.swap (0 : Fin 3) 2))) =
      Matrix.operatorSchmidtRank ρ := by
  exact Matrix.operatorSchmidtRank_reindex_prodCongr ρ
    (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 3) 2)

/-- The first tensor factor may be empty. -/
example (ρ : Matrix (Fin 0 × Fin 3) (Fin 0 × Fin 3) ℂ) :
    Matrix.operatorSchmidtRank
        (ρ.reindex
          ((Equiv.refl (Fin 0)).prodCongr (Equiv.swap (0 : Fin 3) 2))
          ((Equiv.refl (Fin 0)).prodCongr (Equiv.swap (0 : Fin 3) 2))) =
      Matrix.operatorSchmidtRank ρ := by
  exact Matrix.operatorSchmidtRank_reindex_prodCongr ρ
    (Equiv.refl (Fin 0)) (Equiv.swap (0 : Fin 3) 2)

/-- The second tensor factor may be empty. -/
example (ρ : Matrix (Fin 2 × Fin 0) (Fin 2 × Fin 0) ℂ) :
    Matrix.operatorSchmidtRank
        (ρ.reindex
          ((Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.refl (Fin 0)))
          ((Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.refl (Fin 0)))) =
      Matrix.operatorSchmidtRank ρ := by
  exact Matrix.operatorSchmidtRank_reindex_prodCongr ρ
    (Equiv.swap (0 : Fin 2) 1) (Equiv.refl (Fin 0))

/-- Unequal tensor-factor dimensions give the cost 3²5² = 225. -/
example (ρ : Matrix ((Fin 2 × Fin 3) × (Fin 5 × Fin 7))
    ((Fin 2 × Fin 3) × (Fin 5 × Fin 7)) ℂ) :
    Matrix.operatorSchmidtRank
        (ρ.reindex (Equiv.prodProdProdComm (Fin 2) (Fin 3) (Fin 5) (Fin 7))
          (Equiv.prodProdProdComm (Fin 2) (Fin 3) (Fin 5) (Fin 7))) ≤
      225 * Matrix.operatorSchmidtRank ρ := by
  simpa using Matrix.operatorSchmidtRank_reindex_prodProdProdComm_le ρ

/-- An exchanged factor may be empty, giving a zero dimension cost. -/
example (ρ : Matrix ((Fin 2 × Fin 0) × (Fin 3 × Fin 5))
    ((Fin 2 × Fin 0) × (Fin 3 × Fin 5)) ℂ) :
    Matrix.operatorSchmidtRank
        (ρ.reindex (Equiv.prodProdProdComm (Fin 2) (Fin 0) (Fin 3) (Fin 5))
          (Equiv.prodProdProdComm (Fin 2) (Fin 0) (Fin 3) (Fin 5))) ≤ 0 := by
  simpa using Matrix.operatorSchmidtRank_reindex_prodProdProdComm_le ρ
