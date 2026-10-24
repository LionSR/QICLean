/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Operator Schmidt rank for a middle factor and two exterior factors

For an operator on three finite complex tensor factors, the rank across the
middle-versus-exterior cut is at most the product of the two boundary ranks.
A basis of the right operator-block span gives coordinate functionals, extended
linearly to all right operators. Contracting a minimal left-cut decomposition
with those functionals produces the required family of exterior operators.
Basis reconstruction is applied to the actual blocks of the original operator.

Empty factors and zero ranks are included. The proof uses the existing finite
block-span bound and introduces no independence assumption on the factors of
the chosen left decomposition.

Supporting algebra for ALVV, arXiv:1602.08828v2, Proposition prop:Cheby-AGSP-eff,
lines 1324 and 1332. Physical coefficient families, local cut identifications,
and internal MPO bond dimensions are separate statements.
-/

open scoped BigOperators Kronecker
noncomputable section
namespace Matrix

private def middleMatrix {l m n : Type*}
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) :
    Matrix (m × (l × n)) (m × (l × n)) ℂ :=
  fun i j ↦ ρ ((i.2.1, i.1), i.2.2) ((j.2.1, j.1), j.2.2)

private def rightBasis {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) :
    Module.Basis (Fin (Module.finrank ℂ (operatorBlockSpan ρ))) ℂ
      (operatorBlockSpan ρ) :=
  Module.finBasis ℂ (operatorBlockSpan ρ)

private def rightCoord {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ)
    (t : Fin (Module.finrank ℂ (operatorBlockSpan ρ))) : Matrix n n ℂ →ₗ[ℂ] ℂ :=
  ((rightBasis ρ).coord t).comp (operatorBlockSpan ρ).subtype.leftInverse

private theorem right_reconstruct {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ)
    (x : operatorBlockSpan ρ) :
    ∑ t, rightCoord ρ t (x : Matrix n n ℂ) •
      ((rightBasis ρ) t : Matrix n n ℂ) = (x : Matrix n n ℂ) := by
  simpa only [rightCoord, LinearMap.comp_apply,
    (show (operatorBlockSpan ρ).subtype.leftInverse (x : Matrix n n ℂ) = x from
      LinearMap.leftInverse_apply_of_inj (operatorBlockSpan ρ).ker_subtype x),
    Module.Basis.coord_apply, Submodule.coe_sum, Submodule.coe_smul] using
    congrArg (fun y : operatorBlockSpan ρ ↦ (y : Matrix n n ℂ))
      ((rightBasis ρ).sum_repr x)

private theorem right_block_expand {l m n : Type*}
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) {r : ℕ}
    (L : Fin r → Matrix l l ℂ) (Y : Fin r → Matrix (m × n) (m × n) ℂ)
    (hρ : ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n) = ∑ a, L a ⊗ₖ Y a)
    (x y : l) (i j : m) :
    operatorBlock ρ (x, i) (y, j) = ∑ a, L a x y • operatorBlock (Y a) i j := by
  ext u v
  simpa [operatorBlock, reindex_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul] using
    congrArg (fun Z : Matrix (l × (m × n)) (l × (m × n)) ℂ ↦
      Z (x, (i, u)) (y, (j, v))) hρ

private theorem coordinate_expand {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) {r : ℕ}
    (L : Fin r → Matrix l l ℂ) (Y : Fin r → Matrix (m × n) (m × n) ℂ)
    (hρ : ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n) = ∑ a, L a ⊗ₖ Y a)
    (x y : l) (i j : m) (t : Fin (Module.finrank ℂ (operatorBlockSpan ρ))) :
    rightCoord ρ t (operatorBlock ρ (x, i) (y, j)) =
      ∑ a, L a x y * rightCoord ρ t (operatorBlock (Y a) i j) := by
  simp only [right_block_expand ρ L Y hρ, map_sum, map_smul, smul_eq_mul]

private theorem middle_block_eq {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) {r : ℕ}
    (L : Fin r → Matrix l l ℂ) (Y : Fin r → Matrix (m × n) (m × n) ℂ)
    (hρ : ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n) = ∑ a, L a ⊗ₖ Y a)
    (i j : m) :
    operatorBlock (middleMatrix ρ) i j =
      ∑ pair : Fin r × Fin (Module.finrank ℂ (operatorBlockSpan ρ)),
        rightCoord ρ pair.2 (operatorBlock (Y pair.1) i j) •
          (L pair.1 ⊗ₖ ((rightBasis ρ) pair.2 : Matrix n n ℂ)) := by
  ext p q
  have hrec := congrArg (fun Z : Matrix n n ℂ ↦ Z p.2 q.2)
    (right_reconstruct ρ ⟨operatorBlock ρ (p.1, i) (q.1, j),
      Submodule.subset_span ⟨((p.1, i), (q.1, j)), rfl⟩⟩)
  simp only [middleMatrix, operatorBlock_apply, Matrix.sum_apply, Matrix.smul_apply,
    coordinate_expand ρ L Y hρ, Fintype.sum_prod_type, Finset.sum_mul,
    smul_eq_mul, kroneckerMap_apply, mul_assoc] at hrec ⊢
  exact hrec.symm.trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun t _ ↦
      mul_left_comm _ _ _))

private theorem middle_blocks {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) {r : ℕ}
    (L : Fin r → Matrix l l ℂ) (Y : Fin r → Matrix (m × n) (m × n) ℂ)
    (hρ : ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n) = ∑ a, L a ⊗ₖ Y a)
    (i j : m) :
    operatorBlock (middleMatrix ρ) i j ∈ Submodule.span ℂ
      (Set.range (fun pair : Fin r × Fin (Module.finrank ℂ (operatorBlockSpan ρ)) ↦
        L pair.1 ⊗ₖ ((rightBasis ρ) pair.2 : Matrix n n ℂ))) := by
  rw [middle_block_eq ρ L Y hρ i j]
  exact Submodule.sum_smul_mem _ _ fun pair _ ↦ Submodule.subset_span ⟨pair, rfl⟩

/-- The middle-versus-exterior rank is at most the product of the two boundary ranks.
Supporting algebra for ALVV, arXiv:1602.08828v2, prop:Cheby-AGSP-eff, lines 1324 and 1332. -/
theorem operatorSchmidtRank_middle_le_mul
    {l m n : Type*} [Fintype l] [Fintype m] [Finite n]
    (ρ : Matrix ((l × m) × n) ((l × m) × n) ℂ) :
    let a := Equiv.prodAssoc l m n
    let e := a.trans ((Equiv.prodComm l (m × n)).trans
      ((Equiv.prodAssoc m n l).trans
        (Equiv.prodCongr (Equiv.refl m) (Equiv.prodComm n l))))
    operatorSchmidtRank (ρ.reindex e e) ≤
      operatorSchmidtRank (ρ.reindex a a) * operatorSchmidtRank ρ := by
  classical
  change operatorSchmidtRank (middleMatrix ρ) ≤
    operatorSchmidtRank (ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n)) *
      operatorSchmidtRank ρ
  obtain ⟨L, Y, hρ⟩ := hasOperatorSchmidtDecomposition_operatorSchmidtRank
    (ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n))
  simpa only [Fintype.card_prod, Fintype.card_fin,
    ← operatorSchmidtRank_eq_finrank_operatorBlockSpan] using
    operatorSchmidtRank_le_card_of_blocks_mem_span (middleMatrix ρ)
      (fun pair : Fin (operatorSchmidtRank
        (ρ.reindex (Equiv.prodAssoc l m n) (Equiv.prodAssoc l m n))) ×
        Fin (Module.finrank ℂ (operatorBlockSpan ρ)) ↦
          L pair.1 ⊗ₖ ((rightBasis ρ) pair.2 : Matrix n n ℂ))
      (middle_blocks ρ L Y hρ)

end Matrix
