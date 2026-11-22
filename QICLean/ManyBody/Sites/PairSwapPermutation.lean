/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.PairSwap
import QICLean.Analysis.Norm.MatrixKroneckerContraction

/-!
# The exchange of two copies as a permutation of configurations

On the system with basis `X v × X v` at every site, the exchange `ManyBody.pairSwapOp A` of the
two copies at the sites of a region `A` is the permutation matrix of the permutation
`ManyBody.pairSwap A` of configurations that exchanges the two entries of the pair at every site
of `A`. Exchanging on `A` and then on `B` exchanges on the symmetric difference of `A` and `B`;
in particular exchanging on `A ⊆ Y` after exchanging on `Y` exchanges on `Y \ A`. Being a
permutation matrix, the exchange is a contraction. Conjugating by the exchange on `R` permutes
the entries of a matrix, and it exchanges the two factors of `A ⊗ B` when `A` and `B` are
supported on `R`.

Reading a paired configuration as a pair of configurations of the two copies, along
`Equiv.arrowProdEquivProdArrow`, the exchange on `A` takes the parts on `A` from the other copy
and keeps the parts outside `A`.

These are the statements of TNLean's `TNLean.Lattice.sheetSwap` lemmas (`Circuit/RegionalSwap`,
at commit `707a50e56c`), written for the exchange `ManyBody.pairSwapOp`; the two sheets
`(ι → Fin q) × (ι → Fin q)` there are the two copies here, paired at every site.

## Main definitions

* `ManyBody.pairSwap` — the permutation of paired configurations exchanging the two copies at
  the sites of a region.

## Main results

* `ManyBody.pairSwapOp_eq_permMatrix` — the exchange is the permutation matrix of `pairSwap`.
* `ManyBody.pairSwapOp_mul`, `ManyBody.pairSwapOp_mul_of_subset` — the composition law.
* `ManyBody.norm_pairSwapOp_le_one` — the exchange is a contraction.
* `ManyBody.pairSwapOp_mul_mul_conjTranspose_kronecker`, `ManyBody.pairSwapOp_mul_kronecker` —
  the exchange of two operators supported on the region.
* `ManyBody.cutEquiv_permCongr_pairSwap_fst`, `ManyBody.cutEquiv_permCongr_pairSwap_snd` — the
  cut of the exchanged pair of configurations.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, proof of Lemma 6.6 (`lem:exchange`), `05-frames.tex`, lines 481–561, and
  `02-information.tex`, lines 416–424.
-/

open Matrix
open scoped Kronecker symmDiff Matrix.Norms.L2Operator

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-! ### The permutation of configurations -/

section Permutation

variable {X : V → Type*}

omit [Fintype V] in
private theorem pairSwap_involutive (A : Finset V) :
    Function.Involutive fun (σ : Config fun v ↦ X v × X v) v ↦
      if v ∈ A then (σ v).swap else σ v := by
  intro σ
  funext v
  by_cases hv : v ∈ A <;> simp [hv]

/-- The permutation of paired configurations exchanging the two copies at the sites of `A`:
the pair at a site of `A` is swapped, the pair at any other site is kept. -/
def pairSwap (A : Finset V) : Equiv.Perm (Config fun v ↦ X v × X v) :=
  (pairSwap_involutive A).toPerm _

omit [Fintype V] in
@[simp]
theorem pairSwap_apply (A : Finset V) (σ : Config fun v ↦ X v × X v) (v : V) :
    pairSwap A σ v = if v ∈ A then (σ v).swap else σ v :=
  rfl

omit [Fintype V] in
/-- The exchange of the two copies is an involution. -/
@[simp]
theorem pairSwap_symm (A : Finset V) : (pairSwap (X := X) A).symm = pairSwap A :=
  rfl

omit [Fintype V] in
/-- Exchanging on `B` and then on `A` exchanges on the symmetric difference of `A` and `B`. -/
theorem pairSwap_mul (A B : Finset V) :
    pairSwap (X := X) A * pairSwap B = pairSwap (A ∆ B) := by
  ext σ v : 2
  rw [Equiv.Perm.mul_apply, pairSwap_apply, pairSwap_apply, pairSwap_apply]
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;> simp [hA, hB, Finset.mem_symmDiff]

end Permutation

/-! ### The exchange as a permutation matrix -/

omit [∀ v, Fintype (X v)] in
/-- **The exchange is a permutation matrix.** The exchange of the two copies on `A` is the
permutation matrix of `ManyBody.pairSwap A`. -/
theorem pairSwapOp_eq_permMatrix (A : Finset V) :
    pairSwapOp (X := X) A = (pairSwap A).permMatrix ℂ := by
  ext σ τ
  have hsite (v : V) :
      (if v ∈ A then Equiv.Perm.permMatrix ℂ (Equiv.prodComm (X v) (X v)) else 1) (σ v) (τ v) =
        if pairSwap A σ v = τ v then 1 else 0 := by
    by_cases hv : v ∈ A <;>
      simp [hv, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, one_apply]
  rw [pairSwapOp, piKronecker_apply, Finset.prod_congr rfl fun v _ ↦ hsite v, Fintype.prod_boole,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  exact if_congr (by rw [Option.mem_some_iff, funext_iff]) rfl rfl

/-- **The composition law.** Exchanging the two copies on `A` and on `B` is exchanging them on
the symmetric difference of `A` and `B`. -/
theorem pairSwapOp_mul (A B : Finset V) :
    pairSwapOp (X := X) A * pairSwapOp B = pairSwapOp (A ∆ B) := by
  rw [pairSwapOp_eq_permMatrix, pairSwapOp_eq_permMatrix, pairSwapOp_eq_permMatrix,
    ← Matrix.permMatrix_mul, pairSwap_mul, symmDiff_comm]

/-- `F_A F_Y = F_{Y \ A}` when `A ⊆ Y`. Polynomial PEPS approximation, `05-frames.tex`,
lines 516–520. -/
theorem pairSwapOp_mul_of_subset {A Y : Finset V} (h : A ⊆ Y) :
    pairSwapOp (X := X) A * pairSwapOp Y = pairSwapOp (Y \ A) := by
  rw [pairSwapOp_mul, symmDiff_of_le h]

/-- The exchange of the two copies is a contraction. -/
theorem norm_pairSwapOp_le_one (A : Finset V) : ‖pairSwapOp (X := X) A‖ ≤ 1 := by
  rw [pairSwapOp_eq_permMatrix]
  exact l2_opNorm_toMatrix_toPEquiv_le _

/-- Conjugating by the exchange on `A` permutes the entries along `ManyBody.pairSwap A`. -/
theorem pairSwapOp_mul_mul_conjTranspose (A : Finset V)
    (M : Matrix (Config fun v ↦ X v × X v) (Config fun v ↦ X v × X v) ℂ) :
    pairSwapOp A * M * (pairSwapOp A)ᴴ = M.submatrix (pairSwap A) (pairSwap A) := by
  rw [conjTranspose_pairSwapOp, pairSwapOp_eq_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, submatrix_submatrix,
    pairSwap_symm]
  rfl

/-! ### The exchange of two operators supported on the region -/

/-- **The exchange of two operators supported on the region.** For `A` and `B` supported on `R`,
conjugating `A ⊗ B`, with the two copies of every site paired, by the exchange of the two
copies on `R` gives `B ⊗ A`. Polynomial PEPS approximation, `02-information.tex`,
lines 416–424. -/
theorem pairSwapOp_mul_mul_conjTranspose_kronecker {R : Finset V}
    {A B : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R)
    (hB : B ∈ supportedOperators X R) :
    pairSwapOp R * reindex (Equiv.arrowProdEquivProdArrow V X X).symm
        (Equiv.arrowProdEquivProdArrow V X X).symm (A ⊗ₖ B) * (pairSwapOp R)ᴴ =
      reindex (Equiv.arrowProdEquivProdArrow V X X).symm
        (Equiv.arrowProdEquivProdArrow V X X).symm (B ⊗ₖ A) := by
  obtain ⟨K, rfl⟩ := exists_eq_place_of_mem_supportedOperators hA
  obtain ⟨K', rfl⟩ := exists_eq_place_of_mem_supportedOperators hB
  rw [pairSwapOp_mul_mul_conjTranspose]
  ext σ τ
  simp only [submatrix_apply, reindex_apply, Equiv.symm_symm, kroneckerMap_apply,
    Equiv.arrowProdEquivProdArrow_apply, place_apply, pairSwap_apply]
  simp +contextual [mul_comm]

/-- **The exchange of two operators supported on the region**, as a commutation rule:
`F_R (A ⊗ B) = (B ⊗ A) F_R` for `A` and `B` supported on `R`. Polynomial PEPS approximation,
`02-information.tex`, lines 416–424. -/
theorem pairSwapOp_mul_kronecker {R : Finset V} {A B : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X R) (hB : B ∈ supportedOperators X R) :
    pairSwapOp R * reindex (Equiv.arrowProdEquivProdArrow V X X).symm
        (Equiv.arrowProdEquivProdArrow V X X).symm (A ⊗ₖ B) =
      reindex (Equiv.arrowProdEquivProdArrow V X X).symm
        (Equiv.arrowProdEquivProdArrow V X X).symm (B ⊗ₖ A) * pairSwapOp R := by
  rw [← pairSwapOp_mul_mul_conjTranspose_kronecker hA hB, Matrix.mul_assoc _ (pairSwapOp R)ᴴ,
    conjTranspose_pairSwapOp, pairSwapOp_mul_self, Matrix.mul_one]

/-! ### The two copies read as a pair of configurations -/

section TwoCopies

variable {X : V → Type*}

omit [Fintype V] in
/-- Read as a pair of configurations of the two copies, the exchange on `A` takes the parts on
`A` from the other copy and keeps the parts outside `A`. -/
theorem permCongr_pairSwap_apply (A : Finset V) (r : Config X × Config X) :
    (Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap A) r =
      (fun v ↦ if v ∈ A then r.2 v else r.1 v, fun v ↦ if v ∈ A then r.1 v else r.2 v) := by
  refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_) <;>
    by_cases hv : v ∈ A <;> simp [hv]

omit [Fintype V] in
/-- Read as a permutation of pairs of configurations, the exchange is still an involution. -/
@[simp]
theorem permCongr_pairSwap_symm (A : Finset V) :
    ((Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap A)).symm =
      (Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap A) :=
  Equiv.ext fun _ ↦ rfl

omit [Fintype V] in
/-- In the coordinates of the cut along `S`, the exchange on `S` takes the part on `S` of the
first copy from the second copy. -/
theorem cutEquiv_permCongr_pairSwap_fst (S : Finset V) (r : Config X × Config X) :
    cutEquiv X S ((Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap S) r).1 =
      ((cutEquiv X S r.2).1, (cutEquiv X S r.1).2) := by
  rw [permCongr_pairSwap_apply]
  refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_) <;> simp [v.2]

omit [Fintype V] in
/-- In the coordinates of the cut along `S`, the exchange on `S` takes the part on `S` of the
second copy from the first copy. -/
theorem cutEquiv_permCongr_pairSwap_snd (S : Finset V) (r : Config X × Config X) :
    cutEquiv X S ((Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap S) r).2 =
      ((cutEquiv X S r.1).1, (cutEquiv X S r.2).2) := by
  rw [permCongr_pairSwap_apply]
  refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_) <;> simp [v.2]

end TwoCopies

omit [∀ v, Fintype (X v)] in
/-- Read as an operator on pairs of configurations of the two copies, the exchange on `A` is
the permutation matrix of the exchange of the parts on `A`. -/
theorem reindex_pairSwapOp (A : Finset V) :
    reindex (Equiv.arrowProdEquivProdArrow V X X) (Equiv.arrowProdEquivProdArrow V X X)
        (pairSwapOp A) =
      ((Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap A)).permMatrix ℂ := by
  rw [pairSwapOp_eq_permMatrix]
  ext x y
  simp only [reindex_apply, submatrix_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_some_iff, Equiv.permCongr_apply, Equiv.eq_symm_apply]

omit [Fintype V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- An entry of a matrix is the entry of the matrix in the coordinates of the cut along `S`. -/
theorem apply_eq_submatrix_cutEquiv_apply (S : Finset V) (M : Matrix (Config X) (Config X) ℂ)
    (σ τ : Config X) :
    M σ τ = M.submatrix (cutEquiv X S).symm (cutEquiv X S).symm (cutEquiv X S σ)
      (cutEquiv X S τ) := by
  rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- The product of an operator `O = 1 ⊗ O'` acting off `S` and an operator `I = I' ⊗ 1` acting
on `S` is `I' ⊗ O'` in the coordinates of the cut along `S`. -/
theorem submatrix_cutEquiv_symm_mul {S : Finset V} {O I : Matrix (Config X) (Config X) ℂ}
    {O' : Matrix (ComplConfig X S) (ComplConfig X S) ℂ}
    {I' : Matrix (RegionConfig X S) (RegionConfig X S) ℂ}
    (hO : O.submatrix (cutEquiv X S).symm (cutEquiv X S).symm = 1 ⊗ₖ O')
    (hI : I.submatrix (cutEquiv X S).symm (cutEquiv X S).symm = I' ⊗ₖ 1) :
    (O * I).submatrix (cutEquiv X S).symm (cutEquiv X S).symm = I' ⊗ₖ O' := by
  rw [← submatrix_mul_equiv _ _ _ (cutEquiv X S).symm, hO, hI, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

end ManyBody
