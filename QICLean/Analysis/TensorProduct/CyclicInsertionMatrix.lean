/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TensorProduct.CyclicInsertion
import QICLean.Analysis.Norm.MatrixToEuclidean
import QICLean.Analysis.Norm.VectorPreparation

/-!
# Matrices of the cyclic insertion maps

Let `η` be a vector of `ℂ^ι`.  The insertion of a vector at position `k` among copies of `η`,
the cyclic insertion `T_m`, and the ideal map `|η^{⊗ m}⟩⟨η|` of
`QICLean.Analysis.TensorProduct.CyclicInsertion` are linear maps from `ℂ^ι` to the tensor power
`(ℂ^ι)^{⊗ κ}`, written on the configurations `κ → ι`.  Their matrices in the standard bases are
complex matrices with rows indexed by configurations and columns indexed by `ι`, normed by the
operator norm (`Matrix.Norms.L2Operator`).  This file records their entries and transfers the
norm estimates of the maps: the insertions and `T_m` are contractions when `η` is a unit vector,
and `‖T_m - |η^{⊗ m}⟩⟨η|‖ ≤ m^{-1/2}`.

## Main definitions

* `CyclicInsertion.insertAtMatrix` : the matrix of the insertion at one position.
* `CyclicInsertion.cyclicInsertionMatrix` : the matrix of `T_m`.
* `CyclicInsertion.idealInsertionMatrix` : the matrix of `|η^{⊗ m}⟩⟨η|`.

## Main results

* `CyclicInsertion.insertAtMatrix_apply`, `CyclicInsertion.idealInsertionMatrix_apply` : the
  entries.
* `CyclicInsertion.insertAtMatrix_eq_insertNth` : an insertion is a preparation of `η^{⊗ n}`
  followed by a relabelling.
* `CyclicInsertion.cyclicInsertionMatrix_eq_sum` : `T_m` is the average of the `m` insertions.
* `CyclicInsertion.norm_cyclicInsertionMatrix_sub_ideal_le` : the one-effect estimate.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`, proof of the
  one-effect estimate `eq:compression-one-effect`, `04-compression.tex`, lines 73–98.
-/

noncomputable section

open scoped InnerProductSpace Matrix.Norms.L2Operator
open Matrix EuclideanSpace

namespace CyclicInsertion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The matrix of the insertion `insertAt η k : ℂ^ι → (ℂ^ι)^{⊗ κ}` of a vector at position `k`
among copies of `η`. -/
def insertAtMatrix (η : EuclideanSpace ℂ ι) (k : κ) : Matrix (κ → ι) ι ℂ :=
  toEuclideanLin.symm (insertAt η k).toLinearMap

/-- The entries of the insertion matrix: the column index sits at position `k` of the
configuration, and every other position carries a coefficient of `η`. -/
theorem insertAtMatrix_apply (η : EuclideanSpace ℂ ι) (k : κ) (f : κ → ι) (i : ι) :
    insertAtMatrix η k f i =
      (if f k = i then 1 else 0) * ∏ j ∈ Finset.univ.erase k, η (f j) := by
  rw [insertAtMatrix, toEuclideanLin_symm_apply, ContinuousLinearMap.coe_coe, insertAt_apply,
    piTensor_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp [PiLp.single_apply]
  · exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **The insertion at `k` is a preparation followed by a relabelling**: it appends the tensor
power `η^{⊗ n}` behind the input and reads the configuration `(i, f)` as `Fin.insertNth k i f`.
Source: `04-compression.tex`, lines 75–79 and 96–98 (each insertion term is a normalized source
preparation followed by a permutation of the pair registers). -/
theorem insertAtMatrix_eq_insertNth (η : EuclideanSpace ℂ ι) {n : ℕ} (k : Fin (n + 1)) :
    insertAtMatrix η k =
      reindex (Fin.insertNthEquiv (fun _ ↦ ι) k) (Equiv.refl ι)
        (prepMatrix (Equiv.prodComm ι (Fin n → ι)) (tensorPower (Fin n) η)) := by
  ext f i
  rw [insertAtMatrix_apply, reindex_apply, submatrix_apply, prepMatrix_apply]
  have hp : ∏ j ∈ Finset.univ.erase k, η (f j) = ∏ j : Fin n, η (f (k.succAbove j)) := by
    calc ∏ j ∈ Finset.univ.erase k, η (f j)
        = ∏ j ∈ Finset.univ.erase k, (if j = k then 1 else η (f j)) :=
          Finset.prod_congr rfl fun j hj ↦ by simp [Finset.ne_of_mem_erase hj]
      _ = ∏ j, (if j = k then 1 else η (f j)) := Finset.prod_erase _ (by simp)
      _ = _ := by simp [Fin.prod_univ_succAbove _ k, Fin.succAbove_ne]
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, Equiv.refl_symm,
    Equiv.refl_apply, tensorPower, piTensor_apply, hp, ite_mul, one_mul, zero_mul]
  rfl

/-- The matrix of the cyclic insertion `T_m : ℂ^ι → (ℂ^ι)^{⊗ m}`. -/
def cyclicInsertionMatrix (η : EuclideanSpace ℂ ι) (m : ℕ) : Matrix (Fin m → ι) ι ℂ :=
  toEuclideanLin.symm (cyclicInsertion η m).toLinearMap

/-- The matrix of the ideal map `|η^{⊗ m}⟩⟨η|`. -/
def idealInsertionMatrix (η : EuclideanSpace ℂ ι) (m : ℕ) : Matrix (Fin m → ι) ι ℂ :=
  toEuclideanLin.symm (idealInsertion η m).toLinearMap

/-- The entries of the ideal map: `η^{⊗ m}` times the conjugate of a coefficient of `η`. -/
theorem idealInsertionMatrix_apply (η : EuclideanSpace ℂ ι) (m : ℕ) (f : Fin m → ι) (i : ι) :
    idealInsertionMatrix η m f i = tensorPower (Fin m) η f * star (η i) := by
  rw [idealInsertionMatrix, toEuclideanLin_symm_apply, ContinuousLinearMap.coe_coe,
    idealInsertion_apply, EuclideanSpace.inner_single_right, PiLp.smul_apply, smul_eq_mul,
    one_mul, mul_comm]
  rfl

/-- The cyclic insertion is the average of the `m` insertions. -/
theorem cyclicInsertionMatrix_eq_sum (η : EuclideanSpace ℂ ι) (m : ℕ) :
    cyclicInsertionMatrix η m = ∑ k : Fin m, ((m : ℂ)⁻¹) • insertAtMatrix η k := by
  simp only [cyclicInsertionMatrix, insertAtMatrix, cyclicInsertion,
    ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul, map_sum, map_smul]

/-- An insertion among copies of a unit vector is a contraction. -/
theorem norm_insertAtMatrix_le_one {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1) (k : κ) :
    ‖insertAtMatrix η k‖ ≤ 1 :=
  (l2_opNorm_toEuclideanLin_symm _).trans_le (norm_insertAt_le_one hη k)

/-- The cyclic insertion into copies of a unit vector is a contraction. -/
theorem norm_cyclicInsertionMatrix_le_one {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1) (m : ℕ) :
    ‖cyclicInsertionMatrix η m‖ ≤ 1 :=
  (l2_opNorm_toEuclideanLin_symm _).trans_le (norm_cyclicInsertion_le_one hη m)

/-- **One-effect estimate**, matrix form: `‖T_m - |η^{⊗ m}⟩⟨η|‖ ≤ m^{-1/2}`.

Polynomial-PEPS manuscript (September 24, 2026), Lemma 5.1 `lem:effects`, displayed
equation `eq:compression-one-effect`, `04-compression.tex`, lines 73–98. -/
theorem norm_cyclicInsertionMatrix_sub_ideal_le {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1)
    {m : ℕ} (hm : m ≠ 0) :
    ‖cyclicInsertionMatrix η m - idealInsertionMatrix η m‖ ≤ 1 / Real.sqrt m := by
  rw [cyclicInsertionMatrix, idealInsertionMatrix, ← map_sub,
    ← ContinuousLinearMap.toLinearMap_sub]
  exact (l2_opNorm_toEuclideanLin_symm _).trans_le (norm_cyclicInsertion_sub_ideal_le hη hm)

end CyclicInsertion
