/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Representation.SchurWeylCommutant
import QICLean.Algebra.KroneckerFactorPositivity
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Logic.Equiv.Prod

/-!
# Identity extensions of replica means

Regrouping the copies of a product space into separate physical and auxiliary
registers sends a one-copy physical operator extended by the auxiliary identity
to the corresponding physical replica operator with identity on all auxiliary
copies. The normalized sums satisfy the same identity at every replica count.
The one-copy operator is also identified with its iterated Kronecker product.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`06-transport.tex`, lines 335–358, and `07-comparators.tex`, lines 421–438,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are algebraic identities; the operator need not be Hermitian.
-/

open scoped BigOperators Kronecker

noncomputable section

namespace TensorPower

variable {A B : Type*} [DecidableEq A] [DecidableEq B] {k : ℕ}

/-- A one-copy operator extended by an identity, regrouped into physical
copies and auxiliary copies. No state or spectral hypothesis is involved.
Source: OpenAI area-law manuscript, `06-transport.tex`, lines 335–358, and
`07-comparators.tex`, lines 421–438, revision `adc7f124`. -/
theorem siteOp_kronecker_one (i : Fin k) (H : Matrix A A ℂ) :
    siteOp i (H ⊗ₖ (1 : Matrix B B ℂ)) =
      (siteOp i H ⊗ₖ (1 : Matrix (Fin k → B) (Fin k → B) ℂ)).submatrix
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A) (fun _ => B))
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A) (fun _ => B)) := by
  ext x y
  simp only [siteOp, partialTensor, Finset.mem_singleton, Finset.prod_singleton,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk, funext_iff, Prod.ext_iff]
  grind

/-- Identity extension commutes with the replica mean, under the same
regrouping of physical and auxiliary copies, for every replica count.
Source: OpenAI area-law manuscript, `06-transport.tex`, lines 335–358, and
`07-comparators.tex`, lines 421–438, revision `adc7f124`. -/
theorem replicaMean_kronecker_one (H : Matrix A A ℂ) (k : ℕ) :
    (k : ℂ)⁻¹ • (∑ i : Fin k, siteOp i (H ⊗ₖ (1 : Matrix B B ℂ))) =
      (((k : ℂ)⁻¹ • (∑ i : Fin k, siteOp i H)) ⊗ₖ
        (1 : Matrix (Fin k → B) (Fin k → B) ℂ)).submatrix
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A) (fun _ => B))
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A) (fun _ => B)) := by
  ext x y
  simp only [Matrix.smul_apply, Matrix.sum_apply, siteOp_kronecker_one,
    Matrix.submatrix_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
  rw [← Finset.sum_mul, mul_assoc]

/-- The same one-copy operator in the iterated-Kronecker definition.
Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 421–438,
revision `adc7f124`. -/
theorem siteOp_eq_finKronecker [Fintype A] (i : Fin k) (H : Matrix A A ℂ) :
    siteOp i H = Matrix.finKronecker (fun j : Fin k => if j = i then H else 1) := by
  ext x y
  simp only [siteOp, partialTensor, Finset.mem_singleton, Finset.prod_singleton,
    Matrix.finKronecker, Matrix.of_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [Finset.prod_congr rfl (fun j hj ↦
    congrArg (fun M : Matrix A A ℂ ↦ M (x j) (y j))
      (ite_eq_right (Finset.mem_erase.mp hj).1))]
  simp only [ite_true, Matrix.one_apply, Finset.prod_boole, Finset.mem_erase,
    Finset.mem_univ, and_true, mul_ite, mul_one, mul_zero]

end TensorPower
