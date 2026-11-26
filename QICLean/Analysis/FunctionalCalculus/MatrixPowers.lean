/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FunctionalCalculus.CfcLogAdditive
import QICLean.Analysis.FunctionalCalculus.MatrixSqrt
import QICLean.Analysis.Order.PosSemidefCommute
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import QICLean.Analysis.FunctionalCalculus.CfcConjugation

/-!
# Real powers of positive definite matrices

This file collects the elementary identities for real powers of positive
definite complex matrices used by the weighted geometric mean: positivity of
the powers, the exponent law, cancellation of a power against its negative,
scalar homogeneity, and the factorization of a power of a product of
commuting positive definite matrices.

## Main results

* `Matrix.PosDef.rpow` — a real power of a positive definite matrix is
  positive definite.
* `Matrix.PosDef.rpow_mul_rpow` — the exponent law `A ^ r * A ^ s = A ^ (r + s)`.
* `Matrix.PosDef.smul_rpow` — `(c • A) ^ r = c ^ r • A ^ r` for `c > 0`.
* `Matrix.PosDef.commute_rpow` — real powers of commuting positive definite
  matrices commute.
* `Matrix.PosDef.mul_rpow_of_commute` — `(A * B) ^ r = A ^ r * B ^ r` for
  commuting positive definite `A` and `B`.
* `Matrix.MeanTree.posDef_listProd_ofFn` — an ordered product of pairwise commuting
  positive definite matrices is positive definite.
* `Matrix.PosSemidef.rpow_intertwine`: rectangular intertwining of real matrix powers.
* `Matrix.cfc_log_listProd_ofFn`: the logarithm of an ordered commuting product.
-/

section MatrixPowers

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace PosDef

variable {A B : Matrix n n ℂ}

/-- A real power of a positive definite matrix is positive definite. -/
theorem rpow (hA : A.PosDef) (r : ℝ) : (A ^ r).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.rpow A r hA.isStrictlyPositive)

/-- A real power of a positive definite matrix is Hermitian. -/
theorem rpow_isHermitian (hA : A.PosDef) (r : ℝ) : (A ^ r).IsHermitian :=
  (hA.rpow r).isHermitian

/-- The conjugate transpose of a real power of a positive definite matrix is
itself. -/
@[simp] theorem star_rpow (hA : A.PosDef) (r : ℝ) : star (A ^ r) = A ^ r :=
  (hA.rpow_isHermitian r).eq

/-- The exponent law for real powers of a positive definite matrix. -/
theorem rpow_mul_rpow (hA : A.PosDef) (r s : ℝ) : A ^ r * A ^ s = A ^ (r + s) :=
  (CFC.rpow_add hA.isUnit).symm

/-- The zeroth real power of a positive definite matrix is the identity. -/
@[simp] theorem rpow_zero (hA : A.PosDef) : A ^ (0 : ℝ) = 1 :=
  CFC.rpow_zero A hA.posSemidef.nonneg

/-- The first real power of a positive definite matrix is the matrix. -/
@[simp] theorem rpow_one (hA : A.PosDef) : A ^ (1 : ℝ) = A :=
  CFC.rpow_one A hA.posSemidef.nonneg

/-- A real power cancels against its negative. -/
theorem rpow_mul_rpow_neg (hA : A.PosDef) (r : ℝ) : A ^ r * A ^ (-r) = 1 := by
  rw [hA.rpow_mul_rpow, add_neg_cancel, hA.rpow_zero]

/-- A negative real power cancels against the positive one. -/
theorem rpow_neg_mul_rpow (hA : A.PosDef) (r : ℝ) : A ^ (-r) * A ^ r = 1 := by
  rw [hA.rpow_mul_rpow, neg_add_cancel, hA.rpow_zero]

/-- The square of the positive square root is the matrix. -/
theorem rpow_half_mul_rpow_half (hA : A.PosDef) :
    A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by
  rw [hA.rpow_mul_rpow]; norm_num [hA.rpow_one]

/-- Iterated real powers multiply exponents. -/
theorem rpow_rpow (hA : A.PosDef) (r s : ℝ) : (A ^ r) ^ s = A ^ (r * s) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [hA.rpow_zero, CFC.one_rpow]
  · exact CFC.rpow_rpow A r s hr hA.isStrictlyPositive

/-- Scalar homogeneity of real powers: `(c • A) ^ r = c ^ r • A ^ r` for a positive real
scalar `c`. -/
theorem smul_rpow (hA : A.PosDef) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    (c • A) ^ r = c ^ r • A ^ r := by
  have hcA : (c • A).PosDef := hA.smul hc
  rw [CFC.rpow_eq_cfc_real hcA.posSemidef.nonneg, CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  rw [← cfc_comp_smul c (fun x : ℝ ↦ x ^ r) A ((A.finite_real_spectrum.image _).continuousOn _),
    ← cfc_smul (c ^ r) (fun x : ℝ ↦ x ^ r) A (A.finite_real_spectrum.continuousOn _)]
  refine cfc_congr fun x hx ↦ ?_
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hA.posSemidef.nonneg hx
  simp [smul_eq_mul, Real.mul_rpow hc.le hx0]

/-- Real powers of commuting positive definite matrices commute. -/
theorem commute_rpow (hA : A.PosDef) (hB : B.PosDef) (hAB : Commute A B) (r s : ℝ) :
    Commute (A ^ r) (B ^ s) := by
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg, CFC.rpow_eq_cfc_real hB.posSemidef.nonneg]
  exact Commute.cfc_real (Commute.cfc_real hAB.symm _).symm _

/-- A real power of a positive definite matrix commutes with every matrix commuting with
the original matrix. -/
theorem commute_rpow_left (hA : A.PosDef) {X : Matrix n n ℂ} (hAX : Commute A X) (r : ℝ) :
    Commute (A ^ r) X := by
  rw [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg]
  exact Commute.cfc_real hAX _

omit [DecidableEq n] in
/-- The product of commuting positive definite matrices is positive definite. -/
theorem mul_of_commute (hA : A.PosDef) (hB : B.PosDef) (hAB : Commute A B) :
    (A * B).PosDef := by
  classical
  exact (hA.posSemidef.mul_of_commute hB.posSemidef hAB.eq).posDef_iff_isUnit.mpr
    (hA.isUnit.mul hB.isUnit)

/-- A real power of a product of commuting positive definite matrices is the product of
the real powers. -/
theorem mul_rpow_of_commute (hA : A.PosDef) (hB : B.PosDef) (hAB : Commute A B) (r : ℝ) :
    (A * B) ^ r = A ^ r * B ^ r := by
  have hAB' : (A * B).PosDef := hA.mul_of_commute hB hAB
  have hr : (A ^ r * B ^ r).PosDef :=
    (hA.rpow r).mul_of_commute (hB.rpow r) (hA.commute_rpow hB hAB r r)
  have hlog : CFC.log ((A * B) ^ r) = CFC.log (A ^ r * B ^ r) := by
    rw [hAB'.cfc_log_rpow, cfc_log_mul hA hB hAB,
      cfc_log_mul (hA.rpow r) (hB.rpow r) (hA.commute_rpow hB hAB r r),
      hA.cfc_log_rpow, hB.cfc_log_rpow, smul_add]
  rw [← CFC.exp_log ((A * B) ^ r) (hAB'.rpow r).isStrictlyPositive,
    ← CFC.exp_log (A ^ r * B ^ r) hr.isStrictlyPositive, hlog]

end PosDef

namespace MeanTree

/-- A product, in index order, of pairwise commuting positive definite matrices is
positive definite. -/
theorem posDef_listProd_ofFn {K : ℕ} {D : Fin K → Matrix n n ℂ} (hD : ∀ g, (D g).PosDef)
    (hcomm : ∀ g g', g ≠ g' → Commute (D g) (D g')) : (List.ofFn D).prod.PosDef := by
  induction K with
  | zero => simpa using PosDef.one
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have hrest := ih (D := fun g ↦ D g.succ) (fun g ↦ hD _)
      (fun g g' h ↦ hcomm _ _ (fun h' ↦ h (Fin.succ_injective _ h')))
    refine (hD 0).mul_of_commute hrest (Commute.list_prod_right _ _ fun y hy ↦ ?_)
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
    exact hcomm _ _ (Fin.succ_ne_zero g).symm

end MeanTree

end Matrix

end MatrixPowers

section RealPowerIntertwine

/-!
## Rectangular intertwining of real matrix powers

The finite-dimensional functional calculus transports every real power
along a rectangular intertwiner of positive semidefinite matrices.

For a negative exponent, the power is zero on the kernel. No inverse on
that kernel is asserted.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September
  24, 2026, `06-transport.tex`, lines 17–22 and 157–172, revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`: functional-calculus identities
  used in the geometric mean and its derivative.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Every real power transports along a rectangular intertwiner of positive
semidefinite matrices, with the spectral convention on the kernel. Auxiliary
to the geometric-mean calculations of OpenAI's area-law manuscript,
`06-transport.tex`, lines 17–22 and 157–172. -/
theorem PosSemidef.rpow_intertwine
    {A : Matrix n n ℂ} {B : Matrix m m ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (J : Matrix n m ℂ)
    (hAJ : A * J = J * B) (s : ℝ) : A ^ s * J = J * B ^ s := by
  simpa only [CFC.rpow_eq_cfc_real hA.nonneg, CFC.rpow_eq_cfc_real hB.nonneg] using
    ConditionalMovement.QuantumSSA.cfc_intertwine
      hA.isHermitian hB.isHermitian J hAJ (fun x : ℝ ↦ x ^ s)

end Matrix

end RealPowerIntertwine

section CfcLogListProduct

/-!
## The logarithm of an ordered commuting product

The logarithm of an ordered finite product of pairwise commuting positive
definite matrices is the sum of their logarithms. This includes the empty
product and repeated matrix values.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, 06-transport.tex, transport:relative-factorization,
Lemma 7.1, and the band decomposition in 07-comparators.tex,
comparator:sharp-jensen, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The logarithm of an ordered product of pairwise commuting positive
definite matrices is the sum of the logarithms.
Source: 06-transport.tex, transport:relative-factorization, Lemma 7.1. -/
theorem cfc_log_listProd_ofFn {K : ℕ} {X : Fin K → Matrix m m ℂ}
    (hX : ∀ g, (X g).PosDef)
    (hXX : ∀ g g', g ≠ g' → Commute (X g) (X g')) :
    CFC.log (List.ofFn X).prod = ∑ g, CFC.log (X g) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      (hX 0).cfc_log_mul (Matrix.MeanTree.posDef_listProd_ofFn (fun g => hX _)
        (fun g g' h => hXX _ _ (fun h' => h (Fin.succ_injective _ h'))))
        (Commute.list_prod_right _ _ fun y hy => by
          obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
          exact hXX _ _ (Fin.succ_ne_zero g).symm),
      ih (fun g => hX _) (fun g g' h => hXX _ _ (fun h' => h (Fin.succ_injective _ h')))]

end Matrix

end

end CfcLogListProduct
