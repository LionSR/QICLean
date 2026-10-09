/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProjectionCfcUpperBound
import QICLean.Representation.GoodAuxiliaryLabelCompression

/-!
# The joint good auxiliary exponential on the original label subspaces

The two good auxiliary label entropies have a summed lower bound on the
intersection of their original whole-copy label subspaces. Exponentiating
this single compressed lower bound gives a joint operator bound. Thus no
product of separate expectation estimates is used.

Both original labels and both auxiliary dimensions are retained. An arbitrary
spectator register is included. Empty coordinate sets and zero copy groups
are permitted, with the total real logarithm.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 481--493,
`comparator:good-auxiliary`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped Matrix ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace TensorPower

variable {A C R : Type*} [Fintype A] [DecidableEq A]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
variable {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)

/-- The actual good auxiliary entropy sum has the sum of the two accepted
floors on the intersection of the original whole-label subspaces.
Source: `07-comparators.tex`, lines 481--493. -/
theorem copyPerm_groupedGood_auxiliaryPair_labelEntropy_compression
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) :
    let PC := labelProj (copyPerm C k) ellC
    let PR := labelProj (copyPerm R k) ellR
    let FC := labelEntropy ((copyPerm C k).comp (groupHom₁ e))
    let FR := labelEntropy ((copyPerm R k).comp (groupHom₁ e))
    let P := (1 : Matrix A A ℂ) ⊗ₖ (PC ⊗ₖ PR)
    let L := (1 : Matrix A A ℂ) ⊗ₖ
      (FC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ) +
        (1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ FR)
    let b := Real.log ellC.dim + Real.log ellR.dim -
      (r : ℝ) * (Real.log (Fintype.card C) + Real.log (Fintype.card R)) -
        2 * Real.log (k.choose r)
    IsStarProjection P ∧ Commute L P ∧ b • P ≤ P * L * P := by
  intro PC PR FC FR P L b
  let bC := Real.log ellC.dim - (r : ℝ) * Real.log (Fintype.card C) -
    Real.log (k.choose r)
  let bR := Real.log ellR.dim - (r : ℝ) * Real.log (Fintype.card R) -
    Real.log (k.choose r)
  have hb : b = bC + bR := by dsimp only [b, bC, bR]; ring
  obtain ⟨hCC, hC⟩ := copyPerm_groupedGood_labelEntropy_compression (C := C) e ellC
  obtain ⟨hRR, hR⟩ := copyPerm_groupedGood_labelEntropy_compression (C := R) e ellR
  have hPC : PC.IsHermitian := isHermitian_labelProj _ _
  have hPR : PR.IsHermitian := isHermitian_labelProj _ _
  have hPCP : PC * PC = PC := labelProj_mul_self _ _
  have hPRP : PR * PR = PR := labelProj_mul_self _ _
  have hPCpos : PC.PosSemidef := hPC.posSemidef_of_mul_self hPCP
  have hPRpos : PR.PosSemidef := hPR.posSemidef_of_mul_self hPRP
  have hP : IsStarProjection P := by
    rw [isStarProjection_iff']
    constructor
    · simp only [P, ← mul_kronecker_mul, one_mul, hPCP, hPRP]
    · change Pᴴ = P
      simp only [P, conjTranspose_kronecker, conjTranspose_one, hPC.eq, hPR.eq]
  have hLP : Commute L P := by
    change L * P = P * L
    simp only [L, P, ← mul_kronecker_mul, one_mul, mul_add, add_mul,
      mul_one, show FC * PC = PC * FC from hCC.eq,
      show FR * PR = PR * FR from hRR.eq]
  refine ⟨hP, hLP, ?_⟩
  have hC' : (PC * FC * PC - bC • PC).PosSemidef := by
    simpa only [Complex.coe_smul] using Matrix.le_iff.mp hC
  have hR' : (PR * FR * PR - bR • PR).PosSemidef := by
    simpa only [Complex.coe_smul] using Matrix.le_iff.mp hR
  have hsum := (PosSemidef.one (n := A)).kronecker
    ((hC'.kronecker hPRpos).add (hPCpos.kronecker hR'))
  apply Matrix.le_iff.mpr
  convert hsum using 1
  simp only [P, L, hb, add_smul, mul_add, add_mul, ← mul_kronecker_mul,
    one_mul, mul_one, hPCP, hPRP, sub_eq_add_neg,
    add_kronecker, kronecker_add, smul_kronecker, kronecker_smul]
  ext x y
  done

/-- The two good auxiliary exponentials obey one joint compressed bound on
the intersection of the original label subspaces. This is a single operator
inequality, not a multiplication of separate quadratic estimates.
Source: `07-comparators.tex`, lines 481--493. -/
theorem copyPerm_groupedGood_auxiliaryPair_exp_compression
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) {a : ℝ} (ha : 0 ≤ a) :
    let PC := labelProj (copyPerm C k) ellC
    let PR := labelProj (copyPerm R k) ellR
    let FC := labelEntropy ((copyPerm C k).comp (groupHom₁ e))
    let FR := labelEntropy ((copyPerm R k).comp (groupHom₁ e))
    let P := (1 : Matrix A A ℂ) ⊗ₖ (PC ⊗ₖ PR)
    let L := (1 : Matrix A A ℂ) ⊗ₖ
      (FC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ) +
        (1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ FR)
    let b := Real.log ellC.dim + Real.log ellR.dim -
      (r : ℝ) * (Real.log (Fintype.card C) + Real.log (Fintype.card R)) -
        2 * Real.log (k.choose r)
    P * NormedSpace.exp ((-a) • L) * P ≤ Real.exp (-a * b) • P := by
  intro PC PR FC FR P L b
  obtain ⟨hP, hLP, hfloor⟩ :=
    copyPerm_groupedGood_auxiliaryPair_labelEntropy_compression
      (A := A) (C := C) (R := R) e ellC ellR
  have hL : L.IsHermitian := by
    have hFC : FC.IsHermitian := isHermitian_labelObservable _ _
    have hFR : FR.IsHermitian := isHermitian_labelObservable _ _
    simp only [L, IsHermitian, conjTranspose_kronecker, conjTranspose_add,
      conjTranspose_one, hFC.eq, hFR.eq]
  exact hL.compression_exp_neg_smul_le_of_lower_bound hP hLP hfloor ha

end TensorPower
