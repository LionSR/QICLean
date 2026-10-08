/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Derivative

/-!
# Transport-state expectations as derivatives of the filtered norm

For a weighted tree with positive definite inputs, a leaf `j` of nonzero weight and a Hermitian
matrix `Q`, perturb the input at `j` along `A_j^{1/2} e^{δ Q} A_j^{1/2}`. The derivative of
`-log N²` at `δ = 0` is `w_j ∫ m_{1/4}(u) Tr(σ_{j,u} Q) du`, where `σ_{j,u}` are the transport
states of the leaf (`06-transport.tex`, displays `transport:norm-derivative` and
`transport:states`, lines 470--494). The perturbed roots are continuous in every parameter on
which the tree depends continuously, so this expresses the transport-state expectation as a
pointwise limit of continuous functions of such a parameter. It is used to show that the
entropy-gain term of the transport estimate is measurable in the interpolation parameter
(`06-transport.tex` lines 427--429 and 769--779).

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `Matrix.MeanTree.hasDerivAt_eval_update_path` — the chain rule along a path in one input,
  without distinctness of the leaf labels.
* `Matrix.Transport.leafPerturbation` — the path `A_j^{1/2} e^{δ Q} A_j^{1/2}`.
* `Matrix.Transport.hasDerivAt_neg_log_filteredNormSq_leafPerturbation` — the derivative.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology MeasureTheory

noncomputable section

namespace Matrix

namespace MeanTree

variable {ι n : Type*} [Fintype n] [DecidableEq n] [DecidableEq ι]

/-- **Chain rule along a path in one input.** If `P` is a differentiable path of positive
definite matrices, the root of a tree whose input `j` is replaced by `P δ` has derivative
`derivLabel` applied to `P'`. Unlike `hasFDerivWithinAt_eval_update`, the label `j` may occur
at several leaves. -/
theorem hasDerivAt_eval_update_path {A : ι → Matrix n n ℂ} (hA : ∀ i, (A i).PosDef) (j : ι)
    {P : ℝ → Matrix n n ℂ} {P' : Matrix n n ℂ} {δ : ℝ} (hPd : ∀ s, (P s).PosDef)
    (hP : HasDerivAt P P' δ) (T : MeanTree ι) :
    HasDerivAt (fun s => T.eval (Function.update A j (P s)))
      (T.derivLabel (Function.update A j (P δ)) j P') δ := by
  have hIn : ∀ s i, (Function.update A j (P s) i).PosDef := fun s i => by
    by_cases hij : i = j
    · subst hij; simpa using hPd s
    · simpa [Function.update_of_ne hij] using hA i
  induction T with
  | leaf i =>
    by_cases hij : i = j
    · subst hij
      simpa [derivLabel] using hP
    · simpa [derivLabel, hij, Function.update_of_ne hij] using
        hasDerivAt_const (𝕜 := ℝ) δ (A i)
  | node r l rr ihl ihr =>
    have h := hasDerivAt_geomMean_of_hasDerivAt r.2 ihl ihr
      (fun s => isHermitian_eval (fun i => (hIn s i).isHermitian) l)
      (fun s => isHermitian_eval (fun i => (hIn s i).isHermitian) rr)
      (posDef_eval (hIn δ) l) (posDef_eval (hIn δ) rr)
    simpa [derivLabel, eval_node] using h

end MeanTree

namespace Transport

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The perturbation `A^{1/2} e^{δ Q} A^{1/2}` of a positive definite `A` in the direction of
a Hermitian `Q`, with `e^{δ Q}` written as `C^δ` for `C = e^Q`. -/
def leafPerturbation (A Q : Matrix n n ℂ) (δ : ℝ) : Matrix n n ℂ :=
  A ^ (1 / 2 : ℝ) * cfc Real.exp Q ^ δ * A ^ (1 / 2 : ℝ)

theorem posDef_cfc_exp {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) : (cfc Real.exp Q).PosDef :=
  Matrix.isStrictlyPositive_iff_posDef.mp
    ((cfc_isStrictlyPositive_iff Real.exp Q (Real.continuous_exp.continuousOn)
      hQ.isSelfAdjoint).mpr fun x _ => Real.exp_pos x)

theorem log_cfc_exp {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) : CFC.log (cfc Real.exp Q) = Q := by
  rw [CFC.real_exp_eq_normedSpace_exp hQ.isSelfAdjoint, CFC.log_exp Q hQ.isSelfAdjoint]

theorem posDef_leafPerturbation {A Q : Matrix n n ℂ} (hA : A.PosDef) (hQ : Q.IsHermitian)
    (δ : ℝ) : (leafPerturbation A Q δ).PosDef := by
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := cfc Real.exp Q ^ δ)
    (hA.rpow (1 / 2 : ℝ)).isUnit).mpr ((posDef_cfc_exp hQ).rpow δ)
  rwa [star_eq_conjTranspose, (hA.rpow (1 / 2 : ℝ)).isHermitian.eq] at h

theorem leafPerturbation_zero {A Q : Matrix n n ℂ} (hA : A.PosDef) (hQ : Q.IsHermitian) :
    leafPerturbation A Q 0 = A := by
  rw [leafPerturbation, (posDef_cfc_exp hQ).rpow_zero, Matrix.mul_one,
    hA.rpow_half_mul_rpow_half]

theorem hasDerivAt_leafPerturbation {A Q : Matrix n n ℂ} (hQ : Q.IsHermitian) :
    HasDerivAt (leafPerturbation A Q) (A ^ (1 / 2 : ℝ) * Q * A ^ (1 / 2 : ℝ)) 0 := by
  have h := (((posDef_cfc_exp hQ).hasDerivAt_rpow_exponent 0).const_mul (A ^ (1 / 2 : ℝ))).mul_const
    (A ^ (1 / 2 : ℝ))
  rwa [(posDef_cfc_exp hQ).rpow_zero, Matrix.one_mul, log_cfc_exp hQ] at h

/-- **A transport-state expectation as a derivative.** For positive definite inputs, a leaf
`j` of nonzero weight, a Hermitian `Q` and a nonzero `pre`, perturbing the input at `j` along
`A_j^{1/2} e^{δ Q} A_j^{1/2}` changes `-log N²` at rate `w_j ∫ m_{1/4}(u) Tr(σ_{j,u} Q) du`
(`06-transport.tex` lines 470--494). -/
theorem hasDerivAt_neg_log_filteredNormSq_leafPerturbation {J : Type*} [DecidableEq J]
    (T : MeanTree J) {A : J → Matrix n n ℂ} (hA : ∀ i, (A i).PosDef) {j : J}
    (hw : T.weight j ≠ 0) {Q : Matrix n n ℂ} (hQ : Q.IsHermitian) {pre : n → ℂ}
    (hpre : pre ≠ 0) :
    HasDerivAt (fun δ => -Real.log (filteredNormSq
        (T.eval (Function.update A j (leafPerturbation (A j) Q δ))) pre))
      (T.weight j * ∫ u, fourierWeight u *
        (transportState T A (filteredVector (T.eval A) pre) j u * Q).trace.re) 0 := by
  have hPd := posDef_leafPerturbation (hA j) hQ
  have hup : Function.update A j (leafPerturbation (A j) Q 0) = A := by
    rw [leafPerturbation_zero (hA j) hQ, Function.update_eq_self]
  have hIn : ∀ s i, (Function.update A j (leafPerturbation (A j) Q s) i).PosDef := fun s i => by
    by_cases hij : i = j
    · subst hij; simpa using hPd s
    · simpa [Function.update_of_ne hij] using hA i
  have hD := MeanTree.hasDerivAt_eval_update_path hA j hPd (hasDerivAt_leafPerturbation hQ) T
  rw [hup] at hD
  have h1 := hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt
    (fun s => MeanTree.posDef_eval (hIn s) T) hD hpre
  simp only [hup] at h1
  convert h1 using 1
  rw [MeanTree.sandwich_derivLabel_eq_smul_leafMap T hw Q, ← integral_const_mul]
  congr 1
  funext u
  set w := imagPow (T.eval A) u *ᵥ filteredVector (T.eval A) pre
  have e := star_dotProduct_mulVec_eq_trace_traceAdjointMap (T.leafMap A j).toLinearMap Q w
  rw [smul_mulVec, dotProduct_smul, Complex.smul_re,
    show (transportState T A (filteredVector (T.eval A) pre) j u * Q).trace =
      star w ⬝ᵥ ((T.leafMap A j) Q *ᵥ w) from e.symm, smul_eq_mul]
  ring

end Transport

end Matrix
