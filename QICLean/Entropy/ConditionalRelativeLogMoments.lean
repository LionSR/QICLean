/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.ConditionalMovementEstimate

/-!
# Conditional logarithmic moments

For a density matrix on `X ⊗ U`, the two-eigenbasis relative logarithmic law has
exponential moments controlled by `dim X`. Its signed logarithmic moment-generating
function and the corresponding conditional Schatten quantity obey quadratic bounds
with universal constants, independently of `dim U`. The marginal is completed by
the identity on its kernel; the density itself may be singular.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, Section 5.1, `04-conditional.tex`, lines 33–114, in particular
  `eq:conditional-log-moments`, `eq:conditional-log-mgf`, and
  `eq:conditional-schatten`; revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The two-eigenbasis entropy calculation adapts `spectral_mean_eq_neg_entropy`
from openai/math (Apache-2.0), commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`lean/OAI/MathematicalPhysics/PEPSMove/FilterEntropy.lean`.
The present argument uses the eigenbasis of the actual marginal, treats its
zero eigenspaces explicitly, and states both exponential-moment bounds.
The signed logarithmic estimate applies the existing relative-logarithm bounds.
The Schatten estimate transports the completed marginal to its eigenbasis and
applies the common filtered Gram estimate in
`ConditionalMovement.ConditionalCollision.conditional_gramMoment_bounds`,
extracted from the corresponding argument in the same upstream revision,
`lean/OAI/MathematicalPhysics/PEPSMove/Optimizer.lean`.
-/

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
open Matrix

namespace Entropy

variable {X U : Type*} [Fintype X] [Fintype U] [DecidableEq X] [DecidableEq U]

/-- The two-eigenbasis relative logarithmic law is a probability law, its mean is
minus the conditional entropy, and both exponential moments are at most the
dimension of the first subsystem. The chosen marginal eigenbasis respects the
support of the marginal, including when that marginal is singular.
Source: area-law manuscript, `04-conditional.tex`, lines 33–67,
`eq:conditional-log-moments`. -/
theorem conditional_relative_log_moments
    (ρ : Matrix (X × U) (X × U) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    let σ := partialTraceLeft ρ
    let hσ : σ.IsHermitian := partialTraceLeft_isHermitian hρ.isHermitian
    let p : X × U → ℝ := hρ.isHermitian.eigenvalues
    let r : U → ℝ := hσ.eigenvalues
    let V : Matrix (X × U) (X × U) ℂ :=
      (1 : Matrix X X ℂ) ⊗ₖ (hσ.eigenvectorUnitary : Matrix U U ℂ)
    let T := V.conjTranspose *
      (hρ.isHermitian.eigenvectorUnitary : Matrix (X × U) (X × U) ℂ)
    let w : ((X × U) × (X × U)) → ℝ :=
      fun ji => p ji.2 * Complex.normSq (T ji.1 ji.2)
    let L : ((X × U) × (X × U)) → ℝ :=
      fun ji => Real.log (p ji.2) -
        Real.log (if r ji.1.2 = 0 then (1 : ℝ) else r ji.1.2)
    (∀ v, 0 ≤ w v) ∧ (∑ v, w v) = 1 ∧
      (∑ v, w v * L v) = -conditionalEntropy ρ hρ.isHermitian ∧
      (∑ v, w v * Real.exp (L v)) ≤ (Fintype.card X : ℝ) ∧
      (∑ v, w v * Real.exp (-L v)) ≤ (Fintype.card X : ℝ) := by
  classical
  intro σ hσ p r V T w L
  let TU := star (ConditionalMovement.QuantumSSA.tensorRightUnitary (m := X)
    hσ.eigenvectorUnitary) * hρ.isHermitian.eigenvectorUnitary
  have hT : (TU : Matrix (X × U) (X × U) ℂ) = T := rfl
  let A := V.conjTranspose * ρ * V
  have hdec : A = ConditionalMovement.SpectralCurve.spectralHom TU
      (fun i => (p i : ℂ)) := by
    simpa only [Function.comp_def, RCLike.ofReal_eq_complex_ofReal,
      Unitary.conjStarAlgAut_apply, A, ConditionalMovement.SpectralCurve.spectralHom_apply,
      hT, T, p,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc] using
      congrArg (fun B : Matrix (X × U) (X × U) ℂ => V.conjTranspose * B * V)
        hρ.isHermitian.spectral_theorem
  have hrot : ConditionalMovement.QuantumSSA.ptrL A =
      (hσ.eigenvectorUnitary : Matrix U U ℂ).conjTranspose * σ *
        (hσ.eigenvectorUnitary : Matrix U U ℂ) := by
    simpa only [A, V, StarAlgHom.coe_mk,
      ConditionalMovement.QuantumSSA.tensorRightHom,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose] using
      (ConditionalMovement.QuantumSSA.ptrL_rotate ρ
        (hσ.eigenvectorUnitary : Matrix U U ℂ).conjTranspose).trans
        (congrArg (fun B : Matrix U U ℂ =>
          (hσ.eigenvectorUnitary : Matrix U U ℂ).conjTranspose * B *
            ((hσ.eigenvectorUnitary : Matrix U U ℂ).conjTranspose).conjTranspose)
          (show ConditionalMovement.QuantumSSA.ptrL ρ = σ from rfl))
  have hdiagMarg : ConditionalMovement.QuantumSSA.ptrL A =
      Matrix.diagonal (fun u : U => (r u : ℂ)) :=
    hrot.trans (ConditionalMovement.QuantumSSA.spectral_diagonalize σ hσ)
  have hApos : A.PosSemidef := hρ.conjTranspose_mul_mul_same V
  have hW : ConditionalMovement.ConditionalCollision.uncoefficient (CFC.sqrt A) *
      (ConditionalMovement.ConditionalCollision.uncoefficient (CFC.sqrt A)).conjTranspose =
        Matrix.diagonal (fun u : U => (r u : ℂ)) := by
    simpa only [ConditionalMovement.ConditionalCollision.uncoefficient_gram,
      Matrix.conjTranspose_cfc_sqrt, CFC.sqrt_mul_sqrt_self A hApos.nonneg] using hdiagMarg
  have hsumr : (∑ u : U, r u) = 1 :=
    posSemidef_trace_one_eigenvalues_sum_one hρ.partialTraceLeft
      ((trace_partialTraceLeft ρ).trans htr)
  have hcollisionMatrix :
      (∑ j : X × U, ∑ k : X × U, ‖A j k‖ ^ 2 / r k.2) ≤
        (Fintype.card X : ℝ) := by
    simpa only [ConditionalMovement.ConditionalCollision.coefficient_uncoefficient,
      Matrix.conjTranspose_cfc_sqrt, CFC.sqrt_mul_sqrt_self A hApos.nonneg,
      hsumr, mul_one] using
      ConditionalMovement.ConditionalCollision.collision_le
        (ConditionalMovement.ConditionalCollision.uncoefficient (CFC.sqrt A)) r
        hρ.partialTraceLeft.eigenvalues_nonneg hW
  have hsquare : A * A = ConditionalMovement.SpectralCurve.spectralHom TU
      (fun i => (((p i) ^ 2 : ℝ) : ℂ)) := by
    simpa only [hdec, Pi.mul_def, Pi.mul_apply, Complex.ofReal_pow,
      Complex.ofReal_mul, pow_two] using
      (map_mul (ConditionalMovement.SpectralCurve.spectralHom TU)
        (fun i => (p i : ℂ)) (fun i => (p i : ℂ))).symm
  have hcolNorm (j : X × U) :
      ((A.conjTranspose * A) j j).re = ∑ k : X × U, ‖A k j‖ ^ 2 := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum,
      RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hdiagSquare (j : X × U) :
      (∑ i : X × U, (p i) ^ 2 * Complex.normSq (T j i)) = ((A * A) j j).re := by
    simpa only [hsquare, ConditionalMovement.SpectralCurve.spectralHom_apply,
      Matrix.star_eq_conjTranspose, hT, mul_comm] using
      (ConditionalMovement.MatrixEntropy.diagonal_conjugate T (fun i => (p i) ^ 2) j).symm
  have hcolumn (j : X × U) :
      (∑ i : X × U, (p i) ^ 2 * Complex.normSq (T j i)) =
        ∑ k : X × U, ‖A k j‖ ^ 2 :=
    (hdiagSquare j).trans
      ((congrArg (fun M : Matrix (X × U) (X × U) ℂ => ((M * A) j j).re)
        hApos.isHermitian.eq.symm).trans (hcolNorm j))
  have hcollision :
      (∑ j : X × U, ∑ i : X × U, (p i) ^ 2 * Complex.normSq (T j i) / r j.2) ≤
        (Fintype.card X : ℝ) := by
    simpa only [← Finset.sum_div, hcolumn] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun j k : X × U => ‖A k j‖ ^ 2 / r j.2)).le.trans hcollisionMatrix
  have hdiag (j : X × U) : (A j j).re =
      ∑ i : X × U, p i * Complex.normSq (T j i) := by
    simpa only [hdec, ConditionalMovement.SpectralCurve.spectralHom_apply,
      Matrix.star_eq_conjTranspose, hT, mul_comm] using
      ConditionalMovement.MatrixEntropy.diagonal_conjugate T p j
  have hmarg (u : U) :
      (∑ x : X, ∑ i : X × U, p i * Complex.normSq (T (x, u) i)) = r u := by
    simpa only [ConditionalMovement.QuantumSSA.ptrL, Complex.re_sum,
      Matrix.diagonal_apply_eq, Complex.ofReal_re, hdiag] using
      congrArg (fun M : Matrix U U ℂ => (M u u).re) hdiagMarg
  have hcol (i : X × U) : (∑ j : X × U, Complex.normSq (T j i)) = 1 := by
    simpa only [hT] using ConditionalMovement.MatrixEntropy.unitary_col_normSq TU i
  have hpsum : (∑ i : X × U, p i) = 1 :=
    posSemidef_trace_one_eigenvalues_sum_one hρ htr
  have hmass : (∑ v, w v) = 1 :=
    (Fintype.sum_prod_type_right w).trans (by
      simpa only [w, ← Finset.mul_sum, hcol, mul_one] using hpsum)
  have hz (j : X × U) (hr0 : r j.2 = 0) (i : X × U) :
      p i * Complex.normSq (T j i) = 0 :=
    le_antisymm
      (((Finset.single_le_sum (s := Finset.univ)
        (f := fun k : X × U => p k * Complex.normSq (T j k))
        (fun k _ => mul_nonneg (hρ.eigenvalues_nonneg k) (Complex.normSq_nonneg (T j k)))
        (Finset.mem_univ i)).trans
          (Finset.single_le_sum (s := Finset.univ)
            (f := fun x : X => ∑ k : X × U, p k * Complex.normSq (T (x, j.2) k))
            (fun x _ => Finset.sum_nonneg (fun k _ =>
              mul_nonneg (hρ.eigenvalues_nonneg k) (Complex.normSq_nonneg (T (x, j.2) k))))
            (Finset.mem_univ j.1))).trans_eq ((hmarg j.2).trans hr0))
      (mul_nonneg (hρ.eigenvalues_nonneg i) (Complex.normSq_nonneg (T j i)))
  have hlog (u : U) :
      Real.log (if r u = 0 then (1 : ℝ) else r u) = Real.log (r u) := by
    by_cases hr0 : r u = 0 <;> simp [hr0]
  have hfirst :
      (∑ j : X × U, ∑ i : X × U, p i * Complex.normSq (T j i) * Real.log (p i)) =
        ∑ i : X × U, p i * Real.log (p i) :=
    (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun j i : X × U => p i * Complex.normSq (T j i) * Real.log (p i))).trans (by
        simp only [← Finset.sum_mul, ← Finset.mul_sum, hcol, mul_one])
  have hsecond :
      (∑ j : X × U, ∑ i : X × U, p i * Complex.normSq (T j i) * Real.log (r j.2)) =
        ∑ u : U, r u * Real.log (r u) :=
    (Fintype.sum_prod_type_right (fun j : X × U =>
      ∑ i : X × U, p i * Complex.normSq (T j i) * Real.log (r j.2))).trans (by
        simp only [← Finset.sum_mul, hmarg])
  have hmean : (∑ v, w v * L v) = -conditionalEntropy ρ hρ.isHermitian :=
    (Fintype.sum_prod_type (fun v => w v * L v)).trans (by
      simp only [w, L, hlog, mul_sub, Finset.sum_sub_distrib, hfirst, hsecond,
        conditionalEntropy, vonNeumannEntropy, Real.negMulLog_eq_neg, Finset.sum_neg_distrib,
        neg_sub, neg_sub_neg, p, r])
  have hplus (j i : X × U) :
      p i * Complex.normSq (T j i) * Real.exp (Real.log (p i) - Real.log (r j.2)) =
        (p i) ^ 2 * Complex.normSq (T j i) / r j.2 := by
    by_cases hpz : p i = 0
    · simp [hpz]
    · by_cases hrz : r j.2 = 0
      · simp [hrz, hz j hrz i]
      · rw [Real.exp_sub,
          Real.exp_log (lt_of_le_of_ne (hρ.eigenvalues_nonneg i) (Ne.symm hpz)),
          Real.exp_log (lt_of_le_of_ne
            (hρ.partialTraceLeft.eigenvalues_nonneg j.2) (Ne.symm hrz))]
        ring
  have hminus (j i : X × U) :
      p i * Complex.normSq (T j i) * Real.exp (-(Real.log (p i) - Real.log (r j.2))) ≤
        r j.2 * Complex.normSq (T j i) := by
    by_cases hpz : p i = 0
    · simpa only [hpz, zero_mul] using
        mul_nonneg (show 0 ≤ r j.2 from hρ.partialTraceLeft.eigenvalues_nonneg j.2)
          (Complex.normSq_nonneg (T j i))
    · by_cases hrz : r j.2 = 0
      · simp [hrz, hz j hrz i]
      · rw [neg_sub, Real.exp_sub,
          Real.exp_log (show 0 < r j.2 from lt_of_le_of_ne
            (hρ.partialTraceLeft.eigenvalues_nonneg j.2) (Ne.symm hrz)),
          Real.exp_log (show 0 < p i from
            lt_of_le_of_ne (hρ.eigenvalues_nonneg i) (Ne.symm hpz))]
        exact le_of_eq (by field_simp)
  have hrow (j : X × U) : (∑ i : X × U, Complex.normSq (T j i)) = 1 := by
    simpa only [hT] using ConditionalMovement.MatrixEntropy.unitary_row_normSq TU j
  have hpos : (∑ v, w v * Real.exp (L v)) ≤ (Fintype.card X : ℝ) :=
    (Fintype.sum_prod_type (fun v => w v * Real.exp (L v))).le.trans (by
      simpa only [w, L, hlog, hplus] using hcollision)
  have htotal : (∑ j : X × U, r j.2) = (Fintype.card X : ℝ) :=
    (Fintype.sum_prod_type (fun j : X × U => r j.2)).trans (by
      simp only [hsumr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one])
  have hneg : (∑ v, w v * Real.exp (-L v)) ≤ (Fintype.card X : ℝ) :=
    (Fintype.sum_prod_type (fun v => w v * Real.exp (-L v))).le.trans (by
      simpa only [w, L, hlog] using
        (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun i _ => hminus j i))).trans_eq
          (by simpa only [← Finset.mul_sum, hrow, mul_one] using htotal))
  exact ⟨fun v => mul_nonneg (hρ.eigenvalues_nonneg v.2)
    (Complex.normSq_nonneg (T v.1 v.2)), hmass, hmean, hpos, hneg⟩

/-- The signed logarithmic moment-generating function and its tilted second moment
have universal quadratic and second-moment bounds, respectively. The constants
are independent of both coordinate spaces, and only the dimension of the first
subsystem enters the scale `1 + log (dim X)`.
Source: area-law manuscript, `04-conditional.tex`, lines 69–82, including the
tilted second-moment display at lines 73–75 and `eq:conditional-log-mgf`. -/
theorem conditional_relative_log_mgf_le
    (ρ : Matrix (X × U) (X × U) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (b : ℝ) (hsmall : |b| * (1 + Real.log (Fintype.card X : ℝ)) ≤ (1 : ℝ) / 8) :
    let σ := partialTraceLeft ρ
    let hσ : σ.IsHermitian := partialTraceLeft_isHermitian hρ.isHermitian
    let p : X × U → ℝ := hρ.isHermitian.eigenvalues
    let r : U → ℝ := hσ.eigenvalues
    let V : Matrix (X × U) (X × U) ℂ :=
      (1 : Matrix X X ℂ) ⊗ₖ (hσ.eigenvectorUnitary : Matrix U U ℂ)
    let T := V.conjTranspose *
      (hρ.isHermitian.eigenvectorUnitary : Matrix (X × U) (X × U) ℂ)
    let w : ((X × U) × (X × U)) → ℝ :=
      fun ji => p ji.2 * Complex.normSq (T ji.1 ji.2)
    let L : ((X × U) × (X × U)) → ℝ :=
      fun ji => Real.log (p ji.2) -
        Real.log (if r ji.1.2 = 0 then (1 : ℝ) else r ji.1.2)
    Real.log (∑ v, w v * Real.exp (b * L v)) ≤
        -b * conditionalEntropy ρ hρ.isHermitian +
          (256 * Real.exp 1 + 512) * b ^ 2 *
            (1 + Real.log (Fintype.card X : ℝ)) ^ 2 ∧
      (∑ v, w v * ((L v) ^ 2 * Real.exp (|b * L v|))) ≤
        (256 * Real.exp 1 + 512) * (1 + Real.log (Fintype.card X : ℝ)) ^ 2 := by
  classical
  intro σ hσ p r V T w L
  rcases (show (∀ v, 0 ≤ w v) ∧ (∑ v, w v) = 1 ∧
      (∑ v, w v * L v) = -conditionalEntropy ρ hρ.isHermitian ∧
      (∑ v, w v * Real.exp (L v)) ≤ (Fintype.card X : ℝ) ∧
      (∑ v, w v * Real.exp (-L v)) ≤ (Fintype.card X : ℝ) from
        conditional_relative_log_moments ρ hρ htr) with ⟨hw, hs, hmean, hpos, hneg⟩
  have hD : 1 ≤ (Fintype.card X : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (@Fintype.card_pos X _
      (Matrix.PosSemidef.nonempty_of_trace_eq_one
        ((Matrix.trace_partialTraceRight ρ).trans htr)))
  have hl : 0 ≤ Real.log (Fintype.card X : ℝ) := Real.log_nonneg hD
  have hexps :
      (∑ v, w v * Real.exp (L v)) ≤ Real.exp (Real.log (Fintype.card X : ℝ)) ∧
      (∑ v, w v * Real.exp (-L v)) ≤ Real.exp (Real.log (Fintype.card X : ℝ)) := by
    simpa only [Real.exp_log (lt_of_lt_of_le zero_lt_one hD)] using And.intro hpos hneg
  have hpar : |b| ≤ (1 : ℝ) / 2 ∧ |b| * Real.log (Fintype.card X : ℝ) ≤ 1 := by
    constructor <;> nlinarith only [hsmall, abs_nonneg b, mul_nonneg (abs_nonneg b) hl]
  have hcoef : 3 * (16 * Real.exp 1 * (Real.log (Fintype.card X : ℝ)) ^ 2 + 32) ≤
      (256 * Real.exp 1 + 512) * (1 + Real.log (Fintype.card X : ℝ)) ^ 2 := by
    nlinarith only [hl, Real.exp_nonneg 1, sq_nonneg (Real.log (Fintype.card X : ℝ)),
      mul_nonneg (Real.exp_nonneg 1) hl,
      mul_nonneg (Real.exp_nonneg 1) (sq_nonneg (Real.log (Fintype.card X : ℝ)))]
  have htilt : (∑ v, w v * ((L v) ^ 2 * Real.exp (|b * L v|))) ≤
      (256 * Real.exp 1 + 512) * (1 + Real.log (Fintype.card X : ℝ)) ^ 2 := by
    simpa only [abs_mul] using
      (ConditionalMovement.RelativeLogMoment.tilted_second_moment w L hw hs
        (Real.log (Fintype.card X : ℝ)) hl hexps.1 hexps.2 |b| (abs_nonneg b)
        hpar.1 hpar.2).trans (show
          16 * Real.exp 1 * (Real.log (Fintype.card X : ℝ)) ^ 2 + 32 ≤
            (256 * Real.exp 1 + 512) * (1 + Real.log (Fintype.card X : ℝ)) ^ 2 from by
          nlinarith only [hcoef,
            mul_nonneg (Real.exp_nonneg 1) (sq_nonneg (Real.log (Fintype.card X : ℝ)))])
  have hmgf : (∑ v, w v * Real.exp (b * L v)) ≤
      Real.exp (b * (∑ v, w v * L v) +
        3 * b ^ 2 * (16 * Real.exp 1 * (Real.log (Fintype.card X : ℝ)) ^ 2 + 32)) := by
    by_cases hb : 0 ≤ b
    · exact ConditionalMovement.RelativeLogMoment.mgf_bound w L hw hs
        (Real.log (Fintype.card X : ℝ)) hl hexps.1 hexps.2 b hb
        (by simpa only [abs_of_nonneg hb] using hpar.1)
        (by simpa only [abs_of_nonneg hb] using hpar.2)
    · simpa only [mul_neg, neg_mul, neg_neg, neg_sq, Finset.sum_neg_distrib] using
        ConditionalMovement.RelativeLogMoment.mgf_bound w (fun v => -L v) hw hs
          (Real.log (Fintype.card X : ℝ)) hl hexps.2
          (by simpa only [neg_neg] using hexps.1) (-b)
          (le_of_lt (neg_pos.mpr (lt_of_not_ge hb)))
          (by simpa only [abs_of_neg (lt_of_not_ge hb)] using hpar.1)
          (by simpa only [abs_of_neg (lt_of_not_ge hb)] using hpar.2)
  have hMpos : 0 < ∑ v, w v * Real.exp (b * L v) :=
    (Real.exp_pos _).trans_le
      (ConditionalMovement.MatrixInterpolation.mgf_lower w (fun v => b * L v) hw hs)
  refine ⟨(Real.log_le_iff_le_exp hMpos).2
    (hmgf.trans (Real.exp_le_exp.mpr ?_)), htilt⟩
  rw [hmean]
  nlinarith only [mul_le_mul_of_nonneg_left hcoef (sq_nonneg b)]

/-- The conditional Schatten quantity formed with the actual completed marginal
is positive and has the logarithmic entropy bound. The numerical constants are
universal, and no invertibility of the density or its marginal is required.
Source: area-law manuscript, `04-conditional.tex`, lines 84–114,
`eq:conditional-schatten`. -/
theorem conditional_schatten_log_le
    (ρ : Matrix (X × U) (X × U) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (a : ℝ) (ha : 0 < a)
    (hsmall : a * (1 + Real.log (Fintype.card X : ℝ)) ≤ (1 : ℝ) / 8) :
    let σ := partialTraceLeft ρ
    let Q : Matrix (X × U) (X × U) ℂ :=
      (1 : Matrix X X ℂ) ⊗ₖ kernelCompletion σ
    let B := cfc (fun x : ℝ => x ^ (-a)) Q
    let K := B * ρ * B
    let α : ℝ := 1 / (1 - 2 * a)
    let Z : ℝ := ((cfc (fun x : ℝ => x ^ α) K).trace.re) ^ (1 / α)
    0 < Z ∧ Real.log Z ≤
      -2 * a * conditionalEntropy ρ hρ.isHermitian +
        (256 * Real.exp 1 + 512) * a ^ 2 *
          (1 + Real.log (Fintype.card X : ℝ)) ^ 2 := by
  classical
  intro σ Q B K α Z
  have hGram (R C : Matrix (X × U) (X × U) ℂ) :
      (R * C) * (R * C).conjTranspose = R * (C * C.conjTranspose) * R.conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hC : CFC.sqrt ρ * (CFC.sqrt ρ).conjTranspose = ρ := by
    simpa only [Matrix.conjTranspose_cfc_sqrt] using CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hsupp : ((1 : Matrix X X ℂ) ⊗ₖ Matrix.kernelProjection σ) * CFC.sqrt ρ = 0 := by
    simpa only [hC, show ConditionalMovement.QuantumSSA.ptrL ρ = σ from rfl] using
      Entropy.one_kronecker_kernelProjection_mul (CFC.sqrt ρ)
  have hσ : σ.PosSemidef := hρ.partialTraceLeft
  have hcompletion : (Matrix.kernelCompletion σ).IsHermitian :=
    hσ.isHermitian.add (Matrix.kernelProjection_isHermitian σ)
  have hBC : B * CFC.sqrt ρ =
      ((1 : Matrix X X ℂ) ⊗ₖ cfc (fun t : ℝ => t ^ (-a)) σ) * CFC.sqrt ρ := by
    simp only [B, Q, Matrix.cfc_one_kronecker hcompletion,
      Matrix.cfc_rpow_kernelCompletion hσ.isHermitian (neg_ne_zero.mpr ha.ne'),
      Matrix.kronecker_add, Matrix.add_mul, hsupp, add_zero]
  have hB : B.IsHermitian :=
    (cfc_predicate (fun t : ℝ => t ^ (-a)) Q : IsSelfAdjoint B)
  have hBCGram : (B * CFC.sqrt ρ) * (B * CFC.sqrt ρ).conjTranspose = K := by
    simpa only [hC, hB.eq, K] using hGram B (CFC.sqrt ρ)
  let Vunit := ConditionalMovement.QuantumSSA.tensorRightUnitary (m := X)
    hσ.isHermitian.eigenvectorUnitary
  let r : U → ℝ := hσ.isHermitian.eigenvalues
  let D := star (Vunit : Matrix (X × U) (X × U) ℂ) * CFC.sqrt ρ
  let W := ConditionalMovement.ConditionalCollision.uncoefficient D
  have hDgram : D * D.conjTranspose =
      star (Vunit : Matrix (X × U) (X × U) ℂ) * ρ *
        (Vunit : Matrix (X × U) (X × U) ℂ) := by
    simpa only [D, hC, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose] using
      hGram (star (Vunit : Matrix (X × U) (X × U) ℂ)) (CFC.sqrt ρ)
  have hrot : ConditionalMovement.QuantumSSA.ptrL (D * D.conjTranspose) =
      star (hσ.isHermitian.eigenvectorUnitary : Matrix U U ℂ) * σ *
        (hσ.isHermitian.eigenvectorUnitary : Matrix U U ℂ) := by
    simpa only [D, Vunit, ConditionalMovement.QuantumSSA.tensorRightUnitary_star,
      Unitary.coe_star, OneMemClass.coe_one, Matrix.mul_one, hC,
      show ConditionalMovement.QuantumSSA.ptrL ρ = σ from rfl, star_star,
      StarAlgHom.coe_mk] using
      ConditionalMovement.QuantumSSA.ptrL_gram_rotate (CFC.sqrt ρ)
        (star hσ.isHermitian.eigenvectorUnitary)
        (1 : unitary (Matrix (X × U) (X × U) ℂ))
  have hW : W * W.conjTranspose = Matrix.diagonal (fun u : U => (r u : ℂ)) :=
    (ConditionalMovement.ConditionalCollision.uncoefficient_gram D).trans
      (hrot.trans (ConditionalMovement.QuantumSSA.spectral_diagonalize σ hσ.isHermitian))
  have hsum : (∑ u : U, r u) = 1 :=
    posSemidef_trace_one_eigenvalues_sum_one hσ ((trace_partialTraceLeft ρ).trans htr)
  have hdensity : ConditionalMovement.ConditionalCollision.density W =
      D * D.conjTranspose := rfl
  have hSrot : ConditionalMovement.QuantumSSA.conditionalEntropy (D * D.conjTranspose) =
      ConditionalMovement.QuantumSSA.conditionalEntropy ρ := by
    simpa only [D, Vunit, ConditionalMovement.QuantumSSA.tensorRightUnitary_star,
      Unitary.coe_star, OneMemClass.coe_one, Matrix.mul_one, hC,
      StarAlgHom.coe_mk] using
      ConditionalMovement.QuantumSSA.conditional_gram_rotate (CFC.sqrt ρ)
        (star hσ.isHermitian.eigenvectorUnitary)
        (1 : unitary (Matrix (X × U) (X × U) ℂ))
  have hS : ConditionalMovement.ConditionalCollision.conditionalEntropy W r =
      conditionalEntropy ρ hρ.isHermitian :=
    (ConditionalMovement.ConditionalCollision.conditionalEntropy_eq W r hW).trans
      ((congrArg ConditionalMovement.QuantumSSA.conditionalEntropy hdensity).trans
        (hSrot.trans (conditionalEntropy_eq_quantumSSA ρ hρ.isHermitian).symm))
  let : Nonempty X := Matrix.PosSemidef.nonempty_of_trace_eq_one
    ((Matrix.trace_partialTraceRight ρ).trans htr)
  have hl : 0 ≤ Real.log (Fintype.card X : ℝ) := Real.log_nonneg
    (by exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := X))))
  have ha8 : a ≤ (1 : ℝ) / 8 := by
    nlinarith only [hsmall, mul_nonneg ha.le hl]
  have hsmall' : (2 * a / (1 - 2 * a)) * Real.log (Fintype.card X : ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 1 - 2 * a by linarith only [ha8])).mpr
    nlinarith only [hsmall]
  let hA : (ConditionalMovement.ConditionalCollision.density W).IsHermitian :=
    (ConditionalMovement.ConditionalCollision.density_pos W).isHermitian
  let P := ConditionalMovement.SupportedCurve.power hA.eigenvectorUnitary hA.eigenvalues
    ((1 / 2 : ℝ) : ℂ)
  let F := ConditionalMovement.SupportedCurve.power
    (1 : unitary (Matrix (X × U) (X × U) ℂ)) (fun j : X × U => r j.2)
    ((-(2 * a) / 2 : ℝ) : ℂ)
  let A := F * P
  obtain ⟨_, hG, hu⟩ :=
    ConditionalMovement.ConditionalCollision.conditional_gramMoment_bounds
      W r hσ.eigenvalues_nonneg hW hsum (2 * a) (by positivity)
      (by linarith only [ha8]) hsmall'
  let E := (1 : Matrix X X ℂ) ⊗ₖ cfc (fun t : ℝ => t ^ (-a)) σ
  have hFherm : F.IsHermitian :=
    ConditionalMovement.MatrixInterpolation.power_real_hermitian _ _ _
  have hE : E = (Vunit : Matrix (X × U) (X × U) ℂ) * F *
      star (Vunit : Matrix (X × U) (X × U) ℂ) := by
    have hexponent : -(2 * a) / 2 = -a := by ring
    calc
      E = ConditionalMovement.QuantumSSA.tensorRightHom (m := X)
          (ConditionalMovement.SupportedCurve.power hσ.isHermitian.eigenvectorUnitary r
            ((-(2 * a) / 2 : ℝ) : ℂ)) := by
        rw [hexponent, ConditionalMovement.SupportedCurve.power_real_eq_cfc
          hσ (-a) (neg_ne_zero.mpr ha.ne')]
        rfl
      _ = ConditionalMovement.SupportedCurve.power Vunit
          (fun j : X × U => r j.2) ((-(2 * a) / 2 : ℝ) : ℂ) :=
        (ConditionalMovement.QuantumSSA.tensorRight_power (m := X)
          hσ.isHermitian.eigenvectorUnitary r ((-(2 * a) / 2 : ℝ) : ℂ)).symm
      _ = _ := by
        simpa only [mul_one, F] using
          ConditionalMovement.QuantumSSA.power_left_unitary Vunit
            (1 : unitary (Matrix (X × U) (X × U) ℂ))
            (fun j : X × U => r j.2) ((-(2 * a) / 2 : ℝ) : ℂ)
  have hEherm : E.IsHermitian := by
    rw [hE, Matrix.star_eq_conjTranspose]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ hFherm
  have hKbase : K = E * ρ * E := by
    rw [← hBCGram, hBC, hGram, hC, hEherm.eq]
  have hPgram : P * P.conjTranspose =
      ConditionalMovement.ConditionalCollision.density W :=
    ConditionalMovement.ConditionalCollision.gram_root W
  have hAgram : A * A.conjTranspose =
      F * ConditionalMovement.ConditionalCollision.density W * F := by
    simpa only [A, hPgram, hFherm.eq] using hGram F P
  have hKconj : K = (Vunit : Matrix (X × U) (X × U) ℂ) *
      (A * A.conjTranspose) * star (Vunit : Matrix (X × U) (X × U) ℂ) := by
    simp only [hKbase, hAgram, hdensity, hDgram, hE, Matrix.mul_assoc]
  have htrace : (cfc (fun t : ℝ => t ^ α) K).trace.re =
      ConditionalMovement.MatrixInterpolation.gramMoment A α := by
    rw [hKconj, Matrix.cfc_conj_unitary
      (Matrix.posSemidef_self_mul_conjTranspose A).isHermitian _ Vunit,
      Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
      ConditionalMovement.QuantumSSA.trace_cfc _
        (Matrix.posSemidef_self_mul_conjTranspose A).isHermitian]
    simp only [ConditionalMovement.MatrixInterpolation.gramMoment,
      Complex.re_sum, Complex.ofReal_re]
  have hZeq : Z =
      ConditionalMovement.MatrixInterpolation.gramMoment A (1 / (1 - 2 * a)) ^
        (1 - 2 * a) := by
    simpa only [Z, α, one_div_one_div] using
      congrArg (fun t : ℝ => t ^ (1 / α)) htrace
  have hZ : 0 < Z := by
    simpa only [hZeq] using Real.rpow_pos_of_pos hG (1 - 2 * a)
  have hcoef : 3 * (2 * a) ^ 2 / (1 - 2 * a) ≤ 16 * a ^ 2 :=
    (div_le_iff₀ (show 0 < 1 - 2 * a by linarith only [ha8])).mpr
      (by nlinarith only [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr ha8)])
  have hHle : 16 * Real.exp 1 * (Real.log (Fintype.card X : ℝ)) ^ 2 + 32 ≤
      (16 * Real.exp 1 + 32) * (1 + Real.log (Fintype.card X : ℝ)) ^ 2 := by
    nlinarith only [hl, Real.exp_nonneg 1, sq_nonneg (Real.log (Fintype.card X : ℝ)),
      mul_nonneg (Real.exp_nonneg 1) hl]
  have hrem : 3 * (2 * a) ^ 2 / (1 - 2 * a) *
      (16 * Real.exp 1 * (Real.log (Fintype.card X : ℝ)) ^ 2 + 32) ≤
      (256 * Real.exp 1 + 512) * a ^ 2 *
        (1 + Real.log (Fintype.card X : ℝ)) ^ 2 := calc
    _ ≤ 16 * a ^ 2 *
        (16 * Real.exp 1 * (Real.log (Fintype.card X : ℝ)) ^ 2 + 32) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ 16 * a ^ 2 *
        ((16 * Real.exp 1 + 32) * (1 + Real.log (Fintype.card X : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hHle (by positivity)
    _ = _ := by ring
  exact ⟨hZ, (Real.log_le_iff_le_exp hZ).2
    (hZeq.trans_le (hu.trans (Real.exp_le_exp.mpr (by
      simpa only [hS, neg_mul, add_comm] using add_le_add_left hrem
        (-(2 * a) * ConditionalMovement.ConditionalCollision.conditionalEntropy W r)))))⟩

end Entropy
