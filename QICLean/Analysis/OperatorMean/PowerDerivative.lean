/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.MatrixPowers
import QICLean.Analysis.NeumannInverse
import QICLean.Analysis.ResolventFunctionalCalculus
import QICLean.Channel.NPositiveIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Fréchet derivative of a real power of a positive definite matrix

For `0 < p < 1` the real power of a positive semidefinite matrix has the Löwner
integral representation
\[
  X^p = \kappa_p \int_0^\infty \bigl(t^{p-1} - t^p (t + X)^{-1}\bigr)\,dt ,
\]
with a positive constant `κ_p`. Differentiating under the integral sign gives the
Fréchet derivative at a positive definite matrix `C`,
\[
  D(C^p)[H] = \kappa_p \int_0^\infty t^p (t + C)^{-1} H (t + C)^{-1}\,dt ,
\]
an integral of sandwich maps. The derivative is taken along Hermitian matrices,
where the real power is defined; off the Hermitian matrices the functional
calculus has no meaning, so the statement is a derivative within the set of
Hermitian matrices.

The integral normalization `κ_p` is Mathlib's: it is the reciprocal of
`∫_0^∞ t^p (t⁻¹ - (t + 1)⁻¹) dt`; its value `sin(π p) / π` is not needed.

## Main definitions

* `Matrix.rpowConst p` — the positive normalizing constant `κ_p`.
* `Matrix.rpowIntegrand p X t` — the resolvent integrand `t ^ (p - 1) - t ^ p (t + X)⁻¹`.
* `Matrix.rpowFDeriv p C` — the derivative map `H ↦ κ_p ∫ t ^ p R_t H R_t` with
  `R_t = (t + C)⁻¹`.

## Main results

* `Matrix.rpow_eq_integral` — the Löwner integral representation.
* `Matrix.hasFDerivWithinAt_rpow` — `X ↦ X ^ p` has derivative `rpowFDeriv p C` at a
  positive definite `C`, within the Hermitian matrices.
* `Matrix.rpowFDeriv_apply` — the derivative as an integral of sandwiches.

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, displays `transport:power-integral`
  (lines 77--82) and `transport:power-derivative` (lines 158--164), in the proof
  of Lemma 7.2 (`transport:cp`). The proofs are written independently from the
  paper.
* E. A. Carlen, *Trace inequalities and quantum entropies: an introductory
  course*, Lemma 2.8.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Set Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive normalizing constant of the Löwner integral representation of
`x ↦ x ^ p`, `0 < p < 1`. -/
noncomputable def rpowConst (p : ℝ) : ℝ := (∫ t in Ioi 0, Real.rpowIntegrand₀₁ p t 1)⁻¹

theorem rpowConst_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < rpowConst p :=
  inv_pos.mpr (Real.integral_rpowIntegrand₀₁_one_pos hp)

/-- The resolvent integrand `t ^ (p - 1) - t ^ p (t + X)⁻¹` of the Löwner
representation. -/
noncomputable def rpowIntegrand (p : ℝ) (X : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  t ^ (p - 1) • (1 : Matrix n n ℂ) - t ^ p • Ring.inverse (t • (1 : Matrix n n ℂ) + X)

/-- The integrability data for the functional calculus of the scalar Löwner integrand
on the spectrum of a positive semidefinite matrix. -/
private theorem rpowIntegrand₀₁_cfc_data {X : Matrix n n ℂ} (hX : X.PosSemidef) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (Function.uncurry (Real.rpowIntegrand₀₁ p)) (Ioi (0 : ℝ) ×ˢ spectrum ℝ X) ∧
      (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ z ∈ spectrum ℝ X,
        ‖Real.rpowIntegrand₀₁ p t z‖ ≤
          ‖Real.rpowIntegrand₀₁ p t (max (sSup (spectrum ℝ X)) 0)‖) ∧
      HasFiniteIntegral (fun t ↦ ‖Real.rpowIntegrand₀₁ p t (max (sSup (spectrum ℝ X)) 0)‖)
        (volume.restrict (Ioi (0 : ℝ))) := by
  have hspec : spectrum ℝ X ⊆ Ici 0 := fun z hz ↦ spectrum_nonneg_of_nonneg hX.nonneg hz
  refine ⟨Real.continuousOn_rpowIntegrand₀₁_uncurry hp _ hspec, ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    have hz0 : 0 ≤ z := hspec hz
    rw [Real.norm_of_nonneg (Real.rpowIntegrand₀₁_nonneg hp.1 ht.le hz0),
      Real.norm_of_nonneg (Real.rpowIntegrand₀₁_nonneg hp.1 ht.le (le_max_right _ _))]
    exact Real.rpowIntegrand₀₁_monotoneOn hp ht.le hz0
      (Set.mem_Ici.mpr (le_max_right _ 0))
      ((le_csSup X.finite_real_spectrum.bddAbove hz).trans (le_max_left _ _))
  · rw [hasFiniteIntegral_norm_iff]
    exact (Real.integrableOn_rpowIntegrand₀₁_Ioi hp (le_max_right _ _)).2

/-- The functional calculus of the scalar Löwner integrand is the resolvent integrand. -/
private theorem cfc_rpowIntegrand₀₁_eq_rpowIntegrand {X : Matrix n n ℂ} (hX : X.PosSemidef)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ioi (0 : ℝ)) :
    cfc (Real.rpowIntegrand₀₁ p t) X = rpowIntegrand p X t := by
  rw [cfc_rpowIntegrand₀₁_eq_resolvent hX hp ht, rpowIntegrand, nonsing_inv_eq_ringInverse]

/-- The resolvent integrand of a positive semidefinite matrix is integrable on `t > 0`. -/
theorem integrableOn_rpowIntegrand {X : Matrix n n ℂ} (hX : X.PosSemidef) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) : IntegrableOn (rpowIntegrand p X) (Ioi 0) := by
  obtain ⟨hcont, hbound, hfin⟩ := rpowIntegrand₀₁_cfc_data hX hp
  exact (integrableOn_cfc measurableSet_Ioi _ _ X hcont hbound hfin hX.isHermitian).congr_fun
    (fun t ht ↦ cfc_rpowIntegrand₀₁_eq_rpowIntegrand hX hp ht) measurableSet_Ioi

/-- **The Löwner integral representation** of a real power `0 < p < 1` of a positive
semidefinite matrix.

Area-law paper, display `transport:power-integral`, `06-transport.tex`
lines 77--82, in resolvent form. -/
theorem rpow_eq_integral {X : Matrix n n ℂ} (hX : X.PosSemidef) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    X ^ p = rpowConst p • ∫ t in Ioi 0, rpowIntegrand p X t := by
  have hspec : spectrum ℝ X ⊆ Ici 0 := fun z hz ↦ spectrum_nonneg_of_nonneg hX.nonneg hz
  obtain ⟨hcont, hbound, hfin⟩ := rpowIntegrand₀₁_cfc_data hX hp
  calc X ^ p
      = cfc (fun x : ℝ ↦ rpowConst p * ∫ t in Ioi 0, Real.rpowIntegrand₀₁ p t x) X := by
        rw [CFC.rpow_eq_cfc_real hX.nonneg]
        exact cfc_congr fun x hx ↦ Real.rpow_eq_const_mul_integral hp (hspec hx)
    _ = rpowConst p • cfc (fun x : ℝ ↦ ∫ t in Ioi 0, Real.rpowIntegrand₀₁ p t x) X :=
        cfc_const_mul _ _ _ (X.finite_real_spectrum.continuousOn _)
    _ = rpowConst p • ∫ t in Ioi 0, cfc (Real.rpowIntegrand₀₁ p t) X := by
        exact congrArg _ (cfc_setIntegral measurableSet_Ioi _ _ X hcont hbound hfin
          hX.isHermitian)
    _ = rpowConst p • ∫ t in Ioi 0, rpowIntegrand p X t := by
        congr 1
        exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦
          cfc_rpowIntegrand₀₁_eq_rpowIntegrand hX hp ht

set_option linter.unusedFintypeInType false in
/-- A positive definite matrix dominates a positive multiple of the identity. -/
theorem PosDef.exists_pos_smul_one_le {C : Matrix n n ℂ} (hC : C.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : Matrix n n ℂ) ≤ C := by
  cases isEmpty_or_nonempty n with
  | inl _ => exact ⟨1, one_pos, le_of_eq (Subsingleton.elim _ _)⟩
  | inr _ =>
    obtain ⟨c, hc, hcC⟩ := (CFC.exists_pos_algebraMap_le_iff C
      hC.isHermitian.isSelfAdjoint).mpr fun x hx ↦ hC.isStrictlyPositive.spectrum_pos hx
    exact ⟨c, hc, by rwa [Algebra.algebraMap_eq_smul_one] at hcC⟩

/-- A lower bound `c • 1 ≤ C` with `c > 0` bounds the shifted inverse:
`‖(t + C)⁻¹‖ ≤ (t + c)⁻¹` for `t ≥ 0`. -/
theorem norm_ringInverse_smul_one_add_le {C : Matrix n n ℂ} {c t : ℝ} (hc : 0 < c)
    (ht : 0 ≤ t) (hcC : c • (1 : Matrix n n ℂ) ≤ C) :
    ‖Ring.inverse (t • (1 : Matrix n n ℂ) + C)‖ ≤ (t + c)⁻¹ := by
  have htc : 0 < t + c := by linarith
  have hlow : (t + c) • (1 : Matrix n n ℂ) ≤ t • 1 + C := by
    rw [add_smul]; exact add_le_add_right hcC _
  have hsp : IsStrictlyPositive ((t + c) • (1 : Matrix n n ℂ)) := by
    rw [Matrix.isStrictlyPositive_iff_posDef]; exact PosDef.one.smul htc
  have hsp' : IsStrictlyPositive (t • (1 : Matrix n n ℂ) + C) := by
    rw [Matrix.isStrictlyPositive_iff_posDef]
    have hd : (t • (1 : Matrix n n ℂ) + C - (t + c) • 1).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hlow)
    simpa using (PosDef.one.smul htc).add_posSemidef hd
  have hle := CStarAlgebra.ringInverse_le_ringInverse hlow hsp
  have hinv : Ring.inverse ((t + c) • (1 : Matrix n n ℂ)) =
      algebraMap ℝ (Matrix n n ℂ) (t + c)⁻¹ := by
    rw [Algebra.algebraMap_eq_smul_one, ← mul_one (Ring.inverse _),
      Ring.inverse_mul_eq_iff_eq_mul _ _ _ hsp.isUnit, smul_mul_smul_comm, one_mul,
      mul_inv_cancel₀ htc.ne', one_smul]
  rw [hinv] at hle
  exact (CStarAlgebra.norm_le_iff_le_algebraMap _ (inv_nonneg.mpr htc.le)
    hsp'.ringInverse.nonneg).mpr hle

/-- A shifted positive definite matrix `t + C`, `t ≥ 0`, is strictly positive. -/
theorem isStrictlyPositive_smul_one_add {C : Matrix n n ℂ} (hC : C.PosDef) {t : ℝ}
    (ht : 0 ≤ t) : IsStrictlyPositive (t • (1 : Matrix n n ℂ) + C) := by
  rw [Matrix.isStrictlyPositive_iff_posDef]
  rcases ht.lt_or_eq with ht | rfl
  · exact (PosDef.one.smul ht).add_posSemidef hC.posSemidef
  · simpa using hC

/-- **Uniform bound for shifted inverses near a positive definite matrix.** If
`c • 1 ≤ C` with `c > 0` and `‖X - C‖ ≤ c / 2`, then for every `t ≥ 0` the matrix
`t + X` is invertible and `‖(t + X)⁻¹‖ ≤ 2 (t + c)⁻¹`. -/
theorem isUnit_and_norm_ringInverse_le {C X : Matrix n n ℂ} {c t : ℝ} (hc : 0 < c)
    (ht : 0 ≤ t) (hcC : c • (1 : Matrix n n ℂ) ≤ C) (hX : ‖X - C‖ ≤ c / 2) :
    IsUnit (t • (1 : Matrix n n ℂ) + X) ∧
      ‖Ring.inverse (t • (1 : Matrix n n ℂ) + X)‖ ≤ 2 * (t + c)⁻¹ := by
  have htc : 0 < t + c := by linarith
  cases isEmpty_or_nonempty n with
  | inl _ =>
    exact ⟨isUnit_of_subsingleton _, by
      rw [Subsingleton.elim (Ring.inverse _) 0, norm_zero]; positivity⟩
  | inr _ =>
  have hC : C.PosDef := by
    have hd : (C - c • (1 : Matrix n n ℂ)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hcC)
    simpa using (PosDef.one.smul hc).add_posSemidef hd
  have hK₀ := (isStrictlyPositive_smul_one_add hC ht).isUnit
  have hnorm := norm_ringInverse_smul_one_add_le hc ht hcC
  have hsmall : ‖Ring.inverse (t • (1 : Matrix n n ℂ) + C)‖ *
      ‖(t • (1 : Matrix n n ℂ) + X) - (t • 1 + C)‖ ≤ 1 / 2 := by
    rw [add_sub_add_left_eq_sub]
    calc ‖Ring.inverse (t • (1 : Matrix n n ℂ) + C)‖ * ‖X - C‖ ≤ (t + c)⁻¹ * (c / 2) := by
          gcongr
      _ ≤ 1 / 2 := by
          rw [inv_mul_le_iff₀ htc]; linarith
  obtain ⟨hu, hb⟩ := NormedRing.isUnit_and_norm_inverse_le_of_norm_mul_norm_sub_le _ _ hK₀
    hsmall (by norm_num)
  refine ⟨hu, hb.trans ?_⟩
  norm_num
  exact hnorm

/-- The scalar domination of the derivative integrand:
`t ^ p (2 (t + c)⁻¹) ^ 2 ≤ (4 / c) t ^ p (t⁻¹ - (t + c)⁻¹)` for `t, c > 0`. -/
private theorem rpow_mul_sq_le_rpowIntegrand {p c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    t ^ p * (2 * (t + c)⁻¹) ^ 2 ≤ 4 / c * Real.rpowIntegrand₀₁ p t c := by
  have htp : 0 ≤ t ^ p := Real.rpow_nonneg ht.le p
  have key : ((t + c)⁻¹) ^ 2 ≤ 1 / c * (t⁻¹ - (t + c)⁻¹) := by
    have h1 : 1 / c * (t⁻¹ - (t + c)⁻¹) = 1 / (t * (t + c)) := by
      field_simp; ring
    rw [h1, inv_pow, ← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  rw [Real.rpowIntegrand₀₁]
  calc t ^ p * (2 * (t + c)⁻¹) ^ 2 = 4 * (t ^ p * ((t + c)⁻¹) ^ 2) := by ring
    _ ≤ 4 * (t ^ p * (1 / c * (t⁻¹ - (t + c)⁻¹))) := by gcongr
    _ = 4 / c * (t ^ p * (t⁻¹ - (t + c)⁻¹)) := by ring

/-- The integrand `H ↦ t ^ p (t + X)⁻¹ H (t + X)⁻¹` of the derivative of `X ↦ X ^ p`. -/
noncomputable def rpowFDerivIntegrand (p : ℝ) (X : Matrix n n ℂ) (t : ℝ) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  t ^ p • ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)
    (Ring.inverse (t • (1 : Matrix n n ℂ) + X)) (Ring.inverse (t • (1 : Matrix n n ℂ) + X))

theorem rpowFDerivIntegrand_apply (p : ℝ) (X : Matrix n n ℂ) (t : ℝ) (H : Matrix n n ℂ) :
    rpowFDerivIntegrand p X t H = t ^ p •
      (Ring.inverse (t • (1 : Matrix n n ℂ) + X) * H *
        Ring.inverse (t • (1 : Matrix n n ℂ) + X)) := rfl

/-- The Fréchet derivative of `X ↦ X ^ p` at `C`, as the integral of the sandwich maps
`H ↦ t ^ p (t + C)⁻¹ H (t + C)⁻¹`.

Area-law paper, display `transport:power-derivative`, `06-transport.tex`
lines 158--164. -/
noncomputable def rpowFDeriv (p : ℝ) (C : Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  rpowConst p • ∫ t in Ioi (0 : ℝ), rpowFDerivIntegrand p C t

/-- Continuity in `t` of the shifted inverse `(t + X)⁻¹` on `t > 0`, when every shift is
invertible. -/
private theorem continuousOn_ringInverse_smul_one_add {X : Matrix n n ℂ}
    (hX : ∀ t : ℝ, 0 < t → IsUnit (t • (1 : Matrix n n ℂ) + X)) :
    ContinuousOn (fun t : ℝ ↦ Ring.inverse (t • (1 : Matrix n n ℂ) + X)) (Ioi 0) := by
  intro t ht
  have hu := hX t ht
  refine ContinuousAt.continuousWithinAt ?_
  have hinv := NormedRing.inverse_continuousAt hu.unit
  rw [hu.unit_spec] at hinv
  exact ContinuousAt.comp (g := Ring.inverse) hinv
    (Continuous.continuousAt (by fun_prop : Continuous fun s : ℝ ↦ s • (1 : Matrix n n ℂ) + X))

private theorem continuousOn_rpowIntegrand {p : ℝ} {X : Matrix n n ℂ}
    (hX : ∀ t : ℝ, 0 < t → IsUnit (t • (1 : Matrix n n ℂ) + X)) :
    ContinuousOn (rpowIntegrand p X) (Ioi 0) := by
  have hr : ∀ q : ℝ, ContinuousOn (fun t : ℝ ↦ t ^ q) (Ioi 0) := fun q ↦
    ContinuousOn.rpow_const continuousOn_id fun t ht ↦ Or.inl (ne_of_gt ht)
  exact ((hr (p - 1)).smul continuousOn_const).sub
    ((hr p).smul (continuousOn_ringInverse_smul_one_add hX))

private theorem continuousOn_rpowFDerivIntegrand {p : ℝ} {X : Matrix n n ℂ}
    (hX : ∀ t : ℝ, 0 < t → IsUnit (t • (1 : Matrix n n ℂ) + X)) :
    ContinuousOn (rpowFDerivIntegrand p X) (Ioi 0) := by
  have hr : ContinuousOn (fun t : ℝ ↦ t ^ p) (Ioi 0) :=
    ContinuousOn.rpow_const continuousOn_id fun t ht ↦ Or.inl (ne_of_gt ht)
  have hR := continuousOn_ringInverse_smul_one_add hX
  have h2 : Continuous (fun q : Matrix n n ℂ × Matrix n n ℂ ↦
      ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) q.1 q.2) :=
    (ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)).continuous₂
  have h3 : ContinuousOn (fun t : ℝ ↦ ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)
      (Ring.inverse (t • (1 : Matrix n n ℂ) + X))
      (Ring.inverse (t • (1 : Matrix n n ℂ) + X))) (Ioi 0) :=
    h2.comp_continuousOn (f := fun t : ℝ ↦ (Ring.inverse (t • (1 : Matrix n n ℂ) + X),
      Ring.inverse (t • (1 : Matrix n n ℂ) + X))) (hR.prodMk hR)
  unfold rpowFDerivIntegrand
  exact ContinuousOn.smul (f := fun t : ℝ ↦ t ^ p) hr h3

/-- The derivative of the resolvent integrand in `X`. -/
private theorem hasFDerivAt_rpowIntegrand {p t : ℝ} {X : Matrix n n ℂ}
    (hu : IsUnit (t • (1 : Matrix n n ℂ) + X)) :
    HasFDerivAt (fun Y ↦ rpowIntegrand p Y t) (rpowFDerivIntegrand p X t) X := by
  have h1 := hasFDerivAt_ringInverse (𝕜 := ℂ) hu.unit
  rw [hu.unit_spec] at h1
  have h2 := ((h1.comp X ((hasFDerivAt_id X).const_add (t • (1 : Matrix n n ℂ)))).const_smul
    (t ^ p)).const_sub (t ^ (p - 1) • (1 : Matrix n n ℂ))
  refine h2.congr_fderiv ?_
  ext H : 1
  rw [← Ring.inverse_unit, hu.unit_spec]
  simp [rpowFDerivIntegrand]

/-- The norm bound for the derivative integrand near a positive definite matrix. -/
private theorem norm_rpowFDerivIntegrand_le {C X : Matrix n n ℂ} {c p t : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hcC : c • (1 : Matrix n n ℂ) ≤ C) (hX : ‖X - C‖ ≤ c / 2) :
    ‖rpowFDerivIntegrand p X t‖ ≤ 4 / c * Real.rpowIntegrand₀₁ p t c := by
  have hb := (isUnit_and_norm_ringInverse_le hc ht.le hcC hX).2
  calc ‖rpowFDerivIntegrand p X t‖
      ≤ ‖t ^ p‖ * (‖Ring.inverse (t • (1 : Matrix n n ℂ) + X)‖ *
          ‖Ring.inverse (t • (1 : Matrix n n ℂ) + X)‖) := by
        unfold rpowFDerivIntegrand
        refine (norm_smul_le (t ^ p) (ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ)
          (Ring.inverse (t • (1 : Matrix n n ℂ) + X))
          (Ring.inverse (t • (1 : Matrix n n ℂ) + X)))).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le _ _ _ _
    _ ≤ t ^ p * (2 * (t + c)⁻¹) ^ 2 := by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le p), sq]
        have htp : 0 ≤ t ^ p := Real.rpow_nonneg ht.le p
        have htc : 0 ≤ 2 * (t + c)⁻¹ := by positivity
        gcongr
    _ ≤ 4 / c * Real.rpowIntegrand₀₁ p t c := rpow_mul_sq_le_rpowIntegrand hc ht

/-- The derivative integrand at a positive definite matrix is integrable on `t > 0`. -/
theorem integrableOn_rpowFDerivIntegrand {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) : IntegrableOn (rpowFDerivIntegrand p C) (Ioi 0) := by
  obtain ⟨c, hc, hcC⟩ := hC.exists_pos_smul_one_le
  have hCC : ‖C - C‖ ≤ c / 2 := by rw [sub_self, norm_zero]; positivity
  have hmeas : AEStronglyMeasurable (rpowFDerivIntegrand p C) (volume.restrict (Ioi 0)) :=
    (continuousOn_rpowFDerivIntegrand (p := p) (X := C) fun t ht ↦
      (isUnit_and_norm_ringInverse_le hc ht.le hcC hCC).1).aestronglyMeasurable
      measurableSet_Ioi
  refine Integrable.mono' (f := rpowFDerivIntegrand p C)
    ((Real.integrableOn_rpowIntegrand₀₁_Ioi hp hc.le).const_mul (4 / c)) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact norm_rpowFDerivIntegrand_le hc ht hcC hCC

/-- **Differentiation of the Löwner integral.** At a positive definite `C`, the
resolvent integral `X ↦ κ_p ∫ (t ^ (p - 1) - t ^ p (t + X)⁻¹) dt`, defined on a
neighbourhood of `C`, has Fréchet derivative `rpowFDeriv p C`.

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex`
lines 158--164: the integrand of the derivative is `O(t ^ p)` at zero and
`O(t ^ (p - 2))` at infinity. -/
theorem hasFDerivAt_integral_rpowIntegrand {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasFDerivAt (fun X ↦ rpowConst p • ∫ t in Ioi 0, rpowIntegrand p X t)
      (rpowFDeriv p C) C := by
  obtain ⟨c, hc, hcC⟩ := hC.exists_pos_smul_one_le
  have hball : ∀ X ∈ Metric.ball C (c / 2), ∀ t : ℝ, 0 ≤ t →
      IsUnit (t • (1 : Matrix n n ℂ) + X) ∧
        ‖Ring.inverse (t • (1 : Matrix n n ℂ) + X)‖ ≤ 2 * (t + c)⁻¹ := by
    intro X hX t ht
    exact isUnit_and_norm_ringInverse_le hc ht hcC (by
      rw [Metric.mem_ball, dist_eq_norm] at hX; exact hX.le)
  have hunit : ∀ X ∈ Metric.ball C (c / 2), ∀ t : ℝ, 0 < t →
      IsUnit (t • (1 : Matrix n n ℂ) + X) := fun X hX t ht ↦ (hball X hX t ht.le).1
  have hCmem : C ∈ Metric.ball C (c / 2) := Metric.mem_ball_self (by positivity)
  have hCint : IntegrableOn (rpowIntegrand p C) (Ioi 0) :=
    integrableOn_rpowIntegrand hC.posSemidef hp
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun X t ↦ rpowIntegrand p X t)
    (F' := rpowFDerivIntegrand p)
    (x₀ := C) (bound := fun t ↦ 4 / c * Real.rpowIntegrand₀₁ p t c)
    (Metric.ball_mem_nhds C (by positivity : 0 < c / 2))
    (eventually_of_mem (Metric.ball_mem_nhds C (by positivity : 0 < c / 2)) fun X hX ↦
      (continuousOn_rpowIntegrand (hunit X hX)).aestronglyMeasurable measurableSet_Ioi)
    hCint ((continuousOn_rpowFDerivIntegrand (hunit C hCmem)).aestronglyMeasurable
      measurableSet_Ioi)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht X hX
      rw [Metric.mem_ball, dist_eq_norm] at hX
      exact norm_rpowFDerivIntegrand_le hc ht hcC hX.le)
    ((Real.integrableOn_rpowIntegrand₀₁_Ioi hp hc.le).const_mul _)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht X hX
      exact hasFDerivAt_rpowIntegrand (hunit X hX t ht))
  exact hderiv.const_smul (rpowConst p)

/-- A Hermitian matrix within distance `c` of a matrix dominating `c • 1` is positive
semidefinite. -/
theorem posSemidef_of_norm_sub_lt {C X : Matrix n n ℂ} {c : ℝ}
    (hcC : c • (1 : Matrix n n ℂ) ≤ C) (hCh : C.IsHermitian) (hXh : X.IsHermitian)
    (hXC : ‖X - C‖ ≤ c) : X.PosSemidef := by
  have h1 := IsSelfAdjoint.neg_algebraMap_norm_le_self (X - C) (hXh.sub hCh).isSelfAdjoint
  rw [Algebra.algebraMap_eq_smul_one] at h1
  have h2 : (c - ‖X - C‖) • (1 : Matrix n n ℂ) ≤ X := by
    calc (c - ‖X - C‖) • (1 : Matrix n n ℂ) = c • 1 + -(‖X - C‖ • 1) := by
          rw [sub_smul, sub_eq_add_neg]
      _ ≤ C + (X - C) := add_le_add hcC h1
      _ = X := by abel
  have h0 : (0 : Matrix n n ℂ) ≤ (c - ‖X - C‖) • 1 :=
    smul_nonneg (sub_nonneg.mpr hXC) zero_le_one
  exact Matrix.nonneg_iff_posSemidef.mp (h0.trans h2)

/-- **The Fréchet derivative of a real power.** For `0 < p < 1` and a positive definite
`C`, the map `X ↦ X ^ p` has derivative `rpowFDeriv p C` at `C` within the Hermitian
matrices.

Area-law paper, display `transport:power-derivative`, `06-transport.tex`
lines 158--164. -/
theorem hasFDerivWithinAt_rpow {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasFDerivWithinAt (fun X : Matrix n n ℂ ↦ X ^ p) (rpowFDeriv p C)
      {X | X.IsHermitian} C := by
  obtain ⟨c, hc, hcC⟩ := hC.exists_pos_smul_one_le
  refine (hasFDerivAt_integral_rpowIntegrand hC hp).hasFDerivWithinAt.congr_of_eventuallyEq
    ?_ (rpow_eq_integral hC.posSemidef hp)
  filter_upwards [inter_mem_nhdsWithin {X : Matrix n n ℂ | X.IsHermitian}
    (Metric.ball_mem_nhds C hc)] with X hX
  obtain ⟨hXh, hXb⟩ := hX
  rw [Metric.mem_ball, dist_eq_norm] at hXb
  exact rpow_eq_integral (posSemidef_of_norm_sub_lt hcC hC.isHermitian hXh hXb.le) hp

/-- The derivative of a real power as an integral of sandwiches:
`D(C ^ p)[H] = κ_p ∫ t ^ p (t + C)⁻¹ H (t + C)⁻¹ dt`.

Area-law paper, display `transport:power-derivative`, `06-transport.tex`
lines 158--164. -/
theorem rpowFDeriv_apply {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (H : Matrix n n ℂ) :
    rpowFDeriv p C H = rpowConst p • ∫ t in Ioi (0 : ℝ), t ^ p •
      (Ring.inverse (t • (1 : Matrix n n ℂ) + C) * H *
        Ring.inverse (t • (1 : Matrix n n ℂ) + C)) := by
  rw [rpowFDeriv, _root_.smul_apply,
    ContinuousLinearMap.integral_apply (integrableOn_rpowFDerivIntegrand hC hp)]
  rfl

/-- **Complete positivity of the derivative of a real power.** For `0 < p < 1` and a
positive definite `C`, the derivative `rpowFDeriv p C` is `k`-positive for every `k`:
it is an integral of the sandwich maps `H ↦ t ^ p (t + C)⁻¹ H (t + C)⁻¹`.

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex`
lines 164--166. -/
theorem isNPositiveMap_rpowFDeriv {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (k : ℕ) : IsNPositiveMap k (rpowFDeriv p C).toLinearMap := by
  have hint := IsNPositiveMap.integral (integrableOn_rpowFDerivIntegrand hC hp) (k := k) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hR : (Ring.inverse (t • (1 : Matrix n n ℂ) + C))ᴴ =
        Ring.inverse (t • (1 : Matrix n n ℂ) + C) := by
      have := (isStrictlyPositive_smul_one_add hC (le_of_lt ht)).ringInverse
      exact (Matrix.isStrictlyPositive_iff_posDef.mp this).isHermitian.eq
    have heq : (rpowFDerivIntegrand p C t).toLinearMap =
        ((t ^ p : ℝ) : ℂ) • singleKrausMap (Ring.inverse (t • (1 : Matrix n n ℂ) + C)) := by
      ext1 H
      simp [rpowFDerivIntegrand, singleKrausMap, hR]
    rw [heq]
    exact (isNPositiveMap_singleKrausMap _ k).smul_nonneg (Real.rpow_nonneg (le_of_lt ht) p))
  have heq : (rpowFDeriv p C).toLinearMap =
      ((rpowConst p : ℝ) : ℂ) • (∫ t in Ioi (0 : ℝ), rpowFDerivIntegrand p C t).toLinearMap := by
    ext1 H
    simp [rpowFDeriv]
  rw [heq]
  exact hint.smul_nonneg (rpowConst_pos hp).le

/-- **Euler identity for the derivative of a real power**: `D(C ^ p)[C] = p C ^ p`, the
derivative of the homogeneity `(s C) ^ p = s ^ p C ^ p` at `s = 1`. -/
theorem rpowFDeriv_self {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    rpowFDeriv p C C = p • C ^ p := by
  have hcurve : HasDerivAt (fun s : ℝ ↦ s • C) C 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const C
  have h1 : HasDerivWithinAt (fun s : ℝ ↦ (s • C) ^ p) (rpowFDeriv p C C) Set.univ 1 := by
    have := ((hasFDerivWithinAt_rpow hC hp).restrictScalars ℝ).comp_hasDerivWithinAt_of_eq
      (x := (1 : ℝ))
      (hcurve.hasDerivWithinAt (s := Set.univ))
      (fun s _ ↦ show s • C ∈ {X : Matrix n n ℂ | X.IsHermitian} by
        rw [Set.mem_ofPred_eq, IsHermitian, conjTranspose_smul, hC.isHermitian.eq, star_trivial])
      (one_smul ℝ C).symm
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun s : ℝ ↦ s ^ p • C ^ p) (p • C ^ p) 1 := by
    simpa using (Real.hasDerivAt_rpow_const (x := 1) (p := p) (Or.inl one_ne_zero)).smul_const
      (C ^ p)
  have heq : (fun s : ℝ ↦ (s • C) ^ p) =ᶠ[𝓝 1] fun s ↦ s ^ p • C ^ p := by
    filter_upwards [lt_mem_nhds one_pos] with s hs
    exact hC.smul_rpow hs p
  exact (h1.hasDerivAt Filter.univ_mem).unique (h2.congr_of_eventuallyEq heq)

end Matrix
