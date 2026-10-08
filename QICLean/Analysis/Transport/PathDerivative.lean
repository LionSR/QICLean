/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Defs

/-!
# Derivatives of weighted geometric means along paths

Helpers for the exact derivative of the area-law paper, Proposition 7.4
(`06-transport.tex` lines 438--468):

* `C ^ q = exp (q log C)` and its derivative in the exponent;
* uniqueness of derivatives within the Hermitian matrices;
* joint differentiability of `(A, B) ↦ A #_r B` within the Hermitian matrices, with the
  partial derivatives `geomMeanDerivLeft` and `geomMeanDerivRight`;
* the derivative of `q ↦ A #_q B` and its identification with the old-child derivative
  applied to `A^{1/2} log C A^{1/2}` (lines 448--458).

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Set Filter Topology NormedSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `C ^ q = exp (q log C)` for a positive definite `C`. -/
theorem PosDef.rpow_eq_exp_smul_log {C : Matrix n n ℂ} (hC : C.PosDef) (q : ℝ) :
    C ^ q = exp (q • CFC.log C) := by
  have hsa : IsSelfAdjoint (CFC.log C) := IsSelfAdjoint.log
  rw [CFC.rpow_eq_cfc_real hC.posSemidef.nonneg, ← CFC.real_exp_eq_normedSpace_exp ((IsSelfAdjoint.all q).smul hsa),
    CFC.log, ← cfc_const_mul q Real.log C (C.finite_real_spectrum.continuousOn _),
    ← cfc_comp' Real.exp (fun x => q * Real.log x) C Real.continuous_exp.continuousOn
      (C.finite_real_spectrum.continuousOn _)]
  refine cfc_congr fun x hx => ?_
  have hx0 : 0 < x := hC.isStrictlyPositive.spectrum_pos hx
  rw [Real.rpow_def_of_pos hx0, mul_comm]

/-- The derivative of `q ↦ C ^ q` is `C ^ p log C`. -/
theorem PosDef.hasDerivAt_rpow_exponent {C : Matrix n n ℂ} (hC : C.PosDef) (p : ℝ) :
    HasDerivAt (fun q : ℝ => C ^ q) (C ^ p * CFC.log C) p := by
  simp_rw [hC.rpow_eq_exp_smul_log]
  exact hasDerivAt_exp_smul_const (𝕂 := ℝ) (CFC.log C) p

omit [DecidableEq n] in
/-- Derivatives within the Hermitian matrices are unique: every matrix is `H₁ + i H₂` with
`H₁, H₂` Hermitian. -/
theorem uniqueDiffWithinAt_hermitianSet {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    UniqueDiffWithinAt ℂ (hermitianSet n) A := by
  refine ⟨?_, subset_closure hA⟩
  have hT : ∀ H : Matrix n n ℂ, H.IsHermitian → H ∈ tangentConeAt ℂ (hermitianSet n) A := by
    intro H hH
    have hseg : segment ℝ A (A + H) ⊆ hermitianSet n := by
      rintro X ⟨a, b, -, -, -, rfl⟩
      change (a • A + b • (A + H)).IsHermitian
      simp [IsHermitian, conjTranspose_add, conjTranspose_smul, hA.eq, hH.eq]
    have := mem_tangentConeAt_of_segment_subset hseg
    rw [add_sub_cancel_left] at this
    exact tangentConeAt_mono_field this
  have hspan : Submodule.span ℂ (tangentConeAt ℂ (hermitianSet n) A) = ⊤ := by
    refine eq_top_iff.mpr fun M _ => ?_
    have h1 : ((1 / 2 : ℂ) • (M + Mᴴ)).IsHermitian := by
      simp [IsHermitian, conjTranspose_smul, add_comm]
    have h2 : ((-Complex.I / 2) • (M - Mᴴ)).IsHermitian := by
      simp only [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    have hM : M = (1 / 2 : ℂ) • (M + Mᴴ) + Complex.I • ((-Complex.I / 2) • (M - Mᴴ)) := by
      rw [smul_smul]
      ext i j
      simp only [add_apply, smul_apply, sub_apply, smul_eq_mul]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [hM]
    exact Submodule.add_mem _ (Submodule.subset_span (hT _ h1))
      (Submodule.smul_mem _ _ (Submodule.subset_span (hT _ h2)))
  rw [hspan]
  simp

/-- `X ↦ X ^ (-1/2)` is differentiable at a positive definite matrix within the Hermitian
matrices. -/
theorem differentiableWithinAt_rpow_neg_half {A : Matrix n n ℂ} (hA : A.PosDef) :
    DifferentiableWithinAt ℂ (fun X : Matrix n n ℂ => X ^ (-(1 / 2) : ℝ)) (hermitianSet n) A := by
  have h1 : DifferentiableWithinAt ℂ (fun X : Matrix n n ℂ => X ^ (1 / 2 : ℝ))
      (hermitianSet n) A :=
    (hasFDerivWithinAt_rpow_Icc hA ⟨by norm_num, by norm_num⟩).differentiableWithinAt
  have h2 : DifferentiableWithinAt ℂ (fun X : Matrix n n ℂ => Ring.inverse (X ^ (1 / 2 : ℝ)))
      (hermitianSet n) A :=
    (differentiableAt_inverse (hA.rpow (1 / 2)).isUnit).comp_differentiableWithinAt A h1
  refine h2.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [eventually_posDef_nhdsWithin hA] with X hX
    rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_eq_left_inv (hX.rpow_neg_mul_rpow _)]
  · rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_eq_left_inv (hA.rpow_neg_mul_rpow _)]

/-- The weighted geometric mean is jointly differentiable within the Hermitian matrices. -/
theorem differentiableWithinAt_geomMean {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    DifferentiableWithinAt ℂ (fun x : Matrix n n ℂ × Matrix n n ℂ => geomMean r x.1 x.2)
      (hermitianSet n ×ˢ hermitianSet n) (A, B) := by
  have hfst : MapsTo (Prod.fst : Matrix n n ℂ × Matrix n n ℂ → _) (hermitianSet n ×ˢ hermitianSet n)
      (hermitianSet n) := fun x hx => hx.1
  have hs : DifferentiableWithinAt ℂ (fun x : Matrix n n ℂ × Matrix n n ℂ => x.1 ^ (1 / 2 : ℝ))
      (hermitianSet n ×ˢ hermitianSet n) (A, B) :=
    ((hasFDerivWithinAt_rpow_Icc hA ⟨by norm_num, by norm_num⟩).differentiableWithinAt).comp
      (A, B) differentiableWithinAt_fst hfst
  have hsi : DifferentiableWithinAt ℂ
      (fun x : Matrix n n ℂ × Matrix n n ℂ => x.1 ^ (-(1 / 2) : ℝ))
      (hermitianSet n ×ˢ hermitianSet n) (A, B) :=
    (differentiableWithinAt_rpow_neg_half hA).comp (A, B) differentiableWithinAt_fst hfst
  have hmid : DifferentiableWithinAt ℂ
      (fun x : Matrix n n ℂ × Matrix n n ℂ => x.1 ^ (-(1 / 2) : ℝ) * x.2 * x.1 ^ (-(1 / 2) : ℝ))
      (hermitianSet n ×ˢ hermitianSet n) (A, B) :=
    (hsi.mul differentiableWithinAt_snd).mul hsi
  have hmaps : MapsTo
      (fun x : Matrix n n ℂ × Matrix n n ℂ => x.1 ^ (-(1 / 2) : ℝ) * x.2 * x.1 ^ (-(1 / 2) : ℝ))
      (hermitianSet n ×ˢ hermitianSet n) (hermitianSet n) := fun x hx => by
    have h1 := isHermitian_rpow x.1 (-(1 / 2))
    change (x.1 ^ (-(1 / 2) : ℝ) * x.2 * x.1 ^ (-(1 / 2) : ℝ)).IsHermitian
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, h1.eq, hx.2.eq, Matrix.mul_assoc]
  have hpow : DifferentiableWithinAt ℂ
      (fun x : Matrix n n ℂ × Matrix n n ℂ =>
        (x.1 ^ (-(1 / 2) : ℝ) * x.2 * x.1 ^ (-(1 / 2) : ℝ)) ^ r)
      (hermitianSet n ×ˢ hermitianSet n) (A, B) :=
    ((hasFDerivWithinAt_rpow_Icc (hA.whiten hB) hr).differentiableWithinAt).comp (A, B) hmid hmaps
  exact (hs.mul hpow).mul hs

/-- **Joint derivative of the weighted geometric mean** within the Hermitian matrices: the sum
of the two partial derivatives. -/
theorem hasFDerivWithinAt_geomMean_prod {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    HasFDerivWithinAt (fun x : Matrix n n ℂ × Matrix n n ℂ => geomMean r x.1 x.2)
      ((geomMeanDerivLeft r A B).comp (ContinuousLinearMap.fst ℂ _ _) +
        (geomMeanDerivRight r A B).comp (ContinuousLinearMap.snd ℂ _ _))
      (hermitianSet n ×ˢ hermitianSet n) (A, B) := by
  have hF := (differentiableWithinAt_geomMean hA hB hr).hasFDerivWithinAt
  set F' := fderivWithin ℂ (fun x : Matrix n n ℂ × Matrix n n ℂ => geomMean r x.1 x.2)
    (hermitianSet n ×ˢ hermitianSet n) (A, B)
  have hl : HasFDerivWithinAt (fun X => geomMean r X B) (F'.comp (ContinuousLinearMap.inl ℂ _ _))
      (hermitianSet n) A := by
    have hm : MapsTo (fun X : Matrix n n ℂ => (X, B)) (hermitianSet n)
        (hermitianSet n ×ˢ hermitianSet n) := fun X hX => ⟨hX, hB.isHermitian⟩
    have h := hF.comp A ((hasFDerivAt_prodMk_left (𝕜 := ℂ) A B).hasFDerivWithinAt) hm
    exact h
  have hr' : HasFDerivWithinAt (fun Y => geomMean r A Y)
      (F'.comp (ContinuousLinearMap.inr ℂ _ _)) (hermitianSet n) B := by
    have hm : MapsTo (fun Y : Matrix n n ℂ => (A, Y)) (hermitianSet n)
        (hermitianSet n ×ˢ hermitianSet n) := fun Y hY => ⟨hA.isHermitian, hY⟩
    have h := hF.comp B ((hasFDerivAt_prodMk_right (𝕜 := ℂ) A B).hasFDerivWithinAt) hm
    exact h
  have el := (uniqueDiffWithinAt_hermitianSet hA.isHermitian).eq hl
    (hasFDerivWithinAt_geomMean_left hA hB hr)
  have er := (uniqueDiffWithinAt_hermitianSet hB.isHermitian).eq hr'
    (hasFDerivWithinAt_geomMean_right hA hB hr)
  convert hF using 1
  rw [← el, ← er]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply,
    ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- **Chain rule for the mean along a pair of paths.** -/
theorem hasDerivAt_geomMean_of_hasDerivAt {L R : ℝ → Matrix n n ℂ} {L' R' : Matrix n n ℂ}
    {p r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hL : HasDerivAt L L' p) (hR : HasDerivAt R R' p)
    (hLh : ∀ q, (L q).IsHermitian) (hRh : ∀ q, (R q).IsHermitian) (hLp : (L p).PosDef)
    (hRp : (R p).PosDef) :
    HasDerivAt (fun q => geomMean r (L q) (R q))
      (geomMeanDerivLeft r (L p) (R p) L' + geomMeanDerivRight r (L p) (R p) R') p := by
  have hm : MapsTo (fun q => (L q, R q)) univ (hermitianSet n ×ˢ hermitianSet n) :=
    fun q _ => ⟨hLh q, hRh q⟩
  have h := ((hasFDerivWithinAt_geomMean_prod hLp hRp hr).restrictScalars ℝ).comp_hasDerivWithinAt p
    (hL.prodMk hR).hasDerivWithinAt hm
  rw [hasDerivWithinAt_univ] at h
  convert h using 1 <;> simp [Function.comp_def]

/-- The derivative of `q ↦ A #_q B` (`06-transport.tex` lines 442--446):
`∂_q (A #_q B) = A^{1/2} C^q log C A^{1/2}` with `C = A^{-1/2} B A^{-1/2}`. -/
theorem hasDerivAt_geomMean_param {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) (p : ℝ) :
    HasDerivAt (fun q => geomMean q A B)
      (A ^ (1 / 2 : ℝ) * ((A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) ^ p *
        CFC.log (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ))) * A ^ (1 / 2 : ℝ)) p :=
  (((hA.whiten hB).hasDerivAt_rpow_exponent p).const_mul _).mul_const _

/-- `C^δ #_p C = C^{δ (1 - p) + p}`. -/
theorem geomMean_rpow_self {C : Matrix n n ℂ} (hC : C.PosDef) (δ p : ℝ) :
    geomMean p (C ^ δ) C = C ^ (δ * (1 - p) + p) := by
  have hmid : (C ^ δ) ^ (-(1 / 2) : ℝ) * C * (C ^ δ) ^ (-(1 / 2) : ℝ) = C ^ (1 - δ) := by
    rw [hC.rpow_rpow]
    conv_lhs => rw [show C ^ (δ * -(1 / 2) : ℝ) * C = C ^ (δ * -(1 / 2) : ℝ) * C ^ (1 : ℝ) by
      rw [hC.rpow_one]]
    rw [hC.rpow_mul_rpow, hC.rpow_mul_rpow]
    congr 1; ring
  rw [geomMean, hmid, hC.rpow_rpow, hC.rpow_rpow, hC.rpow_mul_rpow, hC.rpow_mul_rpow]
  congr 1; ring

/-- **The old-child derivative in the direction `A^{1/2} log C A^{1/2}`**
(`06-transport.tex` lines 448--458): it is `(1 - p)` times the parameter derivative. -/
theorem geomMeanDerivLeft_sandwich_log {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    geomMeanDerivLeft p A B
        (A ^ (1 / 2 : ℝ) * CFC.log (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) *
          A ^ (1 / 2 : ℝ)) =
      (1 - p) • (A ^ (1 / 2 : ℝ) * ((A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) ^ p *
        CFC.log (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ))) * A ^ (1 / 2 : ℝ)) := by
  set C := A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ) with hCdef
  have hC : C.PosDef := hA.whiten hB
  set S := A ^ (1 / 2 : ℝ)
  have hS : S.PosDef := hA.rpow _
  have hSs : star S = S := hA.star_rpow _
  have hSA : S * 1 * S = A := by rw [Matrix.mul_one]; exact hA.rpow_half_mul_rpow_half
  have hSB : S * C * S = B := by
    have h1 : S * A ^ (-(1 / 2) : ℝ) = 1 := hA.rpow_mul_rpow_neg _
    have h2 : A ^ (-(1 / 2) : ℝ) * S = 1 := hA.rpow_neg_mul_rpow _
    calc S * C * S = (S * A ^ (-(1 / 2) : ℝ)) * B * (A ^ (-(1 / 2) : ℝ) * S) := by
          simp only [hCdef, Matrix.mul_assoc]
      _ = B := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  -- The curve `X(δ) = S C^δ S` through `A`.
  set X : ℝ → Matrix n n ℂ := fun δ => S * C ^ δ * S
  have hX : HasDerivAt X (S * (C ^ (0 : ℝ) * CFC.log C) * S) 0 :=
    ((hC.hasDerivAt_rpow_exponent 0).const_mul _).mul_const _
  have hX0 : X 0 = A := by simp only [X, hC.rpow_zero]; exact hSA
  have hXh : ∀ δ, (X δ).IsHermitian := fun δ => by
    simp only [X, IsHermitian, conjTranspose_mul, (hC.rpow_isHermitian δ).eq]
    rw [show Sᴴ = S from hSs, Matrix.mul_assoc]
  have h1 := hasDerivAt_geomMean_of_hasDerivAt hp hX (hasDerivAt_const (0 : ℝ) B) hXh
    (fun _ => hB.isHermitian) (hX0 ▸ hA) hB
  rw [hX0, map_zero, add_zero, hC.rpow_zero, Matrix.one_mul] at h1
  -- The same curve computed through congruence covariance.
  have hcurve : (fun δ => geomMean p (X δ) B) =
      fun δ => S * C ^ (δ * (1 - p) + p) * S := by
    funext δ
    have := geomMean_star_conj (hC.rpow δ) hC hS.isUnit p
    rw [hSs, hSB, geomMean_rpow_self hC] at this
    exact this
  have he : HasDerivAt (fun δ : ℝ => δ * (1 - p) + p) (1 * (1 - p)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).mul_const _).add_const _
  have h2 : HasDerivAt (fun δ => S * C ^ (δ * (1 - p) + p) * S)
      (S * ((1 - p) • (C ^ p * CFC.log C)) * S) 0 := by
    have hg := hC.hasDerivAt_rpow_exponent ((fun δ : ℝ => δ * (1 - p) + p) 0)
    have := hg.scomp 0 he
    simp only [zero_mul, zero_add, one_mul] at this
    exact (this.const_mul S).mul_const S
  rw [hcurve] at h1
  rw [h1.unique h2, Matrix.mul_smul, Matrix.smul_mul]

end Matrix
