/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Order.Basic

/-!
# Range projectors through a supported Gram inverse

A map `T` between Hilbert spaces with finite-dimensional domain need not be injective: it may
vanish outside a subspace of its domain, so that its Gram operator `T† T` is invertible only on
that subspace. A self-adjoint support operator `Q` with `T Q = T` and a supported inverse `H` with
`T† T H = Q` suffice to recover the orthogonal range projection `T H T†`.

For three maps with a common factorization `T J₁ = C = L J₂`, the product of two range
projections minus the third factors through an exact mixed-Gram residual,
`P_T P_L - P_C = T H_T R H_L L†`. Its norm is at most `‖T‖ ‖H_T‖ ‖H_L‖ ‖L‖ ‖R‖`, so uniformly
bounded maps and supported inverses turn a vanishing residual into a vanishing projection defect.
This extends `ContinuousLinearMap.injectiveRangeProjector_comp_sub_of_factorizations`.

These are algebraic identities and norm consequences reconstructed for the projector comparison
in Nachtergaele, arXiv:cond-mat/9410110, Lemma `commutation` (ii), lines 2442--2531.

Moved from TNLean, `TNLean/Algebra/SupportedRangeProjector.lean` and
`TNLean/Algebra/SupportedRangeProjectorNorm.lean` at commit `49b78ed821` (Apache-2.0). Changes:
the two files are merged; docstrings rewritten.

## Main results

* `ContinuousLinearMap.comp_supportedGramInverse_adjoint_eq_starProjection`
* `ContinuousLinearMap.starProjection_comp_sub_of_supportedGramFactorizations`
* `ContinuousLinearMap.norm_starProjection_comp_sub_le_of_supported_factorization`
* `ContinuousLinearMap.tendsto_norm_starProjection_comp_sub_zero_of_supported_factorizations`
-/

open scoped InnerProductSpace
namespace ContinuousLinearMap
variable {𝕜 E F G W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [FiniteDimensional 𝕜 W] [CompleteSpace W]
/-- The supported-Gram formula for an orthogonal range projection. The support
operator is self-adjoint and acts as the identity through the map;
no injectivity or self-adjointness of the chosen inverse is required.
This is an algebraic prerequisite for Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (ii), lines 2442--2531. -/
theorem comp_supportedGramInverse_adjoint_eq_starProjection
    (T : E →L[𝕜] F) (H Q : E →L[𝕜] E)
    (hQ : Q.adjoint = Q) (hTQ : T.comp Q = T)
    (hGH : (T.adjoint.comp T).comp H = Q) :
    T.comp (H.comp T.adjoint) = T.range.starProjection := by
  have hQadj : Q.comp T.adjoint = T.adjoint := by
    simpa only [adjoint_comp, hQ] using congrArg
      (fun S : E →L[𝕜] F => S.adjoint) hTQ
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨H (T.adjoint x), rfl⟩
  · rw [Submodule.mem_orthogonal']
    rintro _ ⟨y, rfl⟩
    change ⟪x - (T.comp (H.comp T.adjoint)) x, T y⟫_𝕜 = 0
    rw [← T.adjoint_inner_left y]
    suffices T.adjoint (x - (T.comp (H.comp T.adjoint)) x) = 0 by
      rw [this, inner_zero_left]
    rw [map_sub]
    change T.adjoint x - (((T.adjoint.comp T).comp H).comp T.adjoint) x = 0
    rw [hGH, hQadj, sub_self]

/-- Exact mixed-Gram residual for three maps with supported Gram inverses and a common
factorization. The inverse associated with the first map is self-adjoint;
the other inverse equations suffice without that assumption. The identity
retains the support operators.
Reconstructed for Nachtergaele, arXiv:cond-mat/9410110,
Lemma `commutation` (ii), lines 2442--2531; no norm estimate is asserted. -/
theorem starProjection_comp_sub_of_supportedGramFactorizations
    (T : E →L[𝕜] F) (L : G →L[𝕜] F) (C : W →L[𝕜] F)
    (J₁ : W →L[𝕜] E) (J₂ : W →L[𝕜] G)
    (HT QT : E →L[𝕜] E) (HL QL : G →L[𝕜] G) (HC QC : W →L[𝕜] W)
    (hHT : HT.adjoint = HT) (hQT : QT.adjoint = QT) (hTQ : T.comp QT = T)
    (hGT : (T.adjoint.comp T).comp HT = QT)
    (hQL : QL.adjoint = QL) (hLQ : L.comp QL = L)
    (hGL : (L.adjoint.comp L).comp HL = QL)
    (hQC : QC.adjoint = QC) (hCQ : C.comp QC = C)
    (hGC : (C.adjoint.comp C).comp HC = QC)
    (hTC : T.comp J₁ = C) (hLC : L.comp J₂ = C) :
    T.range.starProjection.comp L.range.starProjection - C.range.starProjection =
      T.comp (HT.comp ((T.adjoint.comp L -
        (T.adjoint.comp T).comp (J₁.comp (HC.comp
          (J₂.adjoint.comp (L.adjoint.comp L))))).comp (HL.comp L.adjoint))) := by
  have hTG : HT.comp (T.adjoint.comp T) = QT := by
    simpa only [adjoint_comp, adjoint_adjoint, hHT, hQT] using
      congrArg (fun S : E →L[𝕜] E => S.adjoint) hGT
  have hQLadj : QL.comp L.adjoint = L.adjoint := by
    simpa only [adjoint_comp, hQL] using congrArg
      (fun S : G →L[𝕜] F => S.adjoint) hLQ
  have hTcancel (y : E) : T (HT (T.adjoint (T y))) = T y := by
    exact congrArg (fun S : E →L[𝕜] F => S y)
      ((congrArg (fun S : E →L[𝕜] E => T.comp S) hTG).trans hTQ)
  have hLcancel (x : F) : L.adjoint (L (HL (L.adjoint x))) = L.adjoint x := by
    exact congrArg (fun S : F →L[𝕜] G => S x)
      ((congrArg (fun S : G →L[𝕜] G => S.comp L.adjoint) hGL).trans hQLadj)
  have hLCadj : J₂.adjoint.comp L.adjoint = C.adjoint := by
    rw [← adjoint_comp, hLC]
  have hsecond : T.comp (HT.comp
      (((T.adjoint.comp T).comp (J₁.comp (HC.comp
        (J₂.adjoint.comp (L.adjoint.comp L))))).comp (HL.comp L.adjoint))) =
      C.comp (HC.comp C.adjoint) := by
    ext x
    simp only [comp_apply, hTcancel, hLcancel]
    change (T.comp J₁) (HC ((J₂.adjoint.comp L.adjoint) x)) = _
    rw [hTC, hLCadj]
  rw [← comp_supportedGramInverse_adjoint_eq_starProjection T HT QT hQT hTQ hGT,
    ← comp_supportedGramInverse_adjoint_eq_starProjection L HL QL hQL hLQ hGL,
    ← comp_supportedGramInverse_adjoint_eq_starProjection C HC QC hQC hCQ hGC]
  simp only [comp_sub, sub_comp]
  rw [hsecond]
  simp only [comp_assoc]

omit [CompleteSpace E] [CompleteSpace W] in
/-- An exact supported factorization bounds the range-projector difference
by the norms of the two maps, the two supported inverse norms, and the mixed
residual norm. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531. -/
theorem norm_starProjection_comp_sub_le_of_supported_factorization
    (T : E →L[𝕜] F) (L : G →L[𝕜] F) (C : W →L[𝕜] F)
    (HT : E →L[𝕜] E) (HL : G →L[𝕜] G) (R : G →L[𝕜] E)
    (hFactor : T.range.starProjection.comp L.range.starProjection - C.range.starProjection =
      T.comp (HT.comp (R.comp (HL.comp L.adjoint)))) :
    ‖T.range.starProjection.comp L.range.starProjection - C.range.starProjection‖ ≤
      (‖T‖ * ‖HT‖ * ‖HL‖ * ‖L‖) * ‖R‖ := by
  rw [hFactor]
  calc
    ‖T.comp (HT.comp (R.comp (HL.comp L.adjoint)))‖ ≤
        ‖T‖ * ‖HT.comp (R.comp (HL.comp L.adjoint))‖ := opNorm_comp_le _ _
    _ ≤ ‖T‖ * (‖HT‖ * (‖R‖ * (‖HL‖ * ‖L.adjoint‖))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
      refine (opNorm_comp_le HT (R.comp (HL.comp L.adjoint))).trans ?_
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg HT)
      refine (opNorm_comp_le R (HL.comp L.adjoint)).trans ?_
      exact mul_le_mul_of_nonneg_left (opNorm_comp_le HL L.adjoint) (norm_nonneg R)
    _ = _ := by rw [adjoint.norm_map]; ring

/-- Uniformly bounded map norms and supported inverse norms turn vanishing
mixed residuals into vanishing range-projector differences. The Hilbert
spaces may vary, and the filter is arbitrary. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma commutation (ii), lines 2442--2531. -/
theorem tendsto_norm_starProjection_comp_sub_zero_of_supported_factorizations
    {ι : Type*} {l : Filter ι} {𝕜 : Type*} [RCLike 𝕜]
    {E G W F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]
    [∀ i, FiniteDimensional 𝕜 (G i)] [∀ i, CompleteSpace (G i)]
    [∀ i, NormedAddCommGroup (W i)] [∀ i, InnerProductSpace 𝕜 (W i)]
    [∀ i, FiniteDimensional 𝕜 (W i)] [∀ i, CompleteSpace (W i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
    [∀ i, CompleteSpace (F i)]
    (T : (i : ι) → E i →L[𝕜] F i) (L : (i : ι) → G i →L[𝕜] F i)
    (C : (i : ι) → W i →L[𝕜] F i)
    (HT : (i : ι) → E i →L[𝕜] E i) (HL : (i : ι) → G i →L[𝕜] G i)
    (R : (i : ι) → G i →L[𝕜] E i) {K : ℝ}
    (hFactor : ∀ᶠ i in l,
      (T i).range.starProjection.comp (L i).range.starProjection -
        (C i).range.starProjection =
      (T i).comp ((HT i).comp ((R i).comp ((HL i).comp (L i).adjoint))))
    (hBound : ∀ᶠ i in l, ‖T i‖ * ‖HT i‖ * ‖HL i‖ * ‖L i‖ ≤ K)
    (hResidual : Filter.Tendsto (fun i => ‖R i‖) l (nhds 0)) :
    Filter.Tendsto (fun i =>
      ‖(T i).range.starProjection.comp (L i).range.starProjection -
        (C i).range.starProjection‖) l (nhds 0) := by
  have hUpper : Filter.Tendsto (fun i => K * ‖R i‖) l (nhds 0) := by
    simpa only [mul_zero] using hResidual.const_mul K
  refine squeeze_zero' (Filter.Eventually.of_forall fun i => norm_nonneg _) ?_ hUpper
  filter_upwards [hFactor, hBound] with i hiFactor hiBound
  exact (norm_starProjection_comp_sub_le_of_supported_factorization
    (T i) (L i) (C i) (HT i) (HL i) (R i) hiFactor).trans
    (mul_le_mul_of_nonneg_right hiBound (norm_nonneg _))
end ContinuousLinearMap
