/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Subspace.Trimming
import QICLean.Channel.Schmidt.Trimming
import QICLean.Analysis.Parameter.ViableHalfSamplingParameters
import QICLean.Analysis.Subspace.ViableSubspace
import QICLean.Analysis.FunctionalCalculus.ViableSubspaceSpectralProjector

/-!
# Collective trimming is independent of the orthonormal basis

The marginal at each cut depends only on the original Gram operator.
Thus families with the same Gram operator give the same literal trimming
projections. In particular, collective trimming does not depend on the
orthonormal basis used to describe its input subspace.

Source: ALVV, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655.

It also contains the following results.

* `Entropy.finrank_family_image_trim_le`, `Entropy.isCloseTo_terminal_family_reference_trim`: a
  deterministic terminal family image with original-target reference trimming.
-/

section TrimmingInvariance

open Matrix

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- Cutting the physical sites and then tracing the remaining physical
sites and environment is the regional partial trace of the original left
marginal. This identifies the reduced operators in ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem leftMarginal_cutEnvVector {β : Type*} [Fintype β]
    (D : Finset V) (w : EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)) :
    leftMarginal (cutEnvVector D w) = partialTraceRight
        (ManyBody.cutOperator D (leftMarginal w)) := by
  ext x y
  simp only [leftMarginal, mul_apply, conjTranspose_apply, schmidtCoeffMatrix_apply,
    cutEnvVector_apply, partialTraceRight_apply, reindex_apply,
    submatrix_apply, Fintype.sum_prod_type]

/-- After an arbitrary physical operator, every cut marginal is determined
by the original Gram operator. Used for the successive projections of ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem leftMarginal_cutEnvVector_leftApply {β : Type*} [Fintype β]
    (D : Finset V) (P : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ)
    (w : EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)) :
    leftMarginal (cutEnvVector D (leftApply P w)) =
      partialTraceRight (ManyBody.cutOperator D (P * leftMarginal w * Pᴴ)) := by
  rw [leftMarginal_cutEnvVector, leftMarginal_leftApply]

/-- Families with equal Gram operators give the same literal products of
successive trimming projections. No monotonicity of the cuts or positive
threshold is needed for this identity. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem trimProj_eq_of_leftMarginal_stackVector_eq {s t : ℕ}
    (D : ℕ → Finset V) (xi : ℝ)
    (u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v)))
    (v : Fin t → EuclideanSpace ℂ (∀ v, Fin (n v)))
    (h : leftMarginal (stackVector u) = leftMarginal (stackVector v)) (j : ℕ) :
    trimProj D xi u j = trimProj D xi v j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [trimProj, ih, leftMarginal_cutEnvVector_leftApply, h]

omit [Fintype V] [DecidableEq V] in
/-- The Gram operator of the stacked family is the sum of its rank-one
operators. This is the original operator determining ALVV collective
trimming, arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem leftMarginal_stackVector {s : ℕ}
    (u : Fin s → EuclideanSpace ℂ (∀ v, Fin (n v))) :
    leftMarginal (stackVector u) =
      ∑ i, vecMulVec (WithLp.ofLp (u i)) (star (WithLp.ofLp (u i))) := by
  ext x y
  simp only [leftMarginal, mul_apply, conjTranspose_apply, schmidtCoeffMatrix_apply,
    stackVector, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply]

/-- For an orthonormal basis of a subspace, the original stacked Gram
operator is exactly its orthogonal projection. Thus the input to ALVV
collective trimming depends only on the subspace; see
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem toEuclideanLin_leftMarginal_stackVector_orthonormalBasis {s : ℕ}
    {S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v)))}
    (b : OrthonormalBasis (Fin s) ℂ S) :
    toEuclideanLin (leftMarginal (stackVector fun i ↦ (b i : EuclideanSpace ℂ (∀ v, Fin (n v))))) =
      S.starProjection.toLinearMap := by
  rw [leftMarginal_stackVector, map_sum]
  have hstar := congrArg
    (fun P : EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)) ↦
      P.toLinearMap) b.starProjection_eq_sum_rankOne
  rw [hstar]
  simp only [ContinuousLinearMap.toLinearMap_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := congrArg toEuclideanLin
    (InnerProductSpace.symm_toEuclideanLin_rankOne (𝕜 := ℂ)
      (x := (b i : EuclideanSpace ℂ (∀ v, Fin (n v))))
      (y := (b i : EuclideanSpace ℂ (∀ v, Fin (n v)))))
  simpa using h.symm

/-- The successive collective-trimming projections are independent of
which orthonormal basis describes the original subspace. This is the
basis invariance of ALVV, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. -/
theorem trimProj_eq_of_orthonormalBasis {s t : ℕ}
    (D : ℕ → Finset V) (xi : ℝ)
    {S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v)))}
    (b : OrthonormalBasis (Fin s) ℂ S) (c : OrthonormalBasis (Fin t) ℂ S) (j : ℕ) :
    trimProj D xi (fun i ↦ (b i : EuclideanSpace ℂ (∀ v, Fin (n v)))) j =
      trimProj D xi (fun i ↦ (c i : EuclideanSpace ℂ (∀ v, Fin (n v)))) j := by
  apply trimProj_eq_of_leftMarginal_stackVector_eq
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_leftMarginal_stackVector_orthonormalBasis,
    toEuclideanLin_leftMarginal_stackVector_orthonormalBasis]

/-- The actual trimmed span is the image of the original subspace under
its literal product of collective projections. Source: ALVV,
arXiv:1602.08828v2, Definition `def:trimming`, lines 648–655. -/
theorem trimSubspace_eq_map_of_orthonormalBasis {s : ℕ}
    (D : ℕ → Finset V) (xi : ℝ)
    {S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v)))}
    (b : OrthonormalBasis (Fin s) ℂ S) (j : ℕ) :
    trimSubspace D xi (fun i ↦ (b i : EuclideanSpace ℂ (∀ v, Fin (n v)))) j =
      S.map (toEuclideanLin
        (trimProj D xi (fun i ↦ (b i : EuclideanSpace ℂ (∀ v, Fin (n v)))) j)) := by
  have hspan : Submodule.span ℂ
      (Set.range fun i ↦ (b i : EuclideanSpace ℂ (∀ v, Fin (n v)))) = S := by
    simpa only [← Set.range_comp, Function.comp_def] using
      (Submodule.span_val_image_eq_iff S (Set.range b)).mpr b.toBasis.span_eq
  rw [trimSubspace, Set.range_comp', ← Submodule.map_span, hspan]

/-- The literal trimmed subspace is independent of its prescribed
orthonormal basis, including the zero subspace and zero or negative
thresholds. Source: ALVV, arXiv:1602.08828v2,
Definition `def:trimming`, lines 648–655. -/
theorem trimSubspace_eq_of_orthonormalBasis {s t : ℕ}
    (D : ℕ → Finset V) (xi : ℝ)
    {S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v)))}
    (b : OrthonormalBasis (Fin s) ℂ S) (c : OrthonormalBasis (Fin t) ℂ S) (j : ℕ) :
    trimSubspace D xi (fun i ↦ (b i : EuclideanSpace ℂ (∀ v, Fin (n v)))) j =
      trimSubspace D xi (fun i ↦ (c i : EuclideanSpace ℂ (∀ v, Fin (n v)))) j := by
  rw [trimSubspace_eq_map_of_orthonormalBasis, trimSubspace_eq_map_of_orthonormalBasis,
    trimProj_eq_of_orthonormalBasis D xi b c j]

end Entropy

end TrimmingInvariance

section TerminalFamilyReferenceTrimming

/-!
## A deterministic terminal family image with original-target reference trimming

After a stopped resampling loop, including a loop that takes no active round,
the same full improving family is applied once before collective trimming.
Its exact improving-target error is retained. All target and reference data
are fixed before the current input space; no further sample is selected.

This supports ALVV, arXiv:1602.08828v2, the resampling description at
lines 749–755 and the reference argument at lines 1801–1813.
This module treats a repeated-resampling variant of the merge procedure
sketched at arXiv:1602.08828v2, lines 711–755; Figure `fig:merge-prime` and
Theorem `t:alg1` are not formalized here. See
`docs/paper-gaps/alvv16_bootstrap_constants.tex`.
**Local fix (trimming constant):** The estimate retains the corrected
increment recorded in `docs/paper-gaps/alvv16_trimming_constant.tex`.
-/

open Module

namespace Entropy

variable {V β X ι : Type*} [Fintype V] [DecidableEq V]
  [Fintype β] [Fintype ι] {n : V → ℕ}

/-- A full finite-family image and its literal collective trim have the
same unconditional cardinality-times-dimension bound. No target, viability,
monotone-cut or positive-threshold premise is needed. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:er`, lines 597–622, and trimming, lines 648–655. -/
theorem finrank_family_image_trim_le
    (C : ℕ → Finset V) (xi : ℝ) (m : ℕ)
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
    (W : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v)))) :
    let image : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) :=
      ⨆ i, W.map (A i : _ →ₗ[ℂ] _)
    let output := trimSubspace C xi
      (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (∀ v, Fin (n v)))) m
    finrank ℂ image ≤ Fintype.card ι * finrank ℂ W ∧
      finrank ℂ output ≤ Fintype.card ι * finrank ℂ W := by
  intro image output
  have hdim : finrank ℂ image ≤ Fintype.card ι * finrank ℂ W :=
    Submodule.finrank_iSup_map_le_card_mul W (fun i ↦ (A i).toLinearMap)
  refine ⟨hdim, ?_⟩
  change finrank ℂ (trimSubspace C xi
    (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (∀ v, Fin (n v)))) m) ≤ _
  rw [trimSubspace_eq_map_of_orthonormalBasis]
  exact (Submodule.finrank_map_le _ _).trans hdim

/-- One application of the same full family and the same original-reference
trim restores the original-target error after a stopped resampling loop.
The exact improving-target error is retained, without a sign assumption on
Delta. This is a conditional terminal auxiliary to ALVV,
arXiv:1602.08828v2, lines 749–755 and 1801–1813, not a runtime theorem. -/
theorem isCloseTo_terminal_family_reference_trim
    {D m bRef : ℕ} {Delta epsilonRef xi : ℝ}
    {Graw R : Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β))}
    (x0 : X) (T : X → Submodule ℂ (EuclideanSpace ℂ ((∀ v, Fin (n v)) × β)))
    (A : ι → EuclideanSpace ℂ (∀ v, Fin (n v)) →L[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)))
    (hcard : Fintype.card ι ≤ D ^ 2)
    (hRawSoft : ∀ x, Submodule.IsCloseTo (1 / 200) Graw (T x))
    (hSoftRaw : ∀ x, Submodule.IsCloseTo (1 / 200) (T x) Graw)
    (hA : ∀ x delta, delta < 1 →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))),
      Submodule.IsCloseTo delta (Submodule.prodExt S β) (T x) →
      Submodule.IsCloseTo (Delta / (1 - delta) ^ 2)
        (Submodule.prodExt (⨆ i, S.map (A i : _ →ₗ[ℂ] _)) β) (T x))
    (hD : 2 ≤ D) (hDelta : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000)
    (C : ℕ → Finset V) (hC : Monotone C) (hxi : 0 < xi)
    (hepsilonRef0 : 0 ≤ epsilonRef) (hepsilonRef : epsilonRef ≤ 1 / 100000)
    (hRawRef : Submodule.IsCloseTo epsilonRef Graw R)
    (hRefRaw : Submodule.IsCloseTo epsilonRef R Graw)
    (hRank : ∀ t ∈ R, ∀ j < m,
      Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (C j) t)) ≤ bRef)
    (hbudget : xi * Real.sqrt ((m : ℝ) * (bRef : ℝ)) ≤ 1 / 1000)
    (W : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))))
    (hW : Submodule.IsCloseTo 0.04 (Submodule.prodExt W β) Graw) :
    let image : Submodule ℂ (EuclideanSpace ℂ (∀ v, Fin (n v))) :=
      ⨆ i, W.map (A i : _ →ₗ[ℂ] _)
    let output := trimSubspace C xi
      (fun i ↦ (stdOrthonormalBasis ℂ image i : EuclideanSpace ℂ (∀ v, Fin (n v)))) m
    (∀ x, Submodule.IsCloseTo (Delta / (91 / 100 : ℝ) ^ 2)
      (Submodule.prodExt image β) (T x)) ∧
    Submodule.IsCloseTo (27 / 2500) (Submodule.prodExt image β) Graw ∧
    Submodule.IsCloseTo (3 / 200) (Submodule.prodExt output β) Graw ∧
    finrank ℂ image ≤ D ^ 2 * finrank ℂ W ∧
    finrank ℂ output ≤ D ^ 2 * finrank ℂ W := by
  intro image output
  have hImageTarget (x) :
      Submodule.IsCloseTo (Delta / (91 / 100 : ℝ) ^ 2)
        (Submodule.prodExt image β) (T x) := by
    have hInput : Submodule.IsCloseTo (9 / 100)
        (Submodule.prodExt W β) (T x) :=
      by
        simpa only [show (2 * (0.04 + 1 / 200) : ℝ) = 9 / 100 by norm_num] using
          Submodule.IsCloseTo.trans hW (hRawSoft x) (by norm_num)
    have hh := hA x (9 / 100) (by norm_num) W hInput
    simpa only [show (1 - 9 / 100 : ℝ) = 91 / 100 by norm_num] using hh
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hsq : (4 : ℝ) ≤ (D : ℝ) ^ 2 := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (D : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hDreal 2
  have hfilter : Delta / (91 / 100 : ℝ) ^ 2 ≤ 1 / 10000 :=
    Real.half_sampling_filter_error_le hDreal hDelta
      ((div_le_iff₀ (by linarith only [hsq] : (0 : ℝ) < (D : ℝ) ^ 2)).mpr
        (by nlinarith only [hsq]))
  have hImageSmall : Submodule.IsCloseTo (1 / 10000)
      (Submodule.prodExt image β) (T x0) :=
    (hImageTarget x0).of_le hfilter
  have hImageBack : Submodule.IsCloseTo (2 * ((1 / 10000) + (1 / 200)))
      (Submodule.prodExt image β) Graw :=
    Submodule.IsCloseTo.trans hImageSmall (hSoftRaw x0) (by norm_num)
  have hImageRaw : Submodule.IsCloseTo (27 / 2500)
      (Submodule.prodExt image β) Graw := hImageBack.of_le (by norm_num)
  have hOutputRaw : Submodule.IsCloseTo (3 / 200)
      (Submodule.prodExt output β) Graw := by
    have ht := isCloseTo_prodExt_trimSubspace_of_reference_weighted hC hxi
      (by norm_num : (0 : ℝ) ≤ 27 / 2500) hepsilonRef0
      (by norm_num : (0 : ℝ) < 1 / 20)
      (stdOrthonormalBasis ℂ image) hImageRaw hRawRef hRefRaw hRank
    exact ht.of_le (Real.half_sampling_trim_error_le le_rfl hepsilonRef hbudget)
  obtain ⟨hImageDim, hOutputDim⟩ := finrank_family_image_trim_le C xi m A W
  have hcount : Fintype.card ι * finrank ℂ W ≤ D ^ 2 * finrank ℂ W :=
    Nat.mul_le_mul_right _ hcard
  exact ⟨hImageTarget, hImageRaw, hOutputRaw,
    hImageDim.trans hcount, hOutputDim.trans hcount⟩

end Entropy

end TerminalFamilyReferenceTrimming
