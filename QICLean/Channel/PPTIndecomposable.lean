/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.DecomposablePPT
import QICLean.Channel.DecomposableWitness
import QICLean.Channel.PositiveMapDetection
import QICLean.Channel.Schwarz.PositiveMapProperties

/-!
# PPT entangled states and indecomposable positive maps

This module proves both directions of Wolf, Chapter 3, Proposition 3.5:
an indecomposable positive map `M_d(ℂ) → M_{d'}(ℂ)` exists if and only if
a PPT entangled density operator exists on `ℂ^d ⊗ ℂ^{d'}`.

The implication from a PPT entangled state to an indecomposable map is Wolf's
Proposition 3.4 followed by decomposable-PPT preservation.  For the converse,
the proof follows Lewenstein--Kraus--Cirac--Horodecki, Theorem 3, on the
trace-one compact base of decomposable witnesses

`a P + (1-a) Q^{T₁}`,

where `P,Q` are density operators.  The partial transpose is always on Wolf's
first tensor factor.

## Main results

* `exists_isIndecomposablePositiveMap_of_isPPT_not_isSeparable` gives the
  positive-map detector of a PPT entangled density operator.
* `IsIndecomposablePositiveMap.exists_isPPT_not_isSeparable` constructs a PPT
  entangled density operator from an indecomposable positive map.
* `exists_isIndecomposablePositiveMap_iff_exists_isPPT_not_isSeparable` is
  Wolf Proposition 3.5 in fixed nonzero dimensions.
* `exists_isIndecomposablePositiveMap_iff_exists_isPPT_not_isSeparable_all_dimensions`
  includes the explicit zero-dimensional cases.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Proposition 3.5][Wolf2012QChannels]
* M. Lewenstein, B. Kraus, J. I. Cirac, and P. Horodecki,
  *Optimization of entanglement witnesses*, Theorem 3,
  arXiv:quant-ph/0005014v3.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace Matrix

variable {d d' : ℕ}

open ChoiJamiolkowski ChoiRectangular

/-! ## PPT entanglement gives an indecomposable positive map -/

/-- **PPT entanglement gives an indecomposable positive map (Wolf Proposition
3.5, easy direction).** If `ρ` is a density operator on `ℂ^d ⊗ ℂ^{d'}`, has
positive first-factor partial transpose, and is not separable, then there is an
indecomposable positive map `T : M_d(ℂ) → M_{d'}(ℂ)`.

The map is the `n = 1` detector from the rectangular positive-map criterion
(Wolf Proposition 3.4). One-positivity is positivity, and decomposable maps
preserve positivity on PPT states, so a map detected by `ρ` cannot be
decomposable. -/
theorem exists_isIndecomposablePositiveMap_of_isPPT_not_isSeparable [NeZero d']
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) (hPPT : IsPPT ρ)
    (hentangled : ¬ IsSeparable ρ) :
    ∃ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
      IsIndecomposablePositiveMap T := by
  rw [← hasSchmidtNumberLE_one_iff_isSeparable] at hentangled
  obtain ⟨T, hT, hneg⟩ :=
    exists_isNPositiveMap_tensorMapId_not_posSemidef 1 hρ.isHermitian hρtr hentangled
  refine ⟨T, ?_⟩
  exact (isNPositiveMap_one_iff_isPositiveMap.mp hT)
    |>.isIndecomposablePositiveMap_of_isPPT_not_tensorMapId_posSemidef hρ hPPT hneg

/-! ## Separator positivity at the two normalized endpoints -/

private theorem isDecomposablePositiveMap_zero :
    IsDecomposablePositiveMap
      (0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) := by
  have hzeroCP :
      IsKrausCP
        (0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) := by
    refine ⟨0, fun i ↦ Fin.elim0 i, ?_⟩
    intro X
    simp
  refine ⟨0, 0, hzeroCP, ?_, by simp⟩
  simpa [IsCompletelyCopositiveMap] using hzeroCP

private theorem IsNormalizedDecomposableWitness.isHermitian
    {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hW : IsNormalizedDecomposableWitness W) : W.IsHermitian := by
  obtain ⟨a, P, Q, _ha, hP, _hPtr, hQ, _hQtr, rfl⟩ := hW
  exact (hP.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))).add
    ((hQ.isHermitian.partialTransposeLeft).smul
      (isSelfAdjoint_iff.mpr (by simp)))

private theorem posSemidef_and_isPPT_of_nonneg_on_normalized_decomposable
    [NeZero d] [NeZero d']
    {R : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hR : R.IsHermitian)
    (hRnonneg : ∀ X, IsNormalizedDecomposableWitness X →
      0 ≤ (X * R).trace.re) :
    R.PosSemidef ∧ IsPPT R := by
  classical
  let x₀ : Fin d × Fin d' := (0, 0)
  refine ⟨?_, ?_⟩
  · apply PosSemidef.of_forall_trace_mul_nonneg hR
    intro B hB
    let B₀ := normalizePosSemidef x₀ B
    have hB₀ : B₀.PosSemidef := normalizePosSemidef_posSemidef x₀ hB
    have hB₀tr : B₀.trace = 1 := normalizePosSemidef_trace x₀ hB
    have hB₀mem : IsNormalizedDecomposableWitness B₀ := by
      refine ⟨1, B₀, B₀, by simp, hB₀, hB₀tr, hB₀, hB₀tr, ?_⟩
      simp
    have hB₀nonneg : 0 ≤ (R * B₀).trace.re := by
      have h := hRnonneg B₀ hB₀mem
      rw [trace_mul_comm] at h
      exact h
    have hB₀im : (R * B₀).trace.im = 0 := by
      have hreal : (R * B₀).trace = star ((R * B₀).trace) := by
        rw [← trace_conjTranspose, conjTranspose_mul, hB₀.isHermitian.eq, hR.eq,
          trace_mul_comm]
      have him := congrArg Complex.im hreal
      simp only [Complex.star_def, Complex.conj_im] at him
      linarith
    have hB₀pair : (0 : ℂ) ≤ (R * B₀).trace :=
      Complex.nonneg_iff.mpr ⟨hB₀nonneg, hB₀im.symm⟩
    have htrace_nonneg : (0 : ℂ) ≤ (B.trace.re : ℂ) := by
      exact_mod_cast (Complex.nonneg_iff.mp hB.trace_nonneg).1
    rw [← trace_re_smul_normalizePosSemidef x₀ hB, Matrix.mul_smul, trace_smul,
      smul_eq_mul]
    exact mul_nonneg htrace_nonneg hB₀pair
  · apply PosSemidef.of_forall_trace_mul_nonneg hR.partialTransposeLeft
    intro B hB
    let B₀ := normalizePosSemidef x₀ B
    have hB₀ : B₀.PosSemidef := normalizePosSemidef_posSemidef x₀ hB
    have hB₀tr : B₀.trace = 1 := normalizePosSemidef_trace x₀ hB
    have hB₀mem :
        IsNormalizedDecomposableWitness (partialTransposeLeft B₀) := by
      refine ⟨0, B₀, B₀, by simp, hB₀, hB₀tr, hB₀, hB₀tr, ?_⟩
      simp
    have hB₀nonneg : 0 ≤ (partialTransposeLeft R * B₀).trace.re := by
      have h := hRnonneg (partialTransposeLeft B₀) hB₀mem
      rw [trace_partialTransposeLeft_mul_re, trace_mul_comm] at h
      exact h
    have hB₀im : (partialTransposeLeft R * B₀).trace.im = 0 := by
      have hreal : (partialTransposeLeft R * B₀).trace =
          star ((partialTransposeLeft R * B₀).trace) := by
        rw [← trace_conjTranspose, conjTranspose_mul, hB₀.isHermitian.eq,
          hR.partialTransposeLeft.eq, trace_mul_comm]
      have him := congrArg Complex.im hreal
      simp only [Complex.star_def, Complex.conj_im] at him
      linarith
    have hB₀pair : (0 : ℂ) ≤ (partialTransposeLeft R * B₀).trace :=
      Complex.nonneg_iff.mpr ⟨hB₀nonneg, hB₀im.symm⟩
    have htrace_nonneg : (0 : ℂ) ≤ (B.trace.re : ℂ) := by
      exact_mod_cast (Complex.nonneg_iff.mp hB.trace_nonneg).1
    rw [← trace_re_smul_normalizePosSemidef x₀ hB, Matrix.mul_smul, trace_smul,
      smul_eq_mul]
    exact mul_nonneg htrace_nonneg hB₀pair

/-! ## Separation from the normalized decomposable set -/

/-- A trace-one Hermitian witness outside Wolf's decomposable cone admits a
positive-semidefinite PPT separator with strictly negative trace pairing.

This is the Hahn--Banach step in Lewenstein--Kraus--Cirac--Horodecki,
Theorem 3.  Separation is performed on the compact convex set of normalized
decomposable witnesses, rather than on the full unbounded cone. -/
theorem exists_posSemidef_isPPT_negative_separator_of_not_isDecomposableWitness
    [NeZero d] [NeZero d']
    {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hW : W.IsHermitian) (hWtr : W.trace = 1)
    (hWnot : ¬ IsDecomposableWitness W) :
    ∃ R : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ,
      R.PosSemidef ∧ IsPPT R ∧ (W * R).trace.re < 0 := by
  classical
  have : LocallyConvexSpace ℝ
      (Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :=
    NormedSpace.toLocallyConvexSpace
      (E := Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ)
  let K : Set (Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :=
    {X | IsNormalizedDecomposableWitness X}
  have hKconvex : Convex ℝ K :=
    convex_setOf_isNormalizedDecomposableWitness
  have hKcompact : IsCompact K :=
    isCompact_setOf_isNormalizedDecomposableWitness
  have hWnotmem : W ∉ K := by
    intro hWK
    exact hWnot ((isNormalizedDecomposableWitness_iff W).mp hWK).1
  obtain ⟨f, u, v, hfW, huv, hfK⟩ :=
    geometric_hahn_banach_closed_compact (convex_singleton W) isClosed_singleton
      hKconvex hKcompact (by
        rw [Set.disjoint_singleton_left]
        exact hWnotmem)
  let c : ℝ := (u + v) / 2
  have hfWc : f W < c := by
    have h := hfW W rfl
    dsimp only [c]
    linarith
  have hcK : ∀ X ∈ K, c < f X := by
    intro X hX
    have h := hfK X hX
    dsimp only [c]
    linarith
  obtain ⟨H, hH, hHrep⟩ :=
    exists_isHermitian_trace_form_re (N := Fin d × Fin d') f.toLinearMap
  have hfrep : ∀ X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ,
      X.IsHermitian → f X = (X * H).trace.re := by
    intro X hX
    have h := hHrep X hX
    rwa [ContinuousLinearMap.coe_coe] at h
  let R := H - (c : ℂ) • (1 : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ)
  have hR : R.IsHermitian := by
    refine hH.sub ?_
    rw [IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hRnonneg : ∀ X, IsNormalizedDecomposableWitness X →
      0 ≤ (X * R).trace.re := by
    intro X hX
    have hXtr : X.trace = 1 :=
      ((isNormalizedDecomposableWitness_iff X).mp hX).2
    have hpair : (X * R).trace.re = f X - c := by
      rw [show R = H - (c : ℂ) • 1 from rfl, mul_sub, trace_sub,
        Complex.sub_re, Matrix.mul_smul, mul_one, trace_smul, smul_eq_mul,
        Complex.re_ofReal_mul, hXtr, Complex.one_re, mul_one,
        ← hfrep X hX.isHermitian]
    rw [hpair]
    exact sub_nonneg.mpr (hcK X hX).le
  obtain ⟨hRpos, hRPPT⟩ :=
    posSemidef_and_isPPT_of_nonneg_on_normalized_decomposable hR hRnonneg
  refine ⟨R, hRpos, hRPPT, ?_⟩
  have hpair : (W * R).trace.re = f W - c := by
    rw [show R = H - (c : ℂ) • 1 from rfl, mul_sub, trace_sub,
      Complex.sub_re, Matrix.mul_smul, mul_one, trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul, hWtr, Complex.one_re, mul_one, ← hfrep W hW]
  rw [hpair]
  linarith

/-! ## Normalization and entanglement -/

/-- A normalized nondecomposable entanglement witness detects a PPT entangled
density operator.  This is Lewenstein--Kraus--Cirac--Horodecki, Theorem 3,
with the partial transpose fixed on Wolf's first tensor factor. -/
theorem exists_isPPT_not_isSeparable_of_not_isDecomposableWitness
    [NeZero d] [NeZero d']
    {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hW : W.IsHermitian) (hWtr : W.trace = 1)
    (hWnot : ¬ IsDecomposableWitness W)
    (hWnonneg : ∀ ψ : Fin d × Fin d' → ℂ, HasSchmidtRankLE 1 ψ →
      0 ≤ (W * vecMulVec ψ (star ψ)).trace.re) :
    ∃ ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ IsPPT ρ ∧ ¬ IsSeparable ρ := by
  classical
  obtain ⟨R, hR, hRPPT, hWRneg⟩ :=
    exists_posSemidef_isPPT_negative_separator_of_not_isDecomposableWitness
      hW hWtr hWnot
  have hRne : R ≠ 0 := by
    intro hRzero
    rw [hRzero] at hWRneg
    simp at hWRneg
  have hRtrace_pos_complex : 0 < R.trace := hR.trace_pos_of_ne_zero hRne
  have hRtrace_pos : 0 < R.trace.re :=
    (Complex.lt_def.mp hRtrace_pos_complex).1
  let x₀ : Fin d × Fin d' := (0, 0)
  let ρ := normalizePosSemidef x₀ R
  have hρ : ρ.PosSemidef := normalizePosSemidef_posSemidef x₀ hR
  have hρtr : ρ.trace = 1 := normalizePosSemidef_trace x₀ hR
  have hρform : ρ = (((R.trace.re)⁻¹ : ℝ) : ℂ) • R := by
    simp [ρ, normalizePosSemidef, ne_of_gt hRtrace_pos]
  have hρPPT : IsPPT ρ := by
    rw [IsPPT, hρform, partialTransposeLeft_smul]
    exact hRPPT.smul (by
      exact_mod_cast inv_nonneg.mpr hRtrace_pos.le)
  have hWρneg : (W * ρ).trace.re < 0 := by
    rw [hρform, Matrix.mul_smul, trace_smul, smul_eq_mul,
      Complex.re_ofReal_mul]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hRtrace_pos) hWRneg
  have hρnotSchmidt : ¬ HasSchmidtNumberLE 1 ρ :=
    not_hasSchmidtNumberLE_of_exists_witness 1
      ⟨W, hW, hWρneg, hWnonneg⟩
  refine ⟨ρ, hρ, hρtr, hρPPT, ?_⟩
  intro hρsep
  exact hρnotSchmidt hρsep.hasSchmidtNumberLE_one

/-! ## The trace-adjoint Choi witness of an indecomposable map -/

/-- An indecomposable positive map yields a PPT entangled density operator.
The witness is the normalized rectangular Choi matrix of the trace adjoint,
in Wolf's output-first orientation. -/
theorem IsIndecomposablePositiveMap.exists_isPPT_not_isSeparable
    [NeZero d] [NeZero d']
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsIndecomposablePositiveMap T) :
    ∃ ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ IsPPT ρ ∧ ¬ IsSeparable ρ := by
  classical
  let W₀ := ChoiRectangular.choiMatrix (traceAdjointMap T)
  have hTne : T ≠ 0 := by
    intro hTzero
    apply hT.2
    rw [hTzero]
    exact isDecomposablePositiveMap_zero
  have hTone : T 1 ≠ 0 := by
    intro hTone
    apply hTne
    apply LinearMap.ext
    intro X
    have hzero := hT.1.map_mul_eq_zero_of_map_projection_eq_zero
      (P := (1 : Matrix (Fin d) (Fin d) ℂ)) (by simp [IsHermitian])
      (by simp [IsIdempotentElem]) hTone X
    simpa using hzero.1
  have hTonePos : (T 1).PosSemidef := hT.1 1 PosSemidef.one
  have hscale : (0 : ℂ) < 1 / (d' : ℂ) := by
    have hd'pos : (0 : ℝ) < d' := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d')
    have hscaleReal : (0 : ℝ) < 1 / (d' : ℝ) := one_div_pos.mpr hd'pos
    rw [show 1 / (d' : ℂ) = (((1 / d' : ℝ)) : ℂ) by push_cast; ring,
      Complex.lt_def]
    exact ⟨hscaleReal, by simp⟩
  have hW₀trace_pos : 0 < W₀.trace := by
    rw [show W₀ = ChoiRectangular.choiMatrix (traceAdjointMap T) from rfl,
      ChoiRectangular.trace_choiMatrix, traceAdjointMap_traceAdjointMap]
    exact mul_pos hscale (hTonePos.trace_pos_of_ne_zero hTone)
  have hW₀trace_re_pos : 0 < W₀.trace.re :=
    (Complex.lt_def.mp hW₀trace_pos).1
  have hW₀trace_real : W₀.trace = (W₀.trace.re : ℂ) := by
    apply Complex.ext
    · simp
    · exact (Complex.lt_def.mp hW₀trace_pos).2.symm
  have hW₀ : W₀.IsHermitian := by
    apply (ChoiRectangular.choiMatrix_isHermitian_iff_hermiticityPreserving
      (traceAdjointMap T)).mpr
    exact hT.1.traceAdjointMap.map_conjTranspose
  have hW₀nonneg : ∀ ψ : Fin d × Fin d' → ℂ, HasSchmidtRankLE 1 ψ →
      0 ≤ (W₀ * vecMulVec ψ (star ψ)).trace.re := by
    intro ψ hψ
    have hquad :=
      IsNPositiveMap.choiMatrix_quadraticForm_nonneg_of_hasSchmidtRankLE_rectangular
        (isNPositiveMap_one_iff_isPositiveMap.mpr hT.1.traceAdjointMap) hψ
    rw [show W₀ = ChoiRectangular.choiMatrix (traceAdjointMap T) from rfl,
      ChoiJamiolkowski.trace_mul_vecMulVec_eq_dotProduct]
    exact (Complex.nonneg_iff.mp hquad).1
  let W := (((W₀.trace.re)⁻¹ : ℝ) : ℂ) • W₀
  have hW : W.IsHermitian :=
    hW₀.smul (isSelfAdjoint_iff.mpr (by simp))
  have hWtr : W.trace = 1 := by
    rw [show W = (((W₀.trace.re)⁻¹ : ℝ) : ℂ) • W₀ from rfl,
      trace_smul, smul_eq_mul, hW₀trace_real]
    exact_mod_cast inv_mul_cancel₀ (ne_of_gt hW₀trace_re_pos)
  have hWnonneg : ∀ ψ : Fin d × Fin d' → ℂ, HasSchmidtRankLE 1 ψ →
      0 ≤ (W * vecMulVec ψ (star ψ)).trace.re := by
    intro ψ hψ
    rw [show W = (((W₀.trace.re)⁻¹ : ℝ) : ℂ) • W₀ from rfl,
      Matrix.smul_mul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg (inv_nonneg.mpr hW₀trace_re_pos.le) (hW₀nonneg ψ hψ)
  have hWscale : (W₀.trace.re : ℂ) • W = W₀ := by
    rw [show W = (((W₀.trace.re)⁻¹ : ℝ) : ℂ) • W₀ from rfl,
      smul_smul]
    norm_num [ne_of_gt hW₀trace_re_pos]
  have hWnot : ¬ IsDecomposableWitness W := by
    intro hWdec
    apply hT.2
    apply
      (isDecomposablePositiveMap_iff_choiMatrix_traceAdjointMap_isDecomposableWitness
        T).mpr
    obtain ⟨P, Q, hP, hQ, hWdecomp⟩ := hWdec
    refine ⟨(W₀.trace.re : ℂ) • P, (W₀.trace.re : ℂ) • Q,
      hP.smul (by exact_mod_cast hW₀trace_re_pos.le),
      hQ.smul (by exact_mod_cast hW₀trace_re_pos.le), ?_⟩
    calc
      ChoiRectangular.choiMatrix (traceAdjointMap T) = W₀ := rfl
      _ = (W₀.trace.re : ℂ) • W := hWscale.symm
      _ = (W₀.trace.re : ℂ) • (P + partialTransposeLeft Q) := by rw [hWdecomp]
      _ = (W₀.trace.re : ℂ) • P +
          partialTransposeLeft ((W₀.trace.re : ℂ) • Q) := by
            rw [smul_add, partialTransposeLeft_smul]
  exact exists_isPPT_not_isSeparable_of_not_isDecomposableWitness
    hW hWtr hWnot hWnonneg

/-- **Wolf Proposition 3.5 in fixed nonzero dimensions.** There exists an
indecomposable positive map `M_d(ℂ) → M_{d'}(ℂ)` if and only if there
exists a PPT entangled density operator on `ℂ^d ⊗ ℂ^{d'}`. -/
theorem exists_isIndecomposablePositiveMap_iff_exists_isPPT_not_isSeparable
    [NeZero d] [NeZero d'] :
    (∃ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
      IsIndecomposablePositiveMap T) ↔
    ∃ ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ IsPPT ρ ∧ ¬ IsSeparable ρ := by
  constructor
  · rintro ⟨T, hT⟩
    exact IsIndecomposablePositiveMap.exists_isPPT_not_isSeparable hT
  · rintro ⟨ρ, hρ, hρtr, hρPPT, hρentangled⟩
    exact exists_isIndecomposablePositiveMap_of_isPPT_not_isSeparable
      hρ hρtr hρPPT hρentangled

/-- Wolf Proposition 3.5 in arbitrary finite dimensions.  If either tensor
factor is zero-dimensional, both sides are empty: every relevant linear map
is the zero (hence decomposable) map, while a matrix on the empty tensor
product cannot have trace one. -/
theorem exists_isIndecomposablePositiveMap_iff_exists_isPPT_not_isSeparable_all_dimensions
    (d d' : ℕ) :
    (∃ T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ,
      IsIndecomposablePositiveMap T) ↔
    ∃ ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ,
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ IsPPT ρ ∧ ¬ IsSeparable ρ := by
  by_cases hd : d = 0
  · subst d
    constructor
    · rintro ⟨T, hT⟩
      exfalso
      apply hT.2
      have hTzero : T = 0 := Subsingleton.elim _ _
      rw [hTzero]
      exact isDecomposablePositiveMap_zero
    · rintro ⟨ρ, _hρ, hρtr, _hρPPT, _hρentangled⟩
      exfalso
      simp at hρtr
  · by_cases hd' : d' = 0
    · subst d'
      constructor
      · rintro ⟨T, hT⟩
        exfalso
        apply hT.2
        have hTzero : T = 0 := Subsingleton.elim _ _
        rw [hTzero]
        exact isDecomposablePositiveMap_zero
      · rintro ⟨ρ, _hρ, hρtr, _hρPPT, _hρentangled⟩
        exfalso
        simp at hρtr
    · let _ : NeZero d := ⟨hd⟩
      let _ : NeZero d' := ⟨hd'⟩
      exact exists_isIndecomposablePositiveMap_iff_exists_isPPT_not_isSeparable

end Matrix
