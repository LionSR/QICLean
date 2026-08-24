/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.ChoiRectangular
import QICLean.Channel.KrausCPTP
import QICLean.Channel.PartialTranspose
import QICLean.Channel.SchmidtNumberCompact
import QICLean.Algebra.PositiveSemidefiniteNormalization

/-!
# Decomposable witnesses and the trace-adjoint Choi bridge

Wolf Chapter 3, Equation (3.15) defines a decomposable witness on
`ℂ^d ⊗ ℂ^{d'}` explicitly as

`W = P₁ + P₂^{T₁}`, with `P₁, P₂ ≥ 0`.

This file records that cone and proves its exact correspondence with
decomposable maps `T : M_d(ℂ) → M_{d'}(ℂ)`. Following Wolf's map--witness
orientation, the witness is the rectangular Choi matrix of the trace adjoint
`T* : M_{d'}(ℂ) → M_d(ℂ)`. Because rectangular Choi matrices are indexed
output-first, transposition on the output of `T*` is
`Matrix.partialTransposeLeft`.

No closedness, cone duality, or separating-hyperplane statement is asserted
here; those are separate ingredients in Wolf Proposition 3.5.

## Main declarations

* `Matrix.IsDecomposableWitness` -- the explicit cone in Wolf Equation (3.15).
* `Matrix.convex_setOf_isDecomposableWitness` -- convexity of the explicit
  decomposable-witness cone used in Wolf Proposition 3.5.
* `Matrix.IsNormalizedDecomposableWitness` -- the trace-one compact base
  `a P₁ + (1-a) P₂^{T₁}` used in the primary proof of the witness theorem.
* `Matrix.isCompact_setOf_isNormalizedDecomposableWitness` and
  `Matrix.convex_setOf_isNormalizedDecomposableWitness` -- compactness and
  convexity of that normalized base.
* `Matrix.trace_partialTransposeLeft_mul` -- first-factor partial transpose is
  self-adjoint for the bilinear trace pairing.
* `Matrix.traceAdjointMap_transposeLinearMapComplex` -- transposition is
  self-adjoint for the bilinear trace pairing.
* `ChoiRectangular.choiMatrix_transposeLinearMapComplex_comp` -- transposing
  a map's output transposes the output factor of its Choi matrix.
* `ChoiRectangular.isDecomposablePositiveMap_iff_choiMatrix_traceAdjointMap_isDecomposableWitness`
  -- the rectangular map--witness equivalence.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Equations (3.13) and (3.15)][Wolf2012QChannels]
* M. Lewenstein, B. Kraus, J. I. Cirac, and P. Horodecki,
  *Optimization of entanglement witnesses*, Theorem 3,
  arXiv:quant-ph/0005014.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace Matrix

variable {d d' : ℕ}

/-- A **decomposable witness** in the explicit sense of Wolf Chapter 3,
Equation (3.15): `W = P₁ + P₂^{T₁}` for positive semidefinite
`P₁, P₂`. The first tensor factor is `Fin d`, matching the output-first
ordering of the Choi matrix of `T* : M_{d'}(ℂ) → M_d(ℂ)`. -/
def IsDecomposableWitness
    (W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) : Prop :=
  ∃ P₁ P₂ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ,
    P₁.PosSemidef ∧ P₂.PosSemidef ∧ W = P₁ + partialTransposeLeft P₂

/-- The explicit decomposable-witness cone from Wolf Chapter 3, Equation
(3.15), is convex, as used in the proof of Proposition 3.5. Convex
combinations are taken componentwise in the two positive-semidefinite
summands. -/
theorem convex_setOf_isDecomposableWitness :
    Convex ℝ {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
      IsDecomposableWitness W} := by
  rintro X ⟨PX, QX, hPX, hQX, rfl⟩ Y ⟨PY, QY, hPY, hQY, rfl⟩ a b ha hb _hab
  refine ⟨a • PX + b • PY, a • QX + b • QY,
    (hPX.smul ha).add (hPY.smul hb), (hQX.smul ha).add (hQY.smul hb), ?_⟩
  ext p q
  simp [partialTransposeLeft_apply, Matrix.add_apply, Matrix.smul_apply]
  ring

/-! ## The normalized compact base -/

/-- Partial transpose commutes with complex scalar multiplication. -/
@[simp]
theorem partialTransposeLeft_smul (c : ℂ)
    (X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    partialTransposeLeft (c • X) = c • partialTransposeLeft X := by
  ext p q
  simp [partialTransposeLeft_apply]

/-- First-factor partial transpose is continuous on the finite-dimensional
matrix space. -/
theorem continuous_partialTransposeLeft :
    Continuous
      (partialTransposeLeft :
        Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ →
          Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) := by
  refine continuous_matrix fun p q ↦ ?_
  simp only [partialTransposeLeft_apply]
  fun_prop

/-- First-factor partial transpose is self-adjoint for the bilinear trace
pairing:

`tr(X^{T₁} Y) = tr(X Y^{T₁})`.

This is the factor orientation used when the separator in the proof of Wolf
Proposition 3.5 is tested against `Q^{T₁}`. -/
@[simp]
theorem trace_partialTransposeLeft_mul
    (X Y : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    (partialTransposeLeft X * Y).trace =
      (X * partialTransposeLeft Y).trace := by
  classical
  simp only [trace, diag, mul_apply, partialTransposeLeft_apply,
    Fintype.sum_prod_type]
  calc
    ∑ i₁, ∑ k, ∑ i₂, ∑ l,
        X (i₂, k) (i₁, l) * Y (i₂, l) (i₁, k) =
      ∑ i₁, ∑ i₂, ∑ k, ∑ l,
        X (i₂, k) (i₁, l) * Y (i₂, l) (i₁, k) := by
          apply Finset.sum_congr rfl
          intro i₁ _
          rw [Finset.sum_comm]
    _ = ∑ i₂, ∑ i₁, ∑ k, ∑ l,
        X (i₂, k) (i₁, l) * Y (i₂, l) (i₁, k) := by
          rw [Finset.sum_comm]
    _ = ∑ i₂, ∑ k, ∑ i₁, ∑ l,
        X (i₂, k) (i₁, l) * Y (i₂, l) (i₁, k) := by
          apply Finset.sum_congr rfl
          intro i₂ _
          rw [Finset.sum_comm]
    _ = _ := rfl

/-- First-factor partial transpose is self-adjoint for the real trace pairing
`(X,Y) ↦ Re tr(XY)`. -/
@[simp]
theorem trace_partialTransposeLeft_mul_re
    (X Y : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    (partialTransposeLeft X * Y).trace.re =
      (X * partialTransposeLeft Y).trace.re := by
  rw [trace_partialTransposeLeft_mul]

/-- Every positive semidefinite bipartite matrix has Schmidt number at most
the dimension of its first tensor factor. -/
theorem PosSemidef.hasSchmidtNumberLE_left
    {X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hX : X.PosSemidef) : HasSchmidtNumberLE d X := by
  obtain ⟨m, u, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hX
  refine ⟨Fin m, inferInstance, u, ?_, rfl⟩
  intro i
  simpa [HasSchmidtRankLE] using schmidtRank_le_left (u i)

/-- Positive semidefinite trace-one matrices on a rectangular bipartite index
space form a compact set. This is the full Schmidt-number section
`S_d`, since every vector has Schmidt rank at most `d`. -/
theorem isCompact_setOf_posSemidef_trace_one :
    IsCompact
      {X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
        X.PosSemidef ∧ X.trace = 1} := by
  have heq :
      {X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
          X.PosSemidef ∧ X.trace = 1} =
        {X : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
          HasSchmidtNumberLE d X ∧ X.trace = 1} := by
    ext X
    constructor
    · intro h
      exact ⟨h.1.hasSchmidtNumberLE_left, h.2⟩
    · intro h
      exact ⟨h.1.posSemidef, h.2⟩
  rw [heq]
  exact isCompact_setOf_hasSchmidtNumberLE_trace_one d

/-- A normalized decomposable witness in the form used by
Lewenstein--Kraus--Cirac--Horodecki, Theorem 3:

`W = a P₁ + (1-a) P₂^{T₁}`,

where `0 ≤ a ≤ 1` and `P₁,P₂` are positive semidefinite matrices of
trace one. The partial transpose is on Wolf's first tensor factor. -/
def IsNormalizedDecomposableWitness
    (W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) : Prop :=
  ∃ a : ℝ, ∃ P₁ P₂ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ,
    a ∈ Set.Icc 0 1 ∧ P₁.PosSemidef ∧ P₁.trace = 1 ∧
      P₂.PosSemidef ∧ P₂.trace = 1 ∧
        W = (a : ℂ) • P₁ + ((1 - a : ℝ) : ℂ) • partialTransposeLeft P₂

/-- The normalized decomposable witnesses form a compact set. It is the
continuous image of `[0,1] × D × D`, where `D` is the compact set of
positive semidefinite trace-one matrices. -/
theorem isCompact_setOf_isNormalizedDecomposableWitness :
    IsCompact
      {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
        IsNormalizedDecomposableWitness W} := by
  let D : Set (Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :=
    {P | P.PosSemidef ∧ P.trace = 1}
  let K := (Set.Icc (0 : ℝ) 1 ×ˢ D) ×ˢ D
  let f : ((ℝ × Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) ×
      Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) →
        Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ :=
    fun z ↦ (z.1.1 : ℂ) • z.1.2 + ((1 - z.1.1 : ℝ) : ℂ) •
      partialTransposeLeft z.2
  have hD : IsCompact D := by
    simpa only [D] using
      (isCompact_setOf_posSemidef_trace_one (d := d) (d' := d'))
  have hK : IsCompact K := (isCompact_Icc.prod hD).prod hD
  have hf : Continuous f := by
    dsimp only [f]
    apply Continuous.add
    · fun_prop
    · have hpt : Continuous (fun z : ((ℝ ×
          Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) ×
            Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) ↦
          partialTransposeLeft z.2) :=
        continuous_partialTransposeLeft.comp continuous_snd
      have hc : Continuous (fun z : ((ℝ ×
          Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) ×
            Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) ↦
          ((1 - z.1.1 : ℝ) : ℂ)) := by
        fun_prop
      exact hc.smul hpt
  have hEq :
      {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
          IsNormalizedDecomposableWitness W} = f '' K := by
    ext W
    constructor
    · rintro ⟨a, P₁, P₂, ha, hP₁, hP₁tr, hP₂, hP₂tr, rfl⟩
      refine ⟨((a, P₁), P₂), ?_, ?_⟩
      · exact ⟨⟨ha, hP₁, hP₁tr⟩, hP₂, hP₂tr⟩
      · rfl
    · rintro ⟨⟨⟨a, P₁⟩, P₂⟩, ⟨⟨ha, hP₁, hP₁tr⟩, hP₂, hP₂tr⟩, rfl⟩
      exact ⟨a, P₁, P₂, ha, hP₁, hP₁tr, hP₂, hP₂tr, rfl⟩
  rw [hEq]
  exact hK.image hf

/-- On nonzero tensor factors, the normalized formula is exactly the trace-one
section of Wolf's explicit decomposable-witness cone. The zero-trace summands
are normalized by the uniform density matrix, as their original summands then
vanish. -/
theorem isNormalizedDecomposableWitness_iff
    [NeZero d] [NeZero d']
    (W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    IsNormalizedDecomposableWitness W ↔
      IsDecomposableWitness W ∧ W.trace = 1 := by
  constructor
  · rintro ⟨a, P₁, P₂, ha, hP₁, hP₁tr, hP₂, hP₂tr, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨(a : ℂ) • P₁, ((1 - a : ℝ) : ℂ) • P₂, ?_, ?_, ?_⟩
      · exact hP₁.smul (by exact_mod_cast ha.1)
      · exact hP₂.smul (by exact_mod_cast sub_nonneg.mpr ha.2)
      · rw [partialTransposeLeft_smul]
    · rw [trace_add, trace_smul, trace_smul, trace_partialTransposeLeft,
        hP₁tr, hP₂tr]
      simp only [smul_eq_mul]
      push_cast
      ring
  · rintro ⟨⟨P₁, P₂, hP₁, hP₂, hW⟩, hWtr⟩
    let x₀ : Fin d × Fin d' := (0, 0)
    have hsum : P₁.trace.re + P₂.trace.re = 1 := by
      have h := congrArg Complex.re hWtr
      rw [hW, trace_add, trace_partialTransposeLeft] at h
      simpa using h
    refine ⟨P₁.trace.re, normalizePosSemidef x₀ P₁,
      normalizePosSemidef x₀ P₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · exact (Complex.nonneg_iff.mp hP₁.trace_nonneg).1
      · have hP₂trace_nonneg := (Complex.nonneg_iff.mp hP₂.trace_nonneg).1
        linarith
    · exact normalizePosSemidef_posSemidef x₀ hP₁
    · exact normalizePosSemidef_trace x₀ hP₁
    · exact normalizePosSemidef_posSemidef x₀ hP₂
    · exact normalizePosSemidef_trace x₀ hP₂
    · calc
        W = P₁ + partialTransposeLeft P₂ := hW
        _ = (P₁.trace.re : ℂ) • normalizePosSemidef x₀ P₁ +
            partialTransposeLeft
              ((P₂.trace.re : ℂ) • normalizePosSemidef x₀ P₂) := by
                rw [trace_re_smul_normalizePosSemidef x₀ hP₁,
                  trace_re_smul_normalizePosSemidef x₀ hP₂]
        _ = (P₁.trace.re : ℂ) • normalizePosSemidef x₀ P₁ +
            ((1 - P₁.trace.re : ℝ) : ℂ) •
              partialTransposeLeft (normalizePosSemidef x₀ P₂) := by
                rw [partialTransposeLeft_smul]
                have hb : P₂.trace.re = 1 - P₁.trace.re := by linarith
                rw [hb]

/-- The normalized decomposable witnesses form a convex set. Equivalently,
they are the trace-one section of the convex Equation-(3.15) cone. -/
theorem convex_setOf_isNormalizedDecomposableWitness
    [NeZero d] [NeZero d'] :
    Convex ℝ
      {W : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ |
        IsNormalizedDecomposableWitness W} := by
  intro X hX Y hY a b ha hb hab
  have hX' := (isNormalizedDecomposableWitness_iff X).mp hX
  have hY' := (isNormalizedDecomposableWitness_iff Y).mp hY
  apply (isNormalizedDecomposableWitness_iff _).mpr
  constructor
  · exact convex_setOf_isDecomposableWitness hX'.1 hY'.1 ha hb hab
  · have htraceX : (a • X).trace = a • X.trace := Matrix.trace_smul a X
    have htraceY : (b • Y).trace = b • Y.trace := Matrix.trace_smul b Y
    rw [trace_add, htraceX, htraceY, hX'.2, hY'.2]
    simpa [smul_eq_mul] using congrArg (fun t : ℝ ↦ (t : ℂ)) hab

/-- Matrix transposition is self-adjoint for the bilinear trace pairing. -/
@[simp]
theorem traceAdjointMap_transposeLinearMapComplex
    (n : Type*) [Fintype n] :
    traceAdjointMap (transposeLinearMapComplex n) = transposeLinearMapComplex n := by
  classical
  apply LinearMap.ext
  intro X
  ext i j
  rw [traceAdjointMap_apply_apply]
  simpa [transposeLinearMapComplex] using Matrix.trace_mul_single X i j (1 : ℂ)

end Matrix

namespace ChoiRectangular

variable {d d' : ℕ}

/-- Postcomposing a rectangular map with transposition transposes the output
factor of its Choi matrix. The Choi matrix is indexed output-first, so this is
`partialTransposeLeft`, not the input-factor partial transpose.

This is the orientation used for the trace-adjoint map--witness bridge around
Wolf, Chapter 3, Equation (3.15). -/
@[simp]
theorem choiMatrix_transposeLinearMapComplex_comp
    (P : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    choiMatrix ((Matrix.transposeLinearMapComplex (Fin d')).comp P) =
      Matrix.partialTransposeLeft (choiMatrix P) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [choiMatrix_apply, LinearMap.comp_apply, Matrix.transposeLinearMapComplex,
    Matrix.partialTransposeLeft_apply]

/-- **Decomposable-map/decomposable-witness correspondence** (Wolf Chapter 3,
Equations (3.13) and (3.15)). A rectangular map `T : M_d(ℂ) → M_{d'}(ℂ)`
is decomposable exactly when the output-first Choi matrix of its trace adjoint
`T* : M_{d'}(ℂ) → M_d(ℂ)` belongs to the explicit cone
`P₁ + P₂^{T₁}`, `P₁, P₂ ≥ 0`.

Only the witness-side input dimension `d'` must be nonzero, as required for
injectivity and positive surjectivity of the normalized rectangular Choi
assignment. -/
theorem isDecomposablePositiveMap_iff_choiMatrix_traceAdjointMap_isDecomposableWitness
    [NeZero d']
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    IsDecomposablePositiveMap T ↔
      Matrix.IsDecomposableWitness (choiMatrix (Matrix.traceAdjointMap T)) := by
  constructor
  · rintro ⟨T₁, Tccp, hT₁, hTccp, hT⟩
    have hT₂ :
        IsKrausCP (Tccp.comp (Matrix.transposeLinearMapComplex (Fin d))) := hTccp
    refine ⟨choiMatrix (Matrix.traceAdjointMap T₁),
      choiMatrix (Matrix.traceAdjointMap
        (Tccp.comp (Matrix.transposeLinearMapComplex (Fin d)))),
      (isKrausCP_iff_choiMatrix_posSemidef _).mp hT₁.traceAdjointMap,
      (isKrausCP_iff_choiMatrix_posSemidef _).mp hT₂.traceAdjointMap, ?_⟩
    have hccpAdj :
        Matrix.traceAdjointMap Tccp =
          (Matrix.transposeLinearMapComplex (Fin d)).comp
            (Matrix.traceAdjointMap
              (Tccp.comp (Matrix.transposeLinearMapComplex (Fin d)))) := by
      rw [Matrix.traceAdjointMap_comp,
        Matrix.traceAdjointMap_transposeLinearMapComplex]
      ext X i j
      simp [LinearMap.comp_apply, Matrix.transposeLinearMapComplex]
    calc
      choiMatrix (Matrix.traceAdjointMap T)
          = choiMatrix (Matrix.traceAdjointMap T₁) +
              choiMatrix (Matrix.traceAdjointMap Tccp) := by
                rw [hT, Matrix.traceAdjointMap_add, choiMatrix_add]
      _ = choiMatrix (Matrix.traceAdjointMap T₁) +
            Matrix.partialTransposeLeft
              (choiMatrix (Matrix.traceAdjointMap
                (Tccp.comp (Matrix.transposeLinearMapComplex (Fin d))))) := by
              rw [hccpAdj, choiMatrix_transposeLinearMapComplex_comp]
  · rintro ⟨P₁, P₂, hP₁, hP₂, hW⟩
    obtain ⟨Q₁, hQ₁, hQ₁choi⟩ :=
      exists_isKrausCP_of_posSemidef (d := d') (d' := d) hP₁
    obtain ⟨Q₂, hQ₂, hQ₂choi⟩ :=
      exists_isKrausCP_of_posSemidef (d := d') (d' := d) hP₂
    have hadjChoi :
        choiMatrix (Matrix.traceAdjointMap T) =
          choiMatrix (Q₁ + (Matrix.transposeLinearMapComplex (Fin d)).comp Q₂) := by
      calc
        choiMatrix (Matrix.traceAdjointMap T)
            = P₁ + Matrix.partialTransposeLeft P₂ := hW
        _ = choiMatrix Q₁ + Matrix.partialTransposeLeft (choiMatrix Q₂) := by
              rw [hQ₁choi, hQ₂choi]
        _ = choiMatrix
              (Q₁ + (Matrix.transposeLinearMapComplex (Fin d)).comp Q₂) := by
              rw [choiMatrix_add, choiMatrix_transposeLinearMapComplex_comp]
    have hadj : Matrix.traceAdjointMap T =
        Q₁ + (Matrix.transposeLinearMapComplex (Fin d)).comp Q₂ :=
      eq_of_choiMatrix_eq hadjChoi
    refine ⟨Matrix.traceAdjointMap Q₁,
      (Matrix.traceAdjointMap Q₂).comp (Matrix.transposeLinearMapComplex (Fin d)),
      hQ₁.traceAdjointMap, ?_, ?_⟩
    · rw [IsCompletelyCopositiveMap]
      have hcomp :
          ((Matrix.traceAdjointMap Q₂).comp (Matrix.transposeLinearMapComplex (Fin d))).comp
              (Matrix.transposeLinearMapComplex (Fin d)) =
            Matrix.traceAdjointMap Q₂ := by
        ext X i j
        simp [LinearMap.comp_apply, Matrix.transposeLinearMapComplex]
      rw [hcomp]
      exact hQ₂.traceAdjointMap
    · have hback := congrArg (fun S ↦ Matrix.traceAdjointMap S) hadj
      simpa [Matrix.traceAdjointMap_traceAdjointMap, Matrix.traceAdjointMap_comp] using hback

end ChoiRectangular
