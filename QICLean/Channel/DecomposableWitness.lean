/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.ChoiRectangular
import QICLean.Channel.KrausCPTP
import QICLean.Channel.PartialTranspose

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
* `Matrix.traceAdjointMap_transposeLinearMapComplex` -- transposition is
  self-adjoint for the bilinear trace pairing.
* `ChoiRectangular.choiMatrix_transposeLinearMapComplex_comp` -- transposing
  a map's output transposes the output factor of its Choi matrix.
* `ChoiRectangular.isDecomposablePositiveMap_iff_choiMatrix_traceAdjointMap_isDecomposableWitness`
  -- the rectangular map--witness equivalence.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Equations (3.13) and (3.15)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder

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
