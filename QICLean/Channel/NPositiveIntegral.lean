/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Schwarz.TwoPositive
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Closure properties of `k`-positive maps

A linear map is `k`-positive when its blockwise amplification by `k × k` matrices
preserves positive semidefiniteness, and completely positive in the sense of the
amplification definition when it is `k`-positive for every `k`. This file proves
that `k`-positivity is preserved by composition, contains every sandwich map
`X ↦ V X V*`, and is preserved by Bochner integration of continuous linear maps.

The last statement is the form needed for derivatives of matrix functions given by
integrals of sandwich maps, such as the Löwner integral for the derivative of a real
power.

## Main results

* `IsNPositiveMap.comp` — composition of `k`-positive maps is `k`-positive.
* `isNPositiveMap_singleKrausMap` — `X ↦ V X V*` is `k`-positive for every `k`.
* `IsNPositiveMap.integral` — an integral of almost everywhere `k`-positive continuous
  linear maps is `k`-positive.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- The composition of two `k`-positive maps is `k`-positive. -/
theorem IsNPositiveMap.comp {n' n'' : Type*} {E : Matrix n' n' ℂ →ₗ[ℂ] Matrix n'' n'' ℂ}
    {F : Matrix n n ℂ →ₗ[ℂ] Matrix n' n' ℂ} {k : ℕ}
    (hE : IsNPositiveMap k E) (hF : IsNPositiveMap k F) : IsNPositiveMap k (E ∘ₗ F) := by
  intro X hX
  exact hE _ (hF X hX)

omit [DecidableEq n] in
/-- A sandwich map `X ↦ V X V*` is `k`-positive for every `k`. -/
theorem isNPositiveMap_singleKrausMap (V : Matrix n n ℂ) (k : ℕ) :
    IsNPositiveMap k (singleKrausMap V) :=
  IsCPMap.isNPositiveMap ⟨1, fun _ ↦ V, fun X ↦ by simp [singleKrausMap]⟩ k

/-- An integral of almost everywhere `k`-positive continuous linear maps is `k`-positive. -/
theorem IsNPositiveMap.integral {n' : Type*} [Fintype n'] [DecidableEq n'] {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {F : α → Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ} (hF : Integrable F μ) {k : ℕ}
    (hpos : ∀ᵐ a ∂μ, IsNPositiveMap k (F a).toLinearMap) :
    IsNPositiveMap k (∫ a, F a ∂μ).toLinearMap := by
  intro X hX
  let ampEval : (Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ) →ₗ[ℂ]
      Matrix (n' × Fin k) (n' × Fin k) ℂ :=
    { toFun := fun E ↦ Matrix.of fun (ip : n' × Fin k) (jq : n' × Fin k) ↦
        E (Matrix.of fun i j ↦ X (i, ip.2) (j, jq.2)) ip.1 jq.1
      map_add' := fun E G ↦ by ext; simp
      map_smul' := fun c E ↦ by ext; simp }
  let ampEvalL : (Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ) →L[ℂ]
      Matrix (n' × Fin k) (n' × Fin k) ℂ :=
    ⟨ampEval, LinearMap.continuous_of_finiteDimensional _⟩
  have h0 := ContinuousLinearMap.integral_comp_comm
    (E := Matrix n n ℂ →L[ℂ] Matrix n' n' ℂ) (μ := μ) ampEvalL hF
  have h : ampEvalL (∫ a, F a ∂μ) = ∫ a, ampEvalL (F a) ∂μ := h0.symm
  change (ampEvalL (∫ a, F a ∂μ)).PosSemidef
  rw [h, ← Matrix.nonneg_iff_posSemidef]
  exact integral_nonneg_of_ae
    (hpos.mono fun a ha ↦ Matrix.nonneg_iff_posSemidef.mpr (ha X hX))
