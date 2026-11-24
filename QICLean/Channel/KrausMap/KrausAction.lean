/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Matrix.MatrixAux

/-!
# The action of a finite Kraus family

For a finite family of matrices `K : ι → Matrix n n ℂ` this file defines the Kraus map
$X \mapsto \sum_i K_i X K_i^\dagger$, its adjoint $X \mapsto \sum_i K_i^\dagger X K_i$, their
linear-map versions, and the unitality and trace-preservation conditions on the family.

## Main declarations

* `Kraus.map`, `Kraus.mapLM`: the Kraus map of a family.
* `Kraus.adjointMap`, `Kraus.adjointMapLM`: its adjoint for the trace pairing.
* `Kraus.IsUnital`, `Kraus.IsTP`: the conditions `∑ᵢ Kᵢ Kᵢ† = 1` and `∑ᵢ Kᵢ† Kᵢ = 1`.
* `Kraus.trace_mul_map_eq_trace_adjointMap_mul`: `tr(ρ · E(X)) = tr(E†(ρ) · X)`.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace Kraus

open Matrix Finset Complex

variable {ι n : Type*}
variable [Fintype ι]
variable [Fintype n] [DecidableEq n]

/-- Apply a Kraus map: `map K X = ∑ᵢ Kᵢ X Kᵢ†`. -/
noncomputable def map (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i : ι, K i * X * (K i)ᴴ

omit [DecidableEq n] in
lemma map_apply (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    map K X = ∑ i : ι, K i * X * (K i)ᴴ := rfl

/-- The Kraus map as a `ℂ`-linear map: `mapLM K X = ∑ᵢ Kᵢ X Kᵢ†`. -/
noncomputable def mapLM (K : ι → Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := map K
  map_add' X Y := by simp [map, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by simp [map, Finset.smul_sum]

@[simp] lemma mapLM_apply (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    mapLM K X = map K X := rfl

/-- Apply the adjoint Kraus map: `adjointMap K X = ∑ᵢ Kᵢ† X Kᵢ`. -/
noncomputable def adjointMap (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i : ι, (K i)ᴴ * X * K i

omit [DecidableEq n] in
lemma adjointMap_apply (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    adjointMap K X = ∑ i : ι, (K i)ᴴ * X * K i := rfl

omit [DecidableEq n] in
/-- The adjoint Kraus map of the conjugate-transposed family is the Kraus map of the
original family. -/
@[simp] theorem adjointMap_conjTranspose_eq_map (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    adjointMap (fun i => (K i)ᴴ) X = map K X := by
  simp [adjointMap, map, Matrix.conjTranspose_conjTranspose]

/-- The adjoint Kraus map as a `ℂ`-linear map: `adjointMapLM K X = ∑ᵢ Kᵢ† X Kᵢ`. -/
noncomputable def adjointMapLM (K : ι → Matrix n n ℂ) : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := adjointMap K
  map_add' X Y := by simp [adjointMap, add_mul, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by simp [adjointMap, Finset.smul_sum, Matrix.mul_assoc]

@[simp] lemma adjointMapLM_apply (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    adjointMapLM K X = adjointMap K X := rfl

/-- Unitality: `∑ᵢ Kᵢ Kᵢ† = I`. -/
def IsUnital (K : ι → Matrix n n ℂ) : Prop :=
  ∑ i : ι, K i * (K i)ᴴ = 1

omit [Fintype n] in
/-- Trace-preserving condition: `∑ᵢ Kᵢ† Kᵢ = I`, for a finite family of matrices
`Kᵢ : ℂ^n → ℂ^m`. This is the one notion of trace preservation of a Kraus family: the bundled
`KrausFamily.IsTP` is this condition on the operators of the family. Wolf, *Quantum Channels &
Operations*, Thm. 2.1. -/
def IsTP {m : Type*} [Fintype m] (K : ι → Matrix m n ℂ) : Prop :=
  ∑ i : ι, (K i)ᴴ * K i = 1

@[simp]
theorem map_one_of_isUnital (K : ι → Matrix n n ℂ) (h : IsUnital K) :
    map K (1 : Matrix n n ℂ) = 1 := by
  -- Reduce directly to unitality.
  simpa [map, IsUnital, Matrix.mul_one] using h

omit [DecidableEq n] in
/-- Conjugate-transpose commutes with a Kraus map. -/
theorem map_conjTranspose (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) : (map K X)ᴴ = map K Xᴴ := by
  classical
  simp [map, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Scalar-linearity of a Kraus map. -/
theorem map_smul (K : ι → Matrix n n ℂ) (c : ℂ) (X : Matrix n n ℂ) :
    map K (c • X) = c • map K X := by
  classical
  simp [map, Finset.smul_sum]

omit [DecidableEq n] in
/-- **Weighted trace / adjointness identity** for Kraus maps:

`tr(ρ · E(X)) = tr(E†(ρ) · X)`. -/
theorem trace_mul_map_eq_trace_adjointMap_mul
    (K : ι → Matrix n n ℂ) (ρ X : Matrix n n ℂ) :
    Matrix.trace (ρ * map K X) = Matrix.trace (adjointMap K ρ * X) := by
  classical
  -- Expand both sides to a sum over the Kraus index and use cyclicity termwise.
  simp only [map, adjointMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum, Matrix.mul_assoc]
  refine Finset.sum_congr rfl ?_
  intro i _
  calc
    Matrix.trace (ρ * (K i * (X * (K i)ᴴ)))
        = Matrix.trace ((ρ * K i) * X * (K i)ᴴ) := by
            simp [Matrix.mul_assoc]
    _ = Matrix.trace ((K i)ᴴ * (ρ * K i) * X) := by
            simpa using (Matrix.trace_mul_cycle (ρ * K i) X (K i)ᴴ)
    _ = Matrix.trace ((K i)ᴴ * (ρ * (K i * X))) := by
            simp [Matrix.mul_assoc]

attribute [simp] map_apply adjointMap_apply

end Kraus
