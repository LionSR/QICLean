/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Contractions and tensor products of inner product spaces

Bookkeeping for compositions of contractions between tensor products of complex inner product
spaces: appending a fixed vector, the canonical reassociation and exchange isometries, and sums
under `lTensor` and `rTensor`.  The rescaling of an operator close to a contraction is in
`QICLean.Analysis.Norm.ApproximateContractionRescaling`.

Mathlib's `ContinuousLinearMap.lTensor` and `ContinuousLinearMap.rTensor` have `add`, `sub` and
`smul` lemmas but no finite-sum lemma; `ContinuousLinearMap.lTensor_finsetSum` and
`ContinuousLinearMap.rTensor_finsetSum` fill that gap.

## Main definitions

* `ContinuousLinearMap.appendRight`, `ContinuousLinearMap.appendLeft` : `x ↦ x ⊗ v`, `x ↦ v ⊗ x`.
* `ContinuousLinearMap.leftCommL` : `E ⊗ (F ⊗ G) → F ⊗ (E ⊗ G)`.
* `ContinuousLinearMap.assocL` : `(E ⊗ F) ⊗ G → E ⊗ (F ⊗ G)`.

## Main results

* `ContinuousLinearMap.norm_comp_le_one` : a composition of contractions is a contraction.
* `ContinuousLinearMap.lTensor_finsetSum`, `ContinuousLinearMap.rTensor_finsetSum`.

Moved from TNLean, `TNLean/Algebra/TensorProductContraction.lean` at commit
`49b78ed821` (Apache-2.0).
-/

noncomputable section

open scoped TensorProduct

namespace ContinuousLinearMap

/-- A composition of contractions is a contraction. -/
theorem norm_comp_le_one {E F G : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SeminormedAddCommGroup G] [NormedSpace ℂ G]
    {f : F →L[ℂ] G} {g : E →L[ℂ] F} (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) : ‖f ∘L g‖ ≤ 1 :=
  (opNorm_comp_le f g).trans <| by nlinarith [norm_nonneg f, norm_nonneg g]

/-- Composing with a contraction on the left does not increase the norm. -/
theorem norm_comp_le_of_norm_le_one {E F G : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SeminormedAddCommGroup G]
    [NormedSpace ℂ G] {f : F →L[ℂ] G} (g : E →L[ℂ] F) (hf : ‖f‖ ≤ 1) : ‖f ∘L g‖ ≤ ‖g‖ :=
  (opNorm_comp_le f g).trans (mul_le_of_le_one_left (norm_nonneg _) hf)

/-- Composition with a fixed map commutes with a weighted list sum. -/
theorem comp_listSum {E F G : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SeminormedAddCommGroup G] [NormedSpace ℂ G]
    (A : F →L[ℂ] G) (l : List (ℂ × (E →L[ℂ] F))) :
    A ∘L (l.map fun q => q.1 • q.2).sum = (l.map fun q => q.1 • (A ∘L q.2)).sum := by
  induction l with
  | nil => simp
  | cons q l ih => simp [comp_add, ih]

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Appending a fixed vector `v` on the right: `x ↦ x ⊗ v`. -/
def appendRight (v : F) : E →L[ℂ] E ⊗[ℂ] F :=
  (TensorProduct.mkL ℂ E F).flip v

/-- Appending a fixed vector `v` on the left: `x ↦ v ⊗ x`. -/
def appendLeft (v : F) : E →L[ℂ] F ⊗[ℂ] E :=
  TensorProduct.mkL ℂ F E v

@[simp]
theorem appendRight_apply (v : F) (x : E) : appendRight v x = x ⊗ₜ[ℂ] v := rfl

@[simp]
theorem appendLeft_apply (v : F) (x : E) : appendLeft (E := E) v x = v ⊗ₜ[ℂ] x := rfl

theorem norm_appendRight_le (v : F) : ‖appendRight (E := E) v‖ ≤ ‖v‖ :=
  opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [appendRight_apply, TensorProduct.norm_tmul, mul_comm]

theorem norm_appendLeft_le (v : F) : ‖appendLeft (E := E) v‖ ≤ ‖v‖ :=
  opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [appendLeft_apply, TensorProduct.norm_tmul]

theorem norm_appendRight_one_le : ‖appendRight (E := E) (1 : ℂ)‖ ≤ 1 :=
  (norm_appendRight_le _).trans norm_one.le

theorem lTensor_finsetSum {ι : Type*} (s : Finset ι) (f : ι → E →L[ℂ] F) :
    (∑ i ∈ s, f i).lTensor G = ∑ i ∈ s, (f i).lTensor G := by
  induction s using Finset.cons_induction <;> simp_all

theorem rTensor_finsetSum {ι : Type*} (s : Finset ι) (f : ι → E →L[ℂ] F) :
    (∑ i ∈ s, f i).rTensor G = ∑ i ∈ s, (f i).rTensor G := by
  induction s using Finset.cons_induction <;> simp_all

variable (E F G) in
/-- The isometry `E ⊗ (F ⊗ G) ≅ F ⊗ (E ⊗ G)` exchanging the first two factors. -/
def leftCommIso : E ⊗[ℂ] (F ⊗[ℂ] G) ≃ₗᵢ[ℂ] F ⊗[ℂ] (E ⊗[ℂ] G) :=
  (TensorProduct.assocIsometry ℂ E F G).symm.trans
    (((TensorProduct.commIsometry ℂ E F).rTensor G).trans (TensorProduct.assocIsometry ℂ F E G))

@[simp]
theorem leftCommIso_tmul (x : E) (y : F) (z : G) :
    leftCommIso E F G (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) = y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] z) := by
  simp [leftCommIso, LinearIsometryEquiv.rTensor]

variable (E F G) in
/-- `E ⊗ (F ⊗ G) → F ⊗ (E ⊗ G)` as a continuous linear map. -/
def leftCommL : E ⊗[ℂ] (F ⊗[ℂ] G) →L[ℂ] F ⊗[ℂ] (E ⊗[ℂ] G) :=
  (leftCommIso E F G).toLinearIsometry.toContinuousLinearMap

variable (E F G) in
/-- `(E ⊗ F) ⊗ G → E ⊗ (F ⊗ G)` as a continuous linear map. -/
def assocL : E ⊗[ℂ] F ⊗[ℂ] G →L[ℂ] E ⊗[ℂ] (F ⊗[ℂ] G) :=
  (TensorProduct.assocIsometry ℂ E F G).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem leftCommL_tmul (x : E) (y : F) (z : G) :
    leftCommL E F G (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) = y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] z) := by
  simp [leftCommL]

@[simp]
theorem assocL_tmul (x : E) (y : F) (z : G) :
    assocL E F G ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z) = x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z) := by
  simp [assocL]

theorem norm_leftCommL_le : ‖leftCommL E F G‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

theorem norm_assocL_le : ‖assocL E F G‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

end ContinuousLinearMap
