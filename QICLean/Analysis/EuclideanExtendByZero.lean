/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Embedding.Basic
import Mathlib.Tactic.Linarith
import QICLean.Analysis.EuclideanFiberwiseMap

/-!
# Euclidean extension by zero along a finite embedding

An embedding `e : I ↪ J` of finite coordinate sets induces a linear isometry
`ℓ²(I) → ℓ²(J)` by extension by zero; the norm identity is the finite sum identity along an
injection, with all coefficients outside its range zero. Extending an operator over a finite
spectator space commutes with these isometries whenever the operators intertwine them, including
for empty coordinate sets.

Moved from TNLean, `TNLean/Algebra/EuclideanExtendByZero.lean` and
`TNLean/MPS/ParentHamiltonian/Martingale/SpectatorPhysicalEmbedding.lean` at commit `49b78ed821`
(Apache-2.0). Changes: the two files are merged; docstrings rewritten.

## Main definitions

* `Function.Embedding.euclideanExtendByZero`

## Main results

* `Function.Embedding.norm_euclideanExtendByZero`
* `ContinuousLinearMap.rightFiberwiseMap_extendByZero`
-/

open scoped BigOperators

namespace Function.Embedding

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Extension by zero along an embedding of finite coordinate sets is a Euclidean isometry. -/
noncomputable def euclideanExtendByZero (e : I ↪ J) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ J where
  toLinearMap := LinearMap.withLpMap 2 (Function.ExtendByZero.linearMap ℂ ℂ e)
  norm_map' v := by
    classical
    have hsum := Fintype.sum_of_injective e e.injective
      (fun i ↦ ‖v i‖ ^ 2)
      (fun j ↦ ‖Function.extend e (fun i ↦ v i) 0 j‖ ^ 2)
      (fun j hj ↦ by
        rw [Function.extend_apply' _ _ j hj]
        simp)
      (fun i ↦ by rw [e.injective.extend_apply])
    have hsq : ‖LinearMap.withLpMap 2 (Function.ExtendByZero.linearMap ℂ ℂ e) v‖ ^ 2 =
        ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      exact hsum.symm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- Extension by zero preserves the Euclidean norm of every coefficient vector. -/
theorem norm_euclideanExtendByZero (e : I ↪ J) (v : EuclideanSpace ℂ I) :
    ‖e.euclideanExtendByZero v‖ = ‖v‖ :=
  e.euclideanExtendByZero.norm_map v

/-- The extended vector agrees with the original vector on the image of the embedding. -/
@[simp] theorem euclideanExtendByZero_apply_image (e : I ↪ J)
    (v : EuclideanSpace ℂ I) (i : I) :
    e.euclideanExtendByZero v (e i) = v i :=
  e.injective.extend_apply (fun i ↦ v i) 0 i

/-- The extended vector vanishes outside the image of the embedding. -/
theorem euclideanExtendByZero_apply_not_mem_range (e : I ↪ J)
    (v : EuclideanSpace ℂ I) (j : J) (hj : j ∉ Set.range e) :
    e.euclideanExtendByZero v j = 0 :=
  Function.extend_apply' (f := (e : I → J)) (fun i ↦ v i) 0 j hj

end Function.Embedding

namespace Function.Embedding

variable {I J S T : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype T]

private theorem rightFiber_extendByZero_image (e : I ↪ J) (g : S ↪ T)
    (v : EuclideanSpace ℂ (I × S)) (s : S) :
    ContinuousLinearMap.rightFiber ((e.prodMap g).euclideanExtendByZero v) (g s) =
      e.euclideanExtendByZero (ContinuousLinearMap.rightFiber v s) := by
  classical
  ext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    change (e.prodMap g).euclideanExtendByZero v ((e.prodMap g) (i, s)) = _
    rw [euclideanExtendByZero_apply_image, euclideanExtendByZero_apply_image]
    rfl
  · have hp : (j, g s) ∉ Set.range (e.prodMap g) := by
      rintro ⟨⟨i, t⟩, h⟩
      exact hj ⟨i, congrArg Prod.fst h⟩
    change (e.prodMap g).euclideanExtendByZero v (j, g s) =
      e.euclideanExtendByZero (ContinuousLinearMap.rightFiber v s) j
    rw [euclideanExtendByZero_apply_not_mem_range _ _ _ hp,
      euclideanExtendByZero_apply_not_mem_range _ _ _ hj]

private theorem rightFiber_extendByZero_not_mem_range (e : I ↪ J) (g : S ↪ T)
    (v : EuclideanSpace ℂ (I × S)) (t : T) (ht : t ∉ Set.range g) :
    ContinuousLinearMap.rightFiber ((e.prodMap g).euclideanExtendByZero v) t = 0 := by
  ext j
  have hp : (j, t) ∉ Set.range (e.prodMap g) := by
    rintro ⟨⟨i, s⟩, h⟩
    exact ht ⟨s, congrArg Prod.snd h⟩
  exact euclideanExtendByZero_apply_not_mem_range _ _ _ hp

end Function.Embedding

namespace ContinuousLinearMap

variable {I J S T : Type*} [Fintype I] [Fintype J] [Fintype S] [Fintype T]

/-- Fiberwise extension intertwines with Euclidean extension by zero
whenever the operators intertwine. Outside the spectator image both
fibers vanish; no nonempty-coordinate hypothesis is needed. -/
theorem rightFiberwiseMap_extendByZero (e : I ↪ J) (g : S ↪ T)
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (H : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J)
    (h : ∀ v, H (e.euclideanExtendByZero v) = e.euclideanExtendByZero (G v))
    (v : EuclideanSpace ℂ (I × S)) :
    ContinuousLinearMap.rightFiberwiseMap H ((e.prodMap g).euclideanExtendByZero v) =
      (e.prodMap g).euclideanExtendByZero (ContinuousLinearMap.rightFiberwiseMap G v) := by
  classical
  apply PiLp.ext
  rintro ⟨j, t⟩
  change H (ContinuousLinearMap.rightFiber ((e.prodMap g).euclideanExtendByZero v) t) j =
    ContinuousLinearMap.rightFiber ((e.prodMap g).euclideanExtendByZero
      (ContinuousLinearMap.rightFiberwiseMap G v)) t j
  by_cases ht : ∃ s, g s = t
  · obtain ⟨s, rfl⟩ := ht
    rw [Function.Embedding.rightFiber_extendByZero_image,
      Function.Embedding.rightFiber_extendByZero_image,
      ContinuousLinearMap.rightFiber_rightFiberwiseMap, h]
  · rw [Function.Embedding.rightFiber_extendByZero_not_mem_range _ _ _ _ ht,
      Function.Embedding.rightFiber_extendByZero_not_mem_range _ _ _ _ ht, map_zero]

end ContinuousLinearMap
