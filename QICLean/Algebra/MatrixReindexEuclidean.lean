/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenspaces and kernels under reindexing

A linear equivalence `f` with `T ∘ f = f ∘ S` carries each eigenspace of `S` onto the eigenspace
of `T` for the same eigenvalue (`Module.End.eigenspace_eq_map_of_intertwine`). Relabelling the
basis of a square matrix along `e` is such an intertwining: the isometry `ψ ↦ ψ ∘ e.symm` of
Euclidean spaces intertwines `H` with `reindex e e H`
(`Matrix.toEuclideanLin_reindex_piLpCongrLeft`). Hence the isometry carries the eigenspaces, the
kernel, and any norm gap on the orthogonal complement of the kernel of `H` to those of the
reindexed matrix. No positivity or Hermiticity hypothesis is needed.

The statements of `Matrix.toEuclideanLin_reindex_piLpCongrLeft`,
`Matrix.ker_toEuclideanLin_reindex_map` and `Matrix.norm_gap_toEuclideanLin_reindex` are those of
TNLean's `TNLean/Algebra/MatrixReindexGap.lean` (commit
`71c1185e9352a3b5237b37a6840640751da6ca2d`, Apache-2.0); the kernel and norm-gap proofs are
replaced by corollaries of the eigenspace transport.
-/

open scoped InnerProductSpace

/-- A linear equivalence `f` with `T ∘ f = f ∘ S` carries each eigenspace of `S` onto the
eigenspace of `T` for the same eigenvalue. -/
theorem Module.End.eigenspace_eq_map_of_intertwine {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] (f : E ≃ₗ[ℂ] F) (S : Module.End ℂ E) (T : Module.End ℂ F)
    (h : ∀ x, T (f x) = f (S x)) (μ : ℂ) :
    Module.End.eigenspace T μ = (Module.End.eigenspace S μ).map (f : E →ₗ[ℂ] F) := by
  ext y
  rw [Submodule.mem_map_equiv, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  conv_lhs => rw [← f.apply_symm_apply y, h, ← map_smul]
  exact f.injective.eq_iff

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The isometry `ψ ↦ ψ ∘ e.symm` induced by `e` intertwines `H` and `reindex e e H`. -/
theorem toEuclideanLin_reindex_piLpCongrLeft (e : ι ≃ κ) (H : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    toEuclideanLin (reindex e e H) (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e v) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (toEuclideanLin H v) := by
  apply WithLp.ofLp_injective 2
  ext i
  simp [toLpLin_apply, reindex_apply, submatrix_mulVec_equiv, Equiv.piCongrLeft'_apply,
    Function.comp_def]

/-- The eigenspaces of a relabelled matrix are the images of the eigenspaces. -/
theorem eigenspace_toEuclideanLin_reindex (e : ι ≃ κ) (H : Matrix ι ι ℂ) (μ : ℂ) :
    Module.End.eigenspace (toEuclideanLin (reindex e e H)) μ =
      (Module.End.eigenspace (toEuclideanLin H) μ).map
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearEquiv :
          EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ) :=
  Module.End.eigenspace_eq_map_of_intertwine _ _ _ (toEuclideanLin_reindex_piLpCongrLeft e H) μ

/-- Relabelling the basis conjugates the eigenspaces by the induced isometry
`ψ ↦ ψ ∘ e.symm` of Euclidean spaces. -/
theorem mem_eigenspace_toEuclideanLin_reindex_iff (e : ι ≃ κ) (H : Matrix ι ι ℂ) (μ : ℂ)
    (ψ : EuclideanSpace ℂ κ) :
    ψ ∈ Module.End.eigenspace (toEuclideanLin (reindex e e H)) μ ↔
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm ψ ∈
        Module.End.eigenspace (toEuclideanLin H) μ := by
  rw [eigenspace_toEuclideanLin_reindex, Submodule.mem_map_equiv]
  rfl

/-- A relabelled matrix has the same eigenvalues. -/
theorem hasEigenvalue_toEuclideanLin_reindex_iff (e : ι ≃ κ) (H : Matrix ι ι ℂ) (μ : ℂ) :
    Module.End.HasEigenvalue (toEuclideanLin (reindex e e H)) μ ↔
      Module.End.HasEigenvalue (toEuclideanLin H) μ := by
  rw [Module.End.hasEigenvalue_iff, Module.End.hasEigenvalue_iff,
    eigenspace_toEuclideanLin_reindex, Ne, Ne, Submodule.map_eq_bot_iff]

/-- The configuration isometry maps the kernel onto the kernel of the reindexed matrix. -/
theorem ker_toEuclideanLin_reindex_map (e : ι ≃ κ) (H : Matrix ι ι ℂ) :
    (LinearMap.ker (toEuclideanLin H)).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearEquiv.toLinearMap =
      LinearMap.ker (toEuclideanLin (reindex e e H)) := by
  simpa only [Module.End.eigenspace_zero] using (eigenspace_toEuclideanLin_reindex e H 0).symm

/-- Reindexing preserves a norm gap on the orthogonal complement of the kernel, with the same
constant. -/
theorem norm_gap_toEuclideanLin_reindex (e : ι ≃ κ) (H : Matrix ι ι ℂ) {γ : ℝ}
    (hGap : ∀ v ∈ (LinearMap.ker (toEuclideanLin H))ᗮ, γ * ‖v‖ ≤ ‖toEuclideanLin H v‖) :
    ∀ w ∈ (LinearMap.ker (toEuclideanLin (reindex e e H)))ᗮ,
      γ * ‖w‖ ≤ ‖toEuclideanLin (reindex e e H) w‖ := by
  set φ := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
  intro w hw
  rw [← ker_toEuclideanLin_reindex_map e H, ← Submodule.map_orthogonal_equiv,
    Submodule.mem_map_equiv] at hw
  have h := hGap (φ.symm w) hw
  rwa [φ.symm.norm_map, ← φ.norm_map (toEuclideanLin H (φ.symm w)),
    ← toEuclideanLin_reindex_piLpCongrLeft, φ.apply_symm_apply] at h

end Matrix
