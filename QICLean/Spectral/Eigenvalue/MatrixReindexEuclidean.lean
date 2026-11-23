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
(`Matrix.toEuclideanLin_reindex_piLpCongrLeft`, the square case of
`Matrix.toEuclideanLin_reindex_piLpCongrLeft₂`). Hence the isometry carries the eigenspaces, the
eigenvalues and the kernel of `H` to those of the reindexed matrix. No positivity or Hermiticity
hypothesis is needed.

The statements of `Matrix.toEuclideanLin_reindex_piLpCongrLeft` and
`Matrix.ker_toEuclideanLin_reindex_map` are those of TNLean's
`TNLean/Algebra/MatrixReindexGap.lean` (commit `71c1185e9352a3b5237b37a6840640751da6ca2d`,
Apache-2.0); the kernel proof is replaced by a corollary of the eigenspace transport. A gap above
the kernel is carried in eigenvalue form by `Matrix.hasEigenvalue_toEuclideanLin_reindex_iff`.
-/

/-- A linear equivalence `f` with `T ∘ f = f ∘ S` carries each eigenspace of `S` onto the
eigenspace of `T` for the same eigenvalue. -/
theorem Module.End.eigenspace_eq_map_of_intertwine {R E F : Type*} [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F] (f : E ≃ₗ[R] F)
    (S : Module.End R E) (T : Module.End R F) (h : ∀ x, T (f x) = f (S x)) (μ : R) :
    Module.End.eigenspace T μ = (Module.End.eigenspace S μ).map (f : E →ₗ[R] F) := by
  ext y
  rw [Submodule.mem_map_equiv, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff]
  conv_lhs => rw [← f.apply_symm_apply y, h, ← map_smul]
  exact f.injective.eq_iff

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Reading a rectangular matrix along `e` on the rows and `f` on the columns, and a vector along
`f`, commutes with applying the matrix: the output is read along `e`. -/
theorem toEuclideanLin_reindex_piLpCongrLeft₂ {m n m' n' : Type*} [Fintype m] [Fintype n]
    [Fintype m'] [Fintype n'] [DecidableEq n] [DecidableEq n'] (e : m ≃ m') (f : n ≃ n')
    (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    toEuclideanLin (reindex e f M) (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ f x) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (toEuclideanLin M x) := by
  ext i
  simp only [Matrix.ofLp_toLpLin, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, reindex_apply]
  exact Fintype.sum_equiv f.symm _ _ fun j ↦ by simp

/-- The isometry `ψ ↦ ψ ∘ e.symm` induced by `e` intertwines `H` and `reindex e e H`. -/
theorem toEuclideanLin_reindex_piLpCongrLeft (e : ι ≃ κ) (H : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    toEuclideanLin (reindex e e H) (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e v) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e (toEuclideanLin H v) :=
  toEuclideanLin_reindex_piLpCongrLeft₂ e e H v

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

/-- The reindexing isometry `ψ ↦ ψ ∘ e.symm` maps the kernel onto the kernel of the reindexed
matrix. -/
theorem ker_toEuclideanLin_reindex_map (e : ι ≃ κ) (H : Matrix ι ι ℂ) :
    (LinearMap.ker (toEuclideanLin H)).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearEquiv.toLinearMap =
      LinearMap.ker (toEuclideanLin (reindex e e H)) := by
  simpa only [Module.End.eigenspace_zero] using (eigenspace_toEuclideanLin_reindex e H 0).symm

end Matrix
