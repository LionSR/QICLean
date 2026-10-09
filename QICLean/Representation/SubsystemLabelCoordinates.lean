/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.FiniteProduct
import QICLean.Entropy.PureTensorPower
import QICLean.Representation.SchurLabelCutoff
import QICLean.Representation.GroupAlgebraProductCoordinates
import QICLean.Representation.TensorPowerAction
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Regional copy permutations in split coordinates

Splitting each physical copy into a region and its complement identifies the
subsystem copy action with the ordinary copy action on the regional factor.
The complementary factor is placed first to agree with the existing
left-partial-trace formulas for pure tensor powers. Consequently the squared
failure norm of the actual subsystem label cutoff is exactly its trace mass
in the tensor power of the actual regional marginal. The one-copy vector need
not be normalized, and its density need not be invariant under regional copy
permutations. The regional marginal of a compressed selected state is a
separate identification.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 332–354,
  `comparator:rough-overlap`; copy actions are defined in `05-replicas.tex`,
  lines 14–27.

-/

open scoped BigOperators Matrix Kronecker
open Matrix PermutationRepresentation

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) (k : ℕ) (B : Finset F)

/-- Split each copy into its complementary and regional configurations, then
collect the copies of each factor. -/
def subsystemSplitEquiv : Config k ι ≃
    (Fin k → FiniteProduct.Configuration ι Bᶜ) ×
      (Fin k → FiniteProduct.Configuration ι B) :=
  (Equiv.piCongrRight fun _ : Fin k ↦
    (FiniteProduct.splitEquiv ι B).trans (Equiv.prodComm _ _)).trans
      (Equiv.arrowProdEquivProdArrow (Fin k)
        (fun _ ↦ FiniteProduct.Configuration ι Bᶜ)
        (fun _ ↦ FiniteProduct.Configuration ι B))

/-- The actual subsystem permutation fixes the complementary coordinates and
permutes precisely the regional copies after the canonical split. -/
theorem subsystemSplitEquiv_subsystemPerm (σ : Equiv.Perm (Fin k))
    (x : Config k ι) :
    subsystemSplitEquiv ι k B (subsystemPerm k ι B σ x) =
      ((subsystemSplitEquiv ι k B x).1,
        copyPerm (FiniteProduct.Configuration ι B) k σ
          (subsystemSplitEquiv ι k B x).2) := by
  apply Prod.ext
  · funext j f
    change (if (f : F) ∈ B then x (σ⁻¹ j) f else x j f) = x j f
    exact ite_eq_right (Finset.mem_compl.mp f.property)
  · funext j f
    change (if (f : F) ∈ B then x (σ⁻¹ j) f else x j f) = x (σ⁻¹ j) f
    exact ite_eq_left f.property

variable [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- Every central Schur projector on an actual subsystem is the regional
projector tensored with the identity, in the canonical split coordinates.
No invariance assumption on a state is involved. -/
theorem labelProj_subsystemPerm_submatrix (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (labelProj (subsystemPerm k ι B) l).submatrix
        (subsystemSplitEquiv ι k B).symm (subsystemSplitEquiv ι k B).symm =
      (1 : Matrix (Fin k → FiniteProduct.Configuration ι Bᶜ)
        (Fin k → FiniteProduct.Configuration ι Bᶜ) ℂ) ⊗ₖ
          labelProj (copyPerm (FiniteProduct.Configuration ι B) k) l := by
  exact groupAlgebraRep_submatrix_of_prod_action
    (subsystemPerm k ι B) (copyPerm (FiniteProduct.Configuration ι B) k)
    (subsystemSplitEquiv ι k B) (subsystemSplitEquiv_subsystemPerm ι k B)
    (IrrepLabel.centralIdem l)

/-- The closed Schur cutoff on a subsystem becomes the regional cutoff
tensored with the identity under the canonical coordinate split. -/
theorem labelCutoff_subsystemPerm_submatrix (a : ℝ) :
    (labelCutoff (subsystemPerm k ι B) a).submatrix
        (subsystemSplitEquiv ι k B).symm (subsystemSplitEquiv ι k B).symm =
      (1 : Matrix (Fin k → FiniteProduct.Configuration ι Bᶜ)
        (Fin k → FiniteProduct.Configuration ι Bᶜ) ℂ) ⊗ₖ
          labelCutoff (copyPerm (FiniteProduct.Configuration ι B) k) a := by
  classical
  ext x y
  simp only [labelCutoff, labelObservable, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have h := congrArg (fun M ↦ M x y) (labelProj_subsystemPerm_submatrix ι k B l)
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
  rw [h]
  ring

/-- The actual failure mass of a subsystem Schur cutoff on a pure tensor power
is its trace mass in the IID regional marginal. This is the regional
expectation identity in the retained-mass argument of the OpenAI area-law
manuscript, `07-comparators.tex`, lines 332–354.

The identity holds for zero copies, empty regions, singular marginals, and
unnormalized vectors. It does not assume regional permutation invariance of
the full pure state. -/
theorem norm_sq_one_sub_labelCutoff_subsystemPerm_prod
    (ψ : EuclideanSpace ℂ ((f : F) → ι f)) (a : ℝ) :
    ‖Matrix.toEuclideanLin (1 - labelCutoff (subsystemPerm k ι B) a)
      (WithLp.toLp 2 (fun x : Config k ι ↦ ∏ j, ψ (x j)))‖ ^ 2 =
        (Matrix.finKronecker (fun _ : Fin k ↦ FiniteProduct.reducedPure ι ψ B) *
          (1 - labelCutoff (copyPerm (FiniteProduct.Configuration ι B) k) a)).trace.re := by
  classical
  let C := FiniteProduct.Configuration ι Bᶜ
  let R := FiniteProduct.Configuration ι B
  let e := subsystemSplitEquiv ι k B
  let τ : C × R → ℂ := fun x ↦ ψ ((FiniteProduct.splitEquiv ι B).symm (x.2, x.1))
  let v : Config k ι → ℂ := fun x ↦ ∏ j, ψ (x j)
  let v' : (Fin k → C) × (Fin k → R) → ℂ := fun x ↦ ∏ j, τ (x.1 j, x.2 j)
  let M := 1 - labelCutoff (subsystemPerm k ι B) a
  let P := 1 - labelCutoff (copyPerm R k) a
  have hP : IsStarProjection P := by
    apply IsStarProjection.one_sub
    rw [labelCutoff_eq_spectralProjectionGE]
    exact (isHermitian_labelObservable (copyPerm R k)
      (fun l ↦ Real.log l.dim)).neg.isStarProjection_spectralProjectionGE (-a)
  have hv : v ∘ e.symm = v' := rfl
  have hρ : Matrix.partialTraceLeft (Matrix.vecMulVec τ (star τ)) =
      FiniteProduct.reducedPure ι ψ B := rfl
  have hM : M.submatrix e.symm e.symm =
      (1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ P := by
    change (1 - labelCutoff (subsystemPerm k ι B) a).submatrix e.symm e.symm = _
    simp only [Matrix.submatrix_sub, Pi.sub_apply]
    rw [Matrix.submatrix_one_equiv, labelCutoff_subsystemPerm_submatrix]
    change (1 : Matrix ((Fin k → C) × (Fin k → R))
      ((Fin k → C) × (Fin k → R)) ℂ) -
        (1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ labelCutoff (copyPerm R k) a = _
    rw [← Matrix.one_kronecker_one]
    ext x y
    simp only [P, Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring
  have hmul : ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ P) *ᵥ v' =
      (M *ᵥ v) ∘ e.symm := by
    calc
      _ = M.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) := by rw [hM, hv]
      _ = (M *ᵥ ((v ∘ e.symm) ∘ e)) ∘ e.symm :=
        Matrix.submatrix_mulVec_equiv M (v ∘ e.symm) e.symm e.symm
      _ = _ := by simp only [Function.comp_def, Equiv.symm_apply_apply]
  have hn : ‖WithLp.toLp 2 ((M *ᵥ v) ∘ e.symm)‖ =
      ‖WithLp.toLp 2 (M *ᵥ v)‖ :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map (WithLp.toLp 2 (M *ᵥ v))
  change ‖WithLp.toLp 2 (M *ᵥ v)‖ ^ 2 = _
  rw [← hn, ← hmul]
  simpa only [hρ] using Matrix.norm_sq_one_kronecker_mulVec_prod τ k P hP

end TensorPower
