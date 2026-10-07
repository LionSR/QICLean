/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.MaximallyEntangled
import QICLean.Representation.LabelProjectors
import QICLean.Representation.TensorPowerAction
import QICLean.Algebra.MatrixAux

/-!
# Schur labels on the repeated uniform auxiliary pair

Projecting one half of the literal tensor power of the normalized maximally
entangled vector onto an orthogonal projector gives squared mass equal to its
trace divided by the auxiliary dimension. In positive one-copy dimension,
occurrence is nonzero exactly when the operator is nonzero. The actual central
Schur projectors act identically on the two halves.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 273–281, `comparator:high-label`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These statements establish initial positive occurrence and auxiliary-label
matching; the entropy-compatible label selection remains a separate result.
The initial occurrence need not have inverse polynomial probability.

Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex, lines 273–281.
Labels: comparator:high-label, comparator:prevector.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8753-qic-uniform-bell-label-01
Downstream declaration: Matrix.norm_sq_one_kronecker_mulVec_prod_omegaVec
Provenance-ID: 8753-qic-uniform-bell-label-02
Downstream declaration: Matrix.one_kronecker_mulVec_prod_omegaVec_ne_zero_iff
Provenance-ID: 8753-qic-uniform-bell-label-03
Downstream declaration: TensorPower.labelProj_kronecker_mulVec_prod_omegaVec
-/

open scoped BigOperators Matrix Kronecker
open Matrix
noncomputable section
namespace Matrix
private theorem prod_omegaVec_apply (d k : ℕ) (x y : Fin k → Fin d) :
    (∏ i, omegaVec d (x i, y i)) =
      if x = y then ((Real.sqrt (d : ℝ) : ℂ)⁻¹)^k else 0 := by
  classical
  by_cases h : x = y
  · subst y
    simp [omegaVec, one_div]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [omegaVec, hi])

private theorem projected_prod_omegaVec_apply (d k : ℕ)
    (P : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)
    (x : (Fin k → Fin d) × (Fin k → Fin d)) :
    (((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ
      (fun y : (Fin k → Fin d) × (Fin k → Fin d) ↦
        ∏ i, omegaVec d (y.1 i, y.2 i))) x =
      ((Real.sqrt (d : ℝ) : ℂ)⁻¹)^k * P x.2 x.1 := by
  classical
  simp [mulVec, dotProduct, kroneckerMap_apply, one_apply, prod_omegaVec_apply,
    Fintype.sum_prod_type, mul_ite, mul_comm]

private theorem trace_eq_norm_transpose {d k : ℕ} (P : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) :
    (Pᴴ * P).trace.re =
      ‖WithLp.toLp 2 (fun x : (Fin k → Fin d) × (Fin k → Fin d) ↦ P x.2 x.1)‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  exact congrArg Complex.re (star_vec_dotProduct_vec P P).symm

/-- The squared mass of an orthogonal projection of the actual repeated uniform
auxiliary pair is its trace divided by the full auxiliary dimension.
OpenAI area-law manuscript, `07-comparators.tex`, lines 273–281,
`comparator:high-label`. The formula also holds for an empty one-copy space. -/
theorem norm_sq_one_kronecker_mulVec_prod_omegaVec (d k : ℕ)
    (P : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) (hP : IsStarProjection P) :
    ‖WithLp.toLp 2 (((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) ↦ ∏ i, omegaVec d (x.1 i, x.2 i)))‖^2 =
        (P.trace.re) / (d : ℝ)^k := by
  have he : (((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) ↦ ∏ i, omegaVec d (x.1 i, x.2 i))) =
      ((Real.sqrt (d : ℝ) : ℂ)⁻¹)^k • (fun x ↦ P x.2 x.1) := by
    ext x
    exact projected_prod_omegaVec_apply d k P x
  rw [he, WithLp.toLp_smul, norm_smul, mul_pow, ← trace_eq_norm_transpose]
  have hp : Pᴴ * P = P := by
    rw [← star_eq_conjTranspose, hP.isSelfAdjoint.star_eq, hP.isIdempotentElem.eq]
  rw [hp]
  have hn : ‖((Real.sqrt (d : ℝ) : ℂ)⁻¹)^k‖^2 = ((d : ℝ)^k)⁻¹ := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), ← pow_mul, mul_comm k 2, pow_mul,
      inv_pow, Real.sq_sqrt (Nat.cast_nonneg d), ← inv_pow]
  rw [hn, div_eq_mul_inv, mul_comm]

/-- Every nonzero operator occurs nontrivially on one half of the actual
repeated uniform auxiliary pair in positive one-copy dimension.
OpenAI area-law manuscript, `07-comparators.tex`, lines 273–281,
`comparator:high-label`. No lower bound on the occurrence probability is assumed. -/
theorem one_kronecker_mulVec_prod_omegaVec_ne_zero_iff (d k : ℕ) (hd : 0 < d)
    (P : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) :
    WithLp.toLp 2 (((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) ↦ ∏ i, omegaVec d (x.1 i, x.2 i))) ≠ 0 ↔
        P ≠ 0 := by
  classical
  have hc : ((Real.sqrt (d : ℝ) : ℂ)⁻¹)^k ≠ 0 := by
    exact pow_ne_zero k (inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)).ne'))
  have hz : WithLp.toLp 2 (((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) ↦ ∏ i, omegaVec d (x.1 i, x.2 i))) = 0 ↔
        P = 0 := by
    constructor
    · intro h
      ext r c
      have he := congrArg (fun v : EuclideanSpace ℂ ((Fin k → Fin d) × (Fin k → Fin d)) ↦ v (c,r)) h
      simpa only [PiLp.zero_apply, projected_prod_omegaVec_apply,
        mul_eq_zero, hc, false_or, zero_apply] using he
    · intro h
      subst P
      simp
  exact not_congr hz

private theorem projected_prod_omegaVec_left_apply (d k : ℕ)
    (P : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)
    (x : (Fin k → Fin d) × (Fin k → Fin d)) :
    ((P ⊗ₖ (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) *ᵥ
      (fun y : (Fin k → Fin d) × (Fin k → Fin d) ↦
        ∏ i, omegaVec d (y.1 i, y.2 i))) x =
      ((Real.sqrt (d : ℝ) : ℂ)⁻¹)^k * P x.1 x.2 := by
  classical
  simp [mulVec, dotProduct, kroneckerMap_apply, one_apply, prod_omegaVec_apply,
    Fintype.sum_prod_type, mul_ite, mul_comm]
end Matrix
namespace PermutationRepresentation
private theorem transpose_labelProj_copyPerm (d k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (labelProj (TensorPower.copyPerm (Fin d) k) l)ᵀ =
      labelProj (TensorPower.copyPerm (Fin d) k) l := by
  classical
  simp only [labelProj, groupAlgebraRep_eq_sum, transpose_sum, transpose_smul,
    permOp_apply, Matrix.transpose_permMatrix]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin k))) _ _ (fun g ↦ ?_)
  simp only [Equiv.inv_apply, map_inv, inv_inv,
    IrrepLabel.coeff_inv_of_mem_center (IrrepLabel.centralIdem_mem_center l)]
end PermutationRepresentation

namespace TensorPower
open PermutationRepresentation
/-- The actual repeated uniform pair has matching central Schur labels on
its two auxiliary halves. OpenAI area-law manuscript, `07-comparators.tex`,
lines 273–281, and `05-replicas.tex`, lines 176–181. -/
theorem labelProj_kronecker_mulVec_prod_omegaVec (d k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (labelProj (copyPerm (Fin d) k) l ⊗ₖ
      (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) *ᵥ
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) ↦ ∏ i, omegaVec d (x.1 i, x.2 i)) =
    ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ
      labelProj (copyPerm (Fin d) k) l) *ᵥ
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) ↦ ∏ i, omegaVec d (x.1 i, x.2 i)) := by
  ext x
  rw [Matrix.projected_prod_omegaVec_left_apply, Matrix.projected_prod_omegaVec_apply]
  congr 1
  exact congrArg (fun M : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ ↦ M x.2 x.1)
    (PermutationRepresentation.transpose_labelProj_copyPerm d k l)
end TensorPower
