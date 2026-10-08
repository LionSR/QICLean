/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaDefect
import QICLean.Representation.TensorPowerAction
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Copy symmetry of the physical replica count and its spectral cutoff

The sum of identical one-copy operators commutes with every permutation of
physical copies. Consequently every real function of the actual replica
excitation count, including its closed spectral cutoff, commutes with the
physical copy permutations. Tensoring this function with the auxiliary
identity preserves simultaneous physical and auxiliary copy symmetries and
fixed auxiliary sectors.

These are the compatibility assertions in the OpenAI area-law manuscript,
`07-comparators.tex`, lines 421–443, `comparator:defect-mass`.
Literal tensor powers of a one-copy operator are also permutation invariant,
as used for the independent-copy density in `07-comparators.tex`,
lines 255–263, `comparator:high-label`.
No normalization of the one-copy vector is needed for commutation. The
Hamiltonian gap estimate, mass bound, ground-factor decomposition and
inverse-metric estimates, independent-copy concentration and entropy-window
selection are separate statements.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

/-
Original copy-permutation commutation and cutoff compatibility supporting OpenAI,
A two-dimensional area law from a global spectral gap, September 24, 2026.
07-comparators.tex lines 421–443, comparator:defect-mass; lines 255–263,
comparator:high-label, for literal tensor-power invariance.
Independently formalized; no upstream Lean proof text reused.
-/

open Matrix PermutationRepresentation TensorPower
open scoped Matrix Kronecker

namespace Matrix

variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem replicaHamiltonian_copyPerm_apply (H : Matrix A A ℂ) (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (x y : Fin k → A) :
    replicaHamiltonian H k (copyPerm A k σ x) (copyPerm A k σ y) =
      replicaHamiltonian H k x y := by
  classical
  simp only [replicaHamiltonian, Matrix.sum_apply, finKronecker_apply, copyPerm_apply]
  refine Fintype.sum_equiv σ.symm _ _ fun i => ?_
  refine Fintype.prod_equiv σ.symm _ _ fun j => ?_
  simp only [σ.symm.injective.eq_iff, Equiv.Perm.inv_def]

private theorem commute_copyPerm_of_invariant_entries {k : ℕ}
    (K : Matrix (Fin k → A) (Fin k → A) ℂ) (σ : Equiv.Perm (Fin k))
    (hK : ∀ x y, K (copyPerm A k σ x) (copyPerm A k σ y) = K x y) :
    Commute K (permOp (copyPerm A k) σ) := by
  classical
  change K * (copyPerm A k σ)⁻¹.permMatrix ℂ =
    (copyPerm A k σ)⁻¹.permMatrix ℂ * K
  simp only [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  ext x y
  change K x (copyPerm A k σ y) = K ((copyPerm A k σ)⁻¹ x) y
  simpa only [Equiv.apply_symm_apply, Equiv.Perm.inv_def] using
    hK ((copyPerm A k σ).symm x) y

/-- The actual sum of identical one-copy operators commutes with every physical
copy permutation. OpenAI area-law manuscript, `07-comparators.tex`,
lines 421–443, `comparator:defect-mass`. -/
theorem commute_replicaHamiltonian_permOp (H : Matrix A A ℂ) (k : ℕ)
    (σ : Equiv.Perm (Fin k)) :
    Commute (replicaHamiltonian H k) (permOp (copyPerm A k) σ) :=
  commute_copyPerm_of_invariant_entries _ σ (replicaHamiltonian_copyPerm_apply H k σ)

/-- A literal tensor power of any one-copy operator commutes with every copy
permutation. In particular, an actual independent-copy density has this
invariance without an additional hypothesis. OpenAI area-law manuscript,
`07-comparators.tex`, lines 255–263, `comparator:high-label`. -/
theorem commute_finKronecker_const_permOp (H : Matrix A A ℂ) (k : ℕ)
    (σ : Equiv.Perm (Fin k)) :
    Commute (finKronecker (fun _ : Fin k => H)) (permOp (copyPerm A k) σ) := by
  apply commute_copyPerm_of_invariant_entries _ σ
  intro x y
  simp only [finKronecker_apply, copyPerm_apply]
  refine Fintype.prod_equiv σ.symm _ _ fun j => ?_
  rfl

/-- Every real function of the actual physical excitation count commutes with
copy permutations. The closed cutoff is obtained by choosing the threshold
indicator. OpenAI area-law manuscript, `07-comparators.tex`, lines 421–443,
`comparator:defect-mass`. -/
theorem commute_cfc_replicaDefectCount_permOp (Ω : A → ℂ) (k : ℕ)
    (f : ℝ → ℝ) (σ : Equiv.Perm (Fin k)) :
    Commute (cfc f (replicaDefectCount Ω k)) (permOp (copyPerm A k) σ) := by
  exact (commute_replicaHamiltonian_permOp (1 - vecMulVec Ω (star Ω)) k σ).cfc_real f

/-- A physical function of the actual excitation count commutes with the
literal product of a physical copy permutation and any auxiliary operator.
Taking the auxiliary operator to be its copy action gives simultaneous copy
symmetry; taking the physical permutation to be the identity gives auxiliary
sector compatibility. OpenAI area-law manuscript, `07-comparators.tex`,
lines 421–443, `comparator:defect-mass`. -/
theorem commute_cfc_replicaDefectCount_kronecker {C : Type*}
    [Fintype C] [DecidableEq C] (Ω : A → ℂ) (k : ℕ) (f : ℝ → ℝ)
    (σ : Equiv.Perm (Fin k)) (M : Matrix C C ℂ) :
    Commute (cfc f (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ))
      (permOp (copyPerm A k) σ ⊗ₖ M) := by
  change (cfc f (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ)) *
      (permOp (copyPerm A k) σ ⊗ₖ M) =
    (permOp (copyPerm A k) σ ⊗ₖ M) *
      (cfc f (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ))
  simp only [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    (commute_cfc_replicaDefectCount_permOp Ω k f σ).eq]

/-- Applying a physical function of the actual excitation count preserves a
vector fixed by a simultaneous physical and auxiliary copy action. For the
identity physical permutation it also preserves each fixed auxiliary Schur
sector, by taking the auxiliary operator to be the actual label projector.
OpenAI area-law manuscript, `07-comparators.tex`, lines 421–443,
`comparator:defect-mass`. -/
theorem cfc_replicaDefectCount_kronecker_mulVec_preserves_fixed {C : Type*}
    [Fintype C] [DecidableEq C] (Ω : A → ℂ) (k : ℕ) (f : ℝ → ℝ)
    (σ : Equiv.Perm (Fin k)) (M : Matrix C C ℂ)
    (v : (Fin k → A) × C → ℂ) (hv : (permOp (copyPerm A k) σ ⊗ₖ M) *ᵥ v = v) :
    (permOp (copyPerm A k) σ ⊗ₖ M) *ᵥ
        ((cfc f (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ v) =
      (cfc f (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ v := by
  rw [mulVec_mulVec, ← (commute_cfc_replicaDefectCount_kronecker Ω k f σ M).eq,
    ← mulVec_mulVec, hv]

end Matrix
