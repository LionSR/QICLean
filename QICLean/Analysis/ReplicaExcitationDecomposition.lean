/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaDefect
import QICLean.Analysis.TraceCFC
import QICLean.Algebra.MatrixAux
import QICLean.Algebra.MatrixKroneckerEmbed

/-!
# Exact excitation sectors of physical replicas

The sector indexed by a subset of the copies has the ground-complement
projection on precisely those copies and the ground projection on the others.
These actual sectors determine the spectral cutoff of the excitation count.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 421–456, `comparator:defect-mass`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This module proves the exact orthogonal component decomposition and its squared
mass identity. Stabilizer invariance, ground-factor decomposition and the Schur
metric comparisons are separate steps of the source argument.

Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:defect-mass.
Provenance-ID: 8750-qic-replica-excitation-01
Downstream declaration:
Matrix.replicaExcitationProjection
Provenance-ID: 8750-qic-replica-excitation-02
Downstream declaration:
Matrix.isStarProjection_replicaExcitationProjection
Provenance-ID: 8750-qic-replica-excitation-03
Downstream declaration:
Matrix.sum_replicaExcitationProjection
Provenance-ID: 8750-qic-replica-excitation-04
Downstream declaration:
Matrix.replicaDefectCount_mul_replicaExcitationProjection
Provenance-ID: 8750-qic-replica-excitation-05
Downstream declaration:
Matrix.cfc_replicaDefectCount_eq_sum_replicaExcitationProjection
Provenance-ID: 8750-qic-replica-excitation-06
Downstream declaration:
Matrix.replicaExcitationProjection_mul_of_ne
Provenance-ID: 8750-qic-replica-excitation-07
Downstream declaration:
Matrix.replicaDefectCutoff_decomposition
-/

open scoped BigOperators Matrix Kronecker ComplexOrder

noncomputable section

namespace Matrix

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The actual projection onto the sector in which precisely `B` is excited.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 441–456. -/
def replicaExcitationProjection (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k)) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  finKronecker (fun j : Fin k ↦
    if j ∈ B then 1 - vecMulVec Ω (star Ω) else vecMulVec Ω (star Ω))

private theorem cfc_mul_of_mul_eq_smul {D R : Matrix A A ℂ}
    (hD : D.IsHermitian) (r : ℝ) (hR : D * R = (r : ℂ) • R) (f : ℝ → ℝ) :
    cfc f D * R = (f r : ℂ) • R := by
  rw [hD.cfc_eq, hD.cfc_form]
  have hR' := congrArg
    (fun M : Matrix A A ℂ ↦ star (hD.eigenvectorUnitary : Matrix A A ℂ) * M) hR
  conv at hR' => lhs; rhs; lhs; rw [hD.spectral_form]
  simp only [← mul_assoc, Unitary.coe_star_mul_self, one_mul, mul_smul_comm] at hR'
  have hf : diagonal (fun i ↦ (f (hD.eigenvalues i) : ℂ)) *
      (star (hD.eigenvectorUnitary : Matrix A A ℂ) * R) =
      (f r : ℂ) • (star (hD.eigenvectorUnitary : Matrix A A ℂ) * R) := by
    ext i j
    have hij := congrArg (fun M : Matrix A A ℂ ↦ M i j) hR'
    simp only [mul_assoc, diagonal_mul, smul_apply, smul_eq_mul] at hij ⊢
    rcases mul_eq_mul_right_iff.mp hij with heig | hzero
    · exact congrArg
        (fun x : ℝ ↦ (f x : ℂ) * (star (hD.eigenvectorUnitary : Matrix A A ℂ) * R) i j)
        (Complex.ofReal_injective heig)
    · simp only [hzero, mul_zero]
  simpa only [← mul_assoc, mul_smul_comm, Unitary.mul_star_self_of_mem
    hD.eigenvectorUnitary.prop, one_mul] using
    congrArg (fun M : Matrix A A ℂ ↦ (hD.eigenvectorUnitary : Matrix A A ℂ) * M) hf

omit [DecidableEq A] in
private theorem finKronecker_mul_local {k : ℕ} (M L : Fin k → Matrix A A ℂ) :
    finKronecker M * finKronecker L = finKronecker (fun i ↦ M i * L i) := by
  ext x y
  simp only [mul_apply, finKronecker_apply]
  simpa only [Finset.prod_mul_distrib] using
    (Fintype.prod_sum (fun (i : Fin k) (a : A) ↦ M i (x i) a * L i a (y i))).symm

omit [DecidableEq A] in
private theorem ground_isStarProjection (Ω : A → ℂ)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) : IsStarProjection (vecMulVec Ω (star Ω)) := by
  rw [isStarProjection_iff']
  have hdot : Ω ⬝ᵥ star Ω = 1 := by
    simpa only [EuclideanSpace.inner_toLp_toLp, hΩ, RCLike.ofReal_one, one_pow] using
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (WithLp.toLp 2 Ω))
  simp only [vecMulVec_mul_vecMulVec, dotProduct_comm (star Ω), hdot, one_smul,
    star_eq_conjTranspose, conjTranspose_vecMulVec, star_star, and_self]

omit [DecidableEq A] in
private theorem finKronecker_star_local {k : ℕ} (M : Fin k → Matrix A A ℂ) :
    star (finKronecker M) = finKronecker (fun i ↦ star (M i)) := by
  ext x y
  simp only [star_eq_conjTranspose, conjTranspose_apply, finKronecker_apply, star_prod]

private theorem finKronecker_one_local (k : ℕ) :
    finKronecker (fun _ : Fin k ↦ (1 : Matrix A A ℂ)) = 1 := by
  ext x y
  simp only [finKronecker_apply, one_apply, Fintype.prod_boole, ← funext_iff]

/-- The actual exact-excitation sector is an orthogonal projection.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 441–456. -/
theorem isStarProjection_replicaExcitationProjection (Ω : A → ℂ)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (B : Finset (Fin k)) :
    IsStarProjection (replicaExcitationProjection Ω k B) := by
  rw [isStarProjection_iff', replicaExcitationProjection,
    finKronecker_mul_local, finKronecker_star_local]
  have hP := ground_isStarProjection Ω hΩ
  have hproj (i : Fin k) : IsStarProjection
      (if i ∈ B then 1 - vecMulVec Ω (star Ω) else vecMulVec Ω (star Ω)) :=
    if h : i ∈ B then (ite_eq_left h).symm ▸ hP.one_sub else (ite_eq_right h).symm ▸ hP
  exact ⟨congrArg finKronecker (funext fun i ↦ (hproj i).isIdempotentElem.eq),
    congrArg finKronecker (funext fun i ↦ (hproj i).isSelfAdjoint.star_eq)⟩

/-- The actual exact-excitation sectors partition the full physical identity.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 441–456. -/
theorem sum_replicaExcitationProjection (Ω : A → ℂ) (k : ℕ) :
    ∑ B : Finset (Fin k), replicaExcitationProjection Ω k B = 1 := by
  ext x y
  simp only [sum_apply, replicaExcitationProjection, finKronecker_apply,
    Matrix.ite_apply, sub_apply]
  simp only [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, ← Finset.compl_eq_univ_sdiff, ← Fintype.prod_add,
    sub_add_cancel]
  exact congrArg (fun M : Matrix (Fin k → A) (Fin k → A) ℂ ↦ M x y)
    (finKronecker_one_local (A := A) k)

private theorem single_copy_mul_finKronecker {k : ℕ} (i : Fin k)
    (K : Matrix A A ℂ) (M : Fin k → Matrix A A ℂ) (c : ℂ)
    (hc : K * M i = c • M i) :
    finKronecker (fun j : Fin k ↦ if j = i then K else 1) * finKronecker M =
      c • finKronecker M := by
  rw [finKronecker_mul_local]
  have hfactor (j : Fin k) : (if j = i then K else 1) * M j =
      (if j = i then c else 1) • M j := by
    by_cases hji : j = i
    all_goals simp [hji, hc]
  ext x y
  simp only [finKronecker_apply, hfactor, smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

/-- The excitation count equals the cardinality on each actual sector.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 421–456. -/
theorem replicaDefectCount_mul_replicaExcitationProjection (Ω : A → ℂ)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (B : Finset (Fin k)) :
    replicaDefectCount Ω k * replicaExcitationProjection Ω k B =
      (B.card : ℂ) • replicaExcitationProjection Ω k B := by
  have hP := ground_isStarProjection Ω hΩ
  have hc (i : Fin k) : (1 - vecMulVec Ω (star Ω)) *
      (if i ∈ B then 1 - vecMulVec Ω (star Ω) else vecMulVec Ω (star Ω)) =
      (if i ∈ B then (1 : ℂ) else 0) •
        (if i ∈ B then 1 - vecMulVec Ω (star Ω) else vecMulVec Ω (star Ω)) := by
    by_cases hi : i ∈ B
    all_goals simp [hi, hP.one_sub.isIdempotentElem.eq, hP.one_sub_mul_self]
  simp only [replicaDefectCount, replicaExcitationProjection, Finset.sum_mul]
  have hterm (i : Fin k) := single_copy_mul_finKronecker i (1 - vecMulVec Ω (star Ω))
    (fun j ↦ if j ∈ B then 1 - vecMulVec Ω (star Ω) else vecMulVec Ω (star Ω))
    (if i ∈ B then (1 : ℂ) else 0) (hc i)
  simp only [hterm, ← Finset.sum_smul, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

private theorem replicaDefectCount_isHermitian (Ω : A → ℂ) (k : ℕ) :
    (replicaDefectCount Ω k).IsHermitian := by
  change star (replicaDefectCount Ω k) = replicaDefectCount Ω k
  have hP : star (vecMulVec Ω (star Ω)) = vecMulVec Ω (star Ω) := by
    simp only [star_eq_conjTranspose, conjTranspose_vecMulVec, star_star]
  simp only [replicaDefectCount, star_sum, finKronecker_star_local, apply_ite star,
    star_sub, star_one, hP]

/-- The literal spectral cutoff is the sum of the actual sectors below its threshold.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 421–456. -/
theorem cfc_replicaDefectCount_eq_sum_replicaExcitationProjection (Ω : A → ℂ)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (t : ℝ) :
    cfc (fun r : ℝ ↦ if r ≤ t then 1 else 0) (replicaDefectCount Ω k) =
      ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) ↦ (B.card : ℝ) ≤ t),
        replicaExcitationProjection Ω k B := by
  have hN := replicaDefectCount_isHermitian Ω k
  have hmul (B : Finset (Fin k)) :
      replicaDefectCount Ω k * replicaExcitationProjection Ω k B =
        ((B.card : ℝ) : ℂ) • replicaExcitationProjection Ω k B := by
    simpa only [Complex.ofReal_natCast] using
      replicaDefectCount_mul_replicaExcitationProjection Ω hΩ k B
  have hf (B : Finset (Fin k)) :
      cfc (fun r : ℝ ↦ if r ≤ t then 1 else 0) (replicaDefectCount Ω k) *
        replicaExcitationProjection Ω k B =
      if (B.card : ℝ) ≤ t then replicaExcitationProjection Ω k B else 0 := by
    simpa only [apply_ite (fun r : ℝ ↦ (r : ℂ)), Complex.ofReal_one,
      Complex.ofReal_zero, ite_smul, one_smul, zero_smul] using
      cfc_mul_of_mul_eq_smul hN (B.card : ℝ) (hmul B)
        (fun r : ℝ ↦ if r ≤ t then 1 else 0)
  calc
    cfc (fun r : ℝ ↦ if r ≤ t then 1 else 0) (replicaDefectCount Ω k) =
        cfc (fun r : ℝ ↦ if r ≤ t then 1 else 0) (replicaDefectCount Ω k) *
          (∑ B : Finset (Fin k), replicaExcitationProjection Ω k B) := by
      rw [sum_replicaExcitationProjection, mul_one]
    _ = ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) ↦ (B.card : ℝ) ≤ t),
        replicaExcitationProjection Ω k B := by
      simp only [Finset.mul_sum, hf, Finset.sum_filter]

/-- Distinct actual exact-excitation sectors are orthogonal.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 441–456. -/
theorem replicaExcitationProjection_mul_of_ne (Ω : A → ℂ)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) {B C : Finset (Fin k)} (hBC : B ≠ C) :
    replicaExcitationProjection Ω k B * replicaExcitationProjection Ω k C = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp (mt Finset.ext hBC)
  have hlocal :
      (if i ∈ B then 1 - vecMulVec Ω (star Ω) else vecMulVec Ω (star Ω)) *
      (if i ∈ C then 1 - vecMulVec Ω (star Ω) else vecMulVec Ω (star Ω)) = 0 := by
    by_cases hb : i ∈ B
    all_goals by_cases hc : i ∈ C
    all_goals simp_all [(ground_isStarProjection Ω hΩ).one_sub_mul_self,
      (ground_isStarProjection Ω hΩ).mul_one_sub_self]
  rw [replicaExcitationProjection, replicaExcitationProjection, finKronecker_mul_local]
  ext x y
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (congrArg (fun M : Matrix A A ℂ ↦ M (x i) (y i)) hlocal)

omit [DecidableEq A] in
private theorem norm_mulVec_sq_of_isStarProjection {P : Matrix A A ℂ}
    (hP : IsStarProjection P) (u : A → ℂ) :
    ‖WithLp.toLp 2 (P *ᵥ u)‖ ^ 2 = (star u ⬝ᵥ (P *ᵥ u)).re := by
  have hpair : star (P *ᵥ u) ⬝ᵥ (P *ᵥ u) = star u ⬝ᵥ (P *ᵥ u) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      show Pᴴ = P from hP.isSelfAdjoint, hP.isIdempotentElem.eq]
  change ‖WithLp.toLp 2 (P *ᵥ u)‖ ^ 2 = RCLike.re (star u ⬝ᵥ (P *ᵥ u))
  simpa only [re_star_dotProduct_self_eq_norm_sq, PiLp.coe_symm_continuousLinearEquiv] using
    congrArg (RCLike.re : ℂ → ℝ) hpair

/-- An actual cutoff vector decomposes into its retained orthogonal excitation sectors.
The squared masses of all actual components sum to the original squared mass.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 441–456. -/
theorem replicaDefectCutoff_decomposition {C : Type*} [Fintype C] [DecidableEq C]
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (t : ℝ)
    (u : ((Fin k → A) × C) → ℂ)
    (hu : (cfc (fun r : ℝ ↦ if r ≤ t then 1 else 0) (replicaDefectCount Ω k) ⊗ₖ
      (1 : Matrix C C ℂ)) *ᵥ u = u) :
    u = ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) ↦ (B.card : ℝ) ≤ t),
        (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u ∧
      ∑ B : Finset (Fin k),
        ‖WithLp.toLp 2 ((replicaExcitationProjection Ω k B ⊗ₖ
          (1 : Matrix C C ℂ)) *ᵥ u)‖ ^ 2 = ‖WithLp.toLp 2 u‖ ^ 2 := by
  constructor
  · calc
      u = (cfc (fun r : ℝ ↦ if r ≤ t then 1 else 0) (replicaDefectCount Ω k) ⊗ₖ
        (1 : Matrix C C ℂ)) *ᵥ u := hu.symm
      _ = ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) ↦ (B.card : ℝ) ≤ t),
          (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ u := by
        rw [cfc_replicaDefectCount_eq_sum_replicaExcitationProjection Ω hΩ]
        change leftKroneckerEmbed (n := C)
          (∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) ↦ (B.card : ℝ) ≤ t),
            replicaExcitationProjection Ω k B) *ᵥ u =
          ∑ B ∈ Finset.univ.filter (fun B : Finset (Fin k) ↦ (B.card : ℝ) ≤ t),
            leftKroneckerEmbed (n := C) (replicaExcitationProjection Ω k B) *ᵥ u
        rw [map_sum, sum_mulVec]
  · have hnorm (B : Finset (Fin k)) :
        ‖WithLp.toLp 2 ((replicaExcitationProjection Ω k B ⊗ₖ
          (1 : Matrix C C ℂ)) *ᵥ u)‖ ^ 2 =
        (star u ⬝ᵥ ((replicaExcitationProjection Ω k B ⊗ₖ
          (1 : Matrix C C ℂ)) *ᵥ u)).re :=
      norm_mulVec_sq_of_isStarProjection
        ((isStarProjection_replicaExcitationProjection Ω hΩ k B).map
          (leftKroneckerEmbed (n := C))) u
    simp only [hnorm, ← Complex.re_sum, ← dotProduct_sum, ← sum_mulVec]
    have hsum : (∑ B : Finset (Fin k),
        replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) = 1 := by
      change (∑ B : Finset (Fin k),
        leftKroneckerEmbed (n := C) (replicaExcitationProjection Ω k B)) = 1
      rw [← map_sum, sum_replicaExcitationProjection, map_one]
    rw [hsum, one_mulVec]
    simpa only [PiLp.coe_symm_continuousLinearEquiv, RCLike.re_to_complex] using
      re_star_dotProduct_self_eq_norm_sq u

end Matrix
