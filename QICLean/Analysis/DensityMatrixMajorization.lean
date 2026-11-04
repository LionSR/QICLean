/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.VectorMajorization
import QICLean.Analysis.TraceCFC
import QICLean.Algebra.PermutationMatrixUnitary
import Mathlib.Analysis.Matrix.PosDef

/-!
# Majorization and mixtures of unitary conjugations

Wolf, Chapter 8, Theorem 8.7 and Eq. (8.21),
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 298–321.
The equivalences hold for all Hermitian matrices, including singular matrices;
in particular they apply to every pair of density matrices of the same dimension.
The trace criterion uses the actual functional calculus for every convex real function.
-/

open Matrix Finset

namespace TNLean

variable {d : ℕ}

/-- A finite probability mixture of actual unitary conjugations of `ρ` equals `σ`.
This is Wolf Eq. (8.21); zero coefficients and repeated unitaries are allowed. -/
def IsRandomUnitaryImage (ρ σ : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ k : ℕ, ∃ p : Fin k → ℝ, ∃ U : Fin k → Matrix.unitaryGroup (Fin d) ℂ,
    (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      σ = ∑ i, (p i : ℂ) • ((U i : Matrix (Fin d) (Fin d) ℂ) * ρ *
        star (U i : Matrix (Fin d) (Fin d) ℂ))

/-- Squared entry moduli of a unitary matrix form a doubly stochastic matrix.
This is the stochastic matrix used in Wolf Theorem 8.7, implication 3 to 1. -/
theorem unitary_normSq_mem_doublyStochastic (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (fun i j => Complex.normSq ((U : Matrix (Fin d) (Fin d) ℂ) i j)) ∈
      doublyStochastic ℝ (Fin d) := by
  refine mem_doublyStochastic_iff_sum.mpr ⟨fun _ _ => Complex.normSq_nonneg _, ?_, ?_⟩
  · intro i
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A i i).re)
      (Unitary.coe_mul_star_self U)
    simpa [Matrix.mul_apply, Matrix.star_apply, Complex.mul_conj] using h
  · intro j
    have h := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A j j).re)
      (Unitary.coe_star_mul_self U)
    simpa [Matrix.mul_apply, Matrix.star_apply, Complex.normSq_apply] using h

private theorem randomUnitaryImage_of_fintype {ι : Type*} [Fintype ι]
    {ρ σ : Matrix (Fin d) (Fin d) ℂ} (p : ι → ℝ)
    (U : ι → Matrix.unitaryGroup (Fin d) ℂ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1)
    (heq : σ = ∑ i, (p i : ℂ) • ((U i : Matrix (Fin d) (Fin d) ℂ) * ρ *
      star (U i : Matrix (Fin d) (Fin d) ℂ))) : IsRandomUnitaryImage ρ σ := by
  classical
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, p ∘ e, U ∘ e, fun i => hp (e i), ?_, ?_⟩
  · simpa only [Function.comp_apply, Equiv.sum_comp] using hs
  · exact heq.trans (Equiv.sum_comp e _).symm

private noncomputable def permUnitary (τ : Equiv.Perm (Fin d)) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨τ.permMatrix ℂ, τ.permMatrix_mem_unitaryGroup⟩

private theorem permUnitary_conj_diagonal (τ : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    Unitary.conjStarAlgAut ℂ _ (permUnitary τ) (diagonal (fun i => (x i : ℂ))) =
      diagonal (fun i => (x (τ i) : ℂ)) := by
  classical
  simp only [Unitary.conjStarAlgAut_apply, permUnitary, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext i j
  simp [submatrix_apply, diagonal_apply, Equiv.Perm.inv_def, τ.injective.eq_iff]

end TNLean

namespace Matrix.IsHermitian

variable {d : ℕ} {ρ σ : Matrix (Fin d) (Fin d) ℂ}

/-- `ρ` majorizes `σ` when the actual decreasing eigenvalue vectors satisfy Wolf Eq. (8.16).
The eigenvalues are sorted by `VectorMajorized`, preserving every multiplicity. -/
def Majorizes (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : Prop :=
  TNLean.VectorMajorized hσ.eigenvalues hρ.eigenvalues

/-- Wolf Theorem 8.7, clauses 1 and 2, in the stronger Hermitian form.
Finite spectra allow every function on the real line in the functional calculus. -/
theorem majorizes_iff_trace_convex (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    hρ.Majorizes hσ ↔ ∀ f : ℝ → ℝ, ConvexOn ℝ Set.univ f →
      (cfc f σ).trace.re ≤ (cfc f ρ).trace.re := by
  rw [Majorizes, TNLean.vectorMajorized_iff_sum_convex_le]
  simp only [hρ.cfc_eq, hσ.cfc_eq, ← RCLike.re_eq_complex_re,
    trace_cfc_eq_sum_re]

/-- Wolf Theorem 8.7, implication 1 to 3: the finite unitary mixture is constructed
from Birkhoff coefficients and the two actual eigenvector bases. -/
theorem Majorizes.isRandomUnitaryImage {hρ : ρ.IsHermitian} {hσ : σ.IsHermitian}
    (h : hρ.Majorizes hσ) : TNLean.IsRandomUnitaryImage ρ σ := by
  classical
  obtain ⟨M, hM, heig⟩ := h.exists_doublyStochastic
  obtain ⟨p, hp, htotal, hperm⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hM
  let L : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] (Fin d → ℝ) :=
    (Matrix.mulVecBilin ℝ ℝ).flip hρ.eigenvalues
  have hv := congrArg L hperm
  simp only [map_sum, map_smul] at hv
  change (∑ τ, p τ • (τ.permMatrix ℝ *ᵥ hρ.eigenvalues)) = M *ᵥ hρ.eigenvalues at hv
  simp only [Matrix.permMatrix_mulVec] at hv
  have he : hσ.eigenvalues = ∑ τ, p τ • (hρ.eigenvalues ∘ τ) := heig.trans hv.symm
  have hd : diagonal (fun i => (hσ.eigenvalues i : ℂ)) =
      ∑ τ, (p τ : ℂ) • diagonal (fun i => (hρ.eigenvalues (τ i) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hi := congrArg (fun v : Fin d → ℝ => (v i : ℂ)) he
      simpa [Matrix.sum_apply, Matrix.smul_apply, Finset.sum_apply, Pi.smul_apply,
        Complex.ofReal_sum, Complex.ofReal_mul] using hi
    · simp [Matrix.sum_apply, Matrix.smul_apply, hij]
  let U (τ : Equiv.Perm (Fin d)) : Matrix.unitaryGroup (Fin d) ℂ :=
    hσ.eigenvectorUnitary * TNLean.permUnitary τ * star hρ.eigenvectorUnitary
  apply TNLean.randomUnitaryImage_of_fintype p U hp htotal
  change σ = ∑ τ, (p τ : ℂ) • Unitary.conjStarAlgAut ℂ _ (U τ) ρ
  calc
    σ = Unitary.conjStarAlgAut ℂ _ hσ.eigenvectorUnitary
        (diagonal (fun i => (hσ.eigenvalues i : ℂ))) := hσ.spectral_theorem
    _ = ∑ τ, (p τ : ℂ) • Unitary.conjStarAlgAut ℂ _ hσ.eigenvectorUnitary
        (diagonal (fun i => (hρ.eigenvalues (τ i) : ℂ))) := by rw [hd, map_sum]; simp
    _ = _ := by
      apply sum_congr rfl
      intro τ _
      congr 1
      rw [← TNLean.permUnitary_conj_diagonal τ hρ.eigenvalues,
        ← Unitary.conjStarAlgAut_mul_apply]
      have hr := congrArg (Unitary.conjStarAlgAut ℂ _ (U τ)) hρ.spectral_theorem
      rw [← Unitary.conjStarAlgAut_mul_apply] at hr
      have hu : U τ * hρ.eigenvectorUnitary =
          hσ.eigenvectorUnitary * TNLean.permUnitary τ := by
        simp [U, mul_assoc]
      rw [hu] at hr
      exact hr.symm

/-- Wolf Theorem 8.7, implication 3 to 1. Diagonalizing the actual mixture
produces the stochastic matrix whose entries are the weighted squared unitary entries. -/
theorem majorizes_of_randomUnitaryImage (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hmix : TNLean.IsRandomUnitaryImage ρ σ) : hρ.Majorizes hσ := by
  classical
  obtain ⟨k, p, U, hp, htotal, heq⟩ := hmix
  let W (i : Fin k) : Matrix.unitaryGroup (Fin d) ℂ :=
    star hσ.eigenvectorUnitary * U i * hρ.eigenvectorUnitary
  have hd : diagonal (fun a => (hσ.eigenvalues a : ℂ)) =
      ∑ i, (p i : ℂ) • Unitary.conjStarAlgAut ℂ _ (W i)
        (diagonal (fun a => (hρ.eigenvalues a : ℂ))) := by
    change σ = ∑ i, (p i : ℂ) • Unitary.conjStarAlgAut ℂ _ (U i) ρ at heq
    have ht (i : Fin k) :
        Unitary.conjStarAlgAut ℂ _ (star hσ.eigenvectorUnitary)
          (Unitary.conjStarAlgAut ℂ _ (U i) ρ) =
        Unitary.conjStarAlgAut ℂ _ (W i)
          (diagonal (fun a => (hρ.eigenvalues a : ℂ))) := by
      have hr := congrArg (fun A => Unitary.conjStarAlgAut ℂ _
        (star hσ.eigenvectorUnitary) (Unitary.conjStarAlgAut ℂ _ (U i) A))
          hρ.spectral_theorem
      refine hr.trans ?_
      change Unitary.conjStarAlgAut ℂ _ (star hσ.eigenvectorUnitary)
        (Unitary.conjStarAlgAut ℂ _ (U i)
          (Unitary.conjStarAlgAut ℂ _ hρ.eigenvectorUnitary _)) =
        Unitary.conjStarAlgAut ℂ _
          ((star hσ.eigenvectorUnitary * U i) * hρ.eigenvectorUnitary) _
      rw [Unitary.conjStarAlgAut_mul_apply, Unitary.conjStarAlgAut_mul_apply]
      rfl
    have hh := congrArg (Unitary.conjStarAlgAut ℂ _ (star hσ.eigenvectorUnitary)) heq
    rw [hσ.conjStarAlgAut_star_eigenvectorUnitary, map_sum] at hh
    simpa only [map_smul, ht, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using hh
  let S (i : Fin k) : Matrix (Fin d) (Fin d) ℝ :=
    fun a b => Complex.normSq ((W i : Matrix (Fin d) (Fin d) ℂ) a b)
  let M : Matrix (Fin d) (Fin d) ℝ := ∑ i, p i • S i
  have hM : M ∈ doublyStochastic ℝ (Fin d) :=
    convex_doublyStochastic.sum_mem (fun i _ => hp i) htotal
      (fun i _ => TNLean.unitary_normSq_mem_doublyStochastic (W i))
  apply (TNLean.vectorMajorized_iff_exists_doublyStochastic _ _).mpr
  refine ⟨M, hM, ?_⟩
  have hentry (i : Fin k) (a : Fin d) :
      (Unitary.conjStarAlgAut ℂ _ (W i)
        (diagonal (fun b => (hρ.eigenvalues b : ℂ))) a a).re =
          ∑ b, S i a b * hρ.eigenvalues b := by
    rw [Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.star_apply, Complex.re_sum, RCLike.star_def]
    apply sum_congr rfl
    intro b _
    rw [mul_assoc, mul_comm (hρ.eigenvalues b : ℂ), ← mul_assoc, Complex.mul_conj]
    simp [S]
  ext a
  have ha := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => (A a a).re) hd
  simp only [diagonal_apply_eq, Complex.ofReal_re, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hentry] at ha
  rw [ha]
  simp only [M, Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, sum_mul, mul_sum, mul_assoc]
  rw [sum_comm]

/-- Wolf Theorem 8.7, clauses 1 and 3, for arbitrary Hermitian matrices. -/
theorem majorizes_iff_randomUnitaryImage (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    hρ.Majorizes hσ ↔ TNLean.IsRandomUnitaryImage ρ σ :=
  ⟨Majorizes.isRandomUnitaryImage, hρ.majorizes_of_randomUnitaryImage hσ⟩

end Matrix.IsHermitian

namespace Matrix

variable {d : ℕ} {ρ : Matrix (Fin d) (Fin d) ℂ}

/-- A trace-one matrix has positive dimension; hence there are no zero-dimensional
density matrices. No positive-dimension premise is needed for the equivalences. -/
theorem dimension_pos_of_trace_one (htr : ρ.trace = 1) : 0 < d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  subst d
  simp [Matrix.trace] at htr

end Matrix
