/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralQuadraticForm
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Convex trace functions on Hermitian spectral domains

Wolf's convex trace-functions corollary following Theorem 5.17 holds on any real interval,
including intervals excluding zero, for arbitrary scalar convex functions. We prove it directly
using spectral weights and finite scalar Jensen, without operator convexity or positivity of the
matrices. Every function on a finite matrix spectrum has a well-defined functional calculus.

The domain is `Matrix.hermitianSpectralDomain`: Hermitian matrices whose real spectra lie in
the given interval. Unit-vector expectations stay in the interval; this proves convexity of the
domain before proving convexity of the real trace. The finite-mixture statement includes both
domain membership and the trace bound.

Source: `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 1081–1088.
-/

open scoped Matrix BigOperators
open Finset

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hermitian matrices whose real spectra lie in a prescribed set, as in Wolf's convex
trace-functions corollary following Theorem 5.17. -/
def hermitianSpectralDomain (n : Type*) [Fintype n] [DecidableEq n] (I : Set ℝ) :
    Set (Matrix n n ℂ) :=
  {A | A.IsHermitian ∧ spectrum ℝ A ⊆ I}

namespace IsHermitian

variable {I : Set ℝ} {A B : Matrix n n ℂ}

/-- A unit-vector expectation of a Hermitian matrix lies in every convex set containing its
spectrum. This is the spectral-domain step in Wolf's convex trace-functions corollary. -/
theorem re_dotProduct_mem_of_spectrum_subset (hA : A.IsHermitian) (hI : Convex ℝ I)
    (hAI : spectrum ℝ A ⊆ I) {v : n → ℂ} (hv : star v ⬝ᵥ v = (1 : ℂ)) :
    (star v ⬝ᵥ (A *ᵥ v)).re ∈ I := by
  rw [hA.re_dotProduct_mulVec_eq_sum]
  simpa only [smul_eq_mul] using hI.sum_mem
    (fun i _ => hA.spectralWeight_nonneg v i) (hA.sum_spectralWeight hv)
    (fun i _ => hAI (hA.eigenvalues_mem_spectrum_real i))

/-- Scalar Jensen for a Hermitian matrix with spectrum in an arbitrary convex set. No
positivity or continuity assumption is needed; compare Wolf's proof following (5.53). -/
theorem diagonal_jensen_of_spectrum_subset (hA : A.IsHermitian)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ I f) (hAI : spectrum ℝ A ⊆ I)
    {v : n → ℂ} (hv : star v ⬝ᵥ v = (1 : ℂ)) :
    f ((star v ⬝ᵥ (A *ᵥ v)).re) ≤ (star v ⬝ᵥ (hA.cfc f *ᵥ v)).re := by
  rw [hA.re_dotProduct_mulVec_eq_sum, hA.re_dotProduct_cfc_mulVec_eq_sum]
  simpa only [smul_eq_mul] using hf.map_sum_le
    (fun i _ => hA.spectralWeight_nonneg v i) (hA.sum_spectralWeight hv)
    (fun i _ => hAI (hA.eigenvalues_mem_spectrum_real i))

private lemma eigenvector_unit (hA : A.IsHermitian) (j : n) :
    star (⇑(hA.eigenvectorBasis j)) ⬝ᵥ ⇑(hA.eigenvectorBasis j) = (1 : ℂ) := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1 j]
  simp

omit [DecidableEq n] in
private lemma re_quad_smul_add (a b : ℝ) (A B : Matrix n n ℂ) (v : n → ℂ) :
    (star v ⬝ᵥ ((a • A + b • B) *ᵥ v)).re =
      a * (star v ⬝ᵥ (A *ᵥ v)).re + b * (star v ⬝ᵥ (B *ᵥ v)).re := by
  simp [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    Complex.real_smul, Complex.mul_re]

end IsHermitian

/-- The Hermitian spectral domain of a real interval is convex. In particular the spectrum
of a mixture remains in the original interval, even when that interval excludes zero.
This is part of Wolf's convex trace-functions corollary following Theorem 5.17. -/
theorem convex_hermitianSpectralDomain {I : Set ℝ} (hI : Convex ℝ I) :
    Convex ℝ (hermitianSpectralDomain n I) := by
  intro A hA B hB a b ha hb hab
  have hM : (a • A + b • B).IsHermitian :=
    (hA.1.smul (isSelfAdjoint_iff.mpr (star_trivial a))).add
      (hB.1.smul (isSelfAdjoint_iff.mpr (star_trivial b)))
  refine ⟨hM, ?_⟩
  rw [hM.spectrum_real_eq_range_eigenvalues]
  rintro x ⟨j, rfl⟩
  rw [hM.eigenvalues_eq]
  change (star (⇑(hM.eigenvectorBasis j)) ⬝ᵥ
    ((a • A + b • B) *ᵥ ⇑(hM.eigenvectorBasis j))).re ∈ I
  rw [IsHermitian.re_quad_smul_add]
  exact hI
    (hA.1.re_dotProduct_mem_of_spectrum_subset hI hA.2 (hM.eigenvector_unit j))
    (hB.1.re_dotProduct_mem_of_spectrum_subset hI hB.2 (hM.eigenvector_unit j)) ha hb hab

namespace IsHermitian

variable {A B : Matrix n n ℂ}

private lemma sum_re_quad_eq_trace (hM : A.IsHermitian) (C : Matrix n n ℂ) :
    ∑ j, (star (⇑(hM.eigenvectorBasis j)) ⬝ᵥ
      (C *ᵥ ⇑(hM.eigenvectorBasis j))).re = C.trace.re := by
  have h := LinearMap.trace_eq_sum_inner C.toEuclideanLin hM.eigenvectorBasis
  have ht : LinearMap.trace ℂ _ C.toEuclideanLin = C.trace := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
  rw [ht] at h
  have hq (j : n) : inner ℂ (hM.eigenvectorBasis j)
      (C.toEuclideanLin (hM.eigenvectorBasis j)) =
      star (⇑(hM.eigenvectorBasis j)) ⬝ᵥ (C *ᵥ ⇑(hM.eigenvectorBasis j)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    rfl
  have hr := congrArg Complex.re h
  simpa only [Complex.re_sum, hq] using hr.symm

/-- Wolf's convex trace-functions corollary after Theorem 5.17: scalar convexity on an
arbitrary interval suffices for trace convexity on its Hermitian spectral domain. -/
theorem trace_cfc_convex_le {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (cfc f (a • A + b • B)).trace.re ≤
      a * (hA.cfc f).trace.re + b * (hB.cfc f).trace.re := by
  have hM := convex_hermitianSpectralDomain hf.1 ⟨hA, hAI⟩ ⟨hB, hBI⟩ ha hb hab
  let ψ : n → n → ℂ := fun j => ⇑(hM.1.eigenvectorBasis j)
  have hpoint (j : n) :
      f (hM.1.eigenvalues j) ≤
        a * (star (ψ j) ⬝ᵥ (hA.cfc f *ᵥ ψ j)).re +
        b * (star (ψ j) ⬝ᵥ (hB.cfc f *ᵥ ψ j)).re := by
    rw [hM.1.eigenvalues_eq]
    change f ((star (ψ j) ⬝ᵥ ((a • A + b • B) *ᵥ ψ j)).re) ≤ _
    rw [re_quad_smul_add]
    exact (hf.2
      (hA.re_dotProduct_mem_of_spectrum_subset hf.1 hAI (hM.1.eigenvector_unit j))
      (hB.re_dotProduct_mem_of_spectrum_subset hf.1 hBI (hM.1.eigenvector_unit j))
      ha hb hab).trans (add_le_add
        (mul_le_mul_of_nonneg_left
          (hA.diagonal_jensen_of_spectrum_subset hf hAI (hM.1.eigenvector_unit j)) ha)
        (mul_le_mul_of_nonneg_left
          (hB.diagonal_jensen_of_spectrum_subset hf hBI (hM.1.eigenvector_unit j)) hb))
  have ht := hM.1.trace_cfc_eq_sum_re f
  change (hM.1.cfc f).trace.re = _ at ht
  rw [hM.1.cfc_eq, ht]
  calc
    ∑ j, f (hM.1.eigenvalues j) ≤ ∑ j,
        (a * (star (ψ j) ⬝ᵥ (hA.cfc f *ᵥ ψ j)).re +
          b * (star (ψ j) ⬝ᵥ (hB.cfc f *ᵥ ψ j)).re) :=
      sum_le_sum fun j _ => hpoint j
    _ = a * (hA.cfc f).trace.re + b * (hB.cfc f).trace.re := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum,
        sum_re_quad_eq_trace hM.1, sum_re_quad_eq_trace hM.1]

end IsHermitian

/-- The map `A ↦ Re trace (f(A))` is convex on the actual Hermitian spectral domain of
`I`. This is Wolf's convex trace-functions corollary, lines 1081–1088. -/
theorem convexOn_trace_cfc {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f) :
    ConvexOn ℝ (hermitianSpectralDomain n I) (fun A => (cfc f A).trace.re) := by
  refine ⟨convex_hermitianSpectralDomain hf.1, ?_⟩
  intro A hA B hB a b ha hb hab
  simpa only [smul_eq_mul, hA.1.cfc_eq, hB.1.cfc_eq] using
    hA.1.trace_cfc_convex_le hf hB.1 hA.2 hB.2 ha hb hab

/-- Finite mixtures stay in the Hermitian spectral domain and satisfy Wolf's convex
trace-functions inequality. The normalization is the ordinary finite probability sum. -/
theorem trace_cfc_sum_le {ι : Type*} {I : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ I f) (s : Finset ι) (w : ι → ℝ) (A : ι → Matrix n n ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hA : ∀ i ∈ s, A i ∈ hermitianSpectralDomain n I) :
    (∑ i ∈ s, w i • A i) ∈ hermitianSpectralDomain n I ∧
      (cfc f (∑ i ∈ s, w i • A i)).trace.re ≤
        ∑ i ∈ s, w i * (cfc f (A i)).trace.re := by
  exact ⟨(convex_hermitianSpectralDomain hf.1).sum_mem hw hsum hA,
    by simpa only [smul_eq_mul] using (convexOn_trace_cfc hf).map_sum_le hw hsum hA⟩

end Matrix
