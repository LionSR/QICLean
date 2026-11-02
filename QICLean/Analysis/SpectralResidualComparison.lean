/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SpectralResidualGroundEnergy
import QICLean.Analysis.SpectralWindowCount

/-!
# Directed spectral comparisons relative to the actual ground energies

Two residuals control the displacement of the least energies and both
comparisons between enlarged low-energy windows. Each cutoff is measured
relative to the minimum of its own actual matrix. The proof uses the finite
spectral-window estimate, not an inclusion inferred from operator order.

These are auxiliary perturbation estimates for ALVV, arXiv:1602.08828v2,
`lem:hard-trunc`, lines 955–968, and the corrected use of `lem:exp-approx`,
lines 1195–1255. No gap, ground-space dimension or prescribed eigenbasis is
assumed.
-/

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- Residuals on the two actual low-energy windows give directed closeness
at cutoffs relative to the respective canonical ground energies. The scalar
margin and counting budget are explicit. Supporting ALVV,
arXiv:1602.08828v2, `lem:hard-trunc`, lines 955–968, and the corrected
soft comparison following `lem:exp-approx`, lines 1195–1255. -/
lemma isCloseTo_spectralSpanLE_pair_of_residuals
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (eta xi w delta : ℝ) (heta : 0 < eta) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hw : 0 ≤ w) (hxiw : xi ≤ w / 2) (hdelta : 0 ≤ delta)
    (hsmall : 2 * (eta + 2) * xi ≤ delta * w ^ 2)
    (hresA : ‖(toEuclideanCLM (𝕜 := ℂ) (n := n) (A - B)).domRestrict
      (Submodule.spectralSpanLE hA.eigenvectorBasis hA.eigenvalues
        (minEigenvalue hA + eta))‖ ≤ xi)
    (hresB : ‖(toEuclideanCLM (𝕜 := ℂ) (n := n) (A - B)).domRestrict
      (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues
        (minEigenvalue hB + eta))‖ ≤ xi) :
    |minEigenvalue hA - minEigenvalue hB| ≤ xi ∧
      Submodule.IsCloseTo delta
        (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues
          (minEigenvalue hB + eta + w))
        (Submodule.spectralSpanLE hA.eigenvectorBasis hA.eigenvalues
          (minEigenvalue hA + eta)) ∧
      Submodule.IsCloseTo delta
        (Submodule.spectralSpanLE hA.eigenvectorBasis hA.eigenvalues
          (minEigenvalue hA + eta + w))
        (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues
          (minEigenvalue hB + eta)) := by
  let T := toEuclideanCLM (𝕜 := ℂ) (n := n)
  have hrevA : ‖(T (B - A)).domRestrict
      (Submodule.spectralSpanLE hA.eigenvectorBasis hA.eigenvalues
        (minEigenvalue hA + eta))‖ ≤ xi := by
    rw [show B - A = -(A - B) by abel, map_neg]
    change ‖-((T (A - B)).domRestrict _)‖ ≤ xi
    simpa only [norm_neg] using hresA
  have hup := IsHermitian.minEigenvalue_sub_le_of_spectralSpanLE_residual
    A B hA hB eta xi heta.le hresB
  have hdown := IsHermitian.minEigenvalue_sub_le_of_spectralSpanLE_residual
    B A hB hA eta xi heta.le hrevA
  have hpertA (v : EuclideanSpace ℂ n)
      (hv : v ∈ Submodule.spectralSpanLE hA.eigenvectorBasis hA.eigenvalues
        (minEigenvalue hA + eta)) : ‖T A v - T B v‖ ≤ xi * ‖v‖ := by
    have hb := ((T (A - B)).domRestrict _).le_of_opNorm_le hresA ⟨v, hv⟩
    rw [map_sub] at hb
    exact hb
  have hpertB (v : EuclideanSpace ℂ n)
      (hv : v ∈ Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues
        (minEigenvalue hB + eta)) : ‖T B v - T A v‖ ≤ xi * ‖v‖ := by
    have hb := ((T (A - B)).domRestrict _).le_of_opNorm_le hresB ⟨v, hv⟩
    rw [map_sub] at hb
    exact (norm_sub_rev _ _).trans_le hb
  have hwindow := Real.spectral_window_count_bound eta xi heta.le hxi hxi1
  have hbudget (D : ℝ) (hD : w ≤ D) :
      (⌈eta / (2 * xi)⌉₊ : ℝ) * (xi + xi) ^ 2 ≤ delta * D ^ 2 := by
    refine (hwindow.trans hsmall).trans ?_
    gcongr
  refine ⟨abs_le.mpr ⟨by linarith only [hdown], hup⟩, ?_, ?_⟩
  · exact Submodule.isCloseTo_spectralSpanLE_of_perturbation
      hA.eigenvectorBasis hB.eigenvectorBasis hA.eigenvalues hB.eigenvalues
      hA.toEuclideanCLM_eigenvectorBasis hB.toEuclideanCLM_eigenvectorBasis
      hpertA hxi (fun j _ ↦ minEigenvalue_le hA j)
      (by linarith only [heta]) (by linarith only [hup, hxiw, hxi])
      (by simpa only [add_sub_cancel_left] using
        (hbudget (minEigenvalue hB + eta + w - (minEigenvalue hA + eta) + xi)
          (by linarith only [hup])))
  · exact Submodule.isCloseTo_spectralSpanLE_of_perturbation
      hB.eigenvectorBasis hA.eigenvectorBasis hB.eigenvalues hA.eigenvalues
      hB.toEuclideanCLM_eigenvectorBasis hA.toEuclideanCLM_eigenvectorBasis
      hpertB hxi (fun j _ ↦ minEigenvalue_le hB j)
      (by linarith only [heta]) (by linarith only [hdown, hxiw, hxi])
      (by simpa only [add_sub_cancel_left] using
        (hbudget (minEigenvalue hA + eta + w - (minEigenvalue hB + eta) + xi)
          (by linarith only [hdown])))

end Matrix
