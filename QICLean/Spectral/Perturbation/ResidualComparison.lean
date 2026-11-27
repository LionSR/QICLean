/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Parameter.SpectralWindowPrecision
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.Spectral.Eigenvalue.GroundEnergyBounds
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.Spectral.Eigenvalue.MatrixSpectralDecomp

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

section SpectralResidualGroundEnergy

/-!
# Ground-energy displacement from a low-energy residual

A residual on the actual low-energy spectral space controls the change in the
least energy. This is the variational step needed before spectral cutoffs can
be measured relative to the two different ground energies.

These are supporting estimates for the corrected soft-truncation comparison
in ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. No gap,
nondegeneracy, or spectral-subspace comparison is assumed.
-/

open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- The residual on the actual low-energy space of the second matrix bounds
how far its least energy lies below that of the first. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
lemma IsHermitian.minEigenvalue_sub_le_of_spectralSpanLE_residual
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (eta xi : ℝ) (heta : 0 ≤ eta)
    (hres : ‖(toEuclideanCLM (𝕜 := ℂ) (n := n) (A - B)).domRestrict
      (Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues
        (minEigenvalue hB + eta))‖ ≤ xi) :
    minEigenvalue hA - minEigenvalue hB ≤ xi := by
  classical
  let T := toEuclideanCLM (𝕜 := ℂ) (n := n)
  obtain ⟨i, hi⟩ := minEigenvalue_achieved hB
  let v := hB.eigenvectorBasis i
  have hvnorm : ‖v‖ = 1 := hB.eigenvectorBasis.norm_eq_one i
  have hv : v ∈ Submodule.spectralSpanLE hB.eigenvectorBasis hB.eigenvalues
      (minEigenvalue hB + eta) := by
    apply Submodule.subset_span
    exact ⟨i, by change hB.eigenvalues i ≤ _; rw [hi]; linarith only [heta], rfl⟩
  have hbound : ‖T (A - B) v‖ ≤ xi := by
    have hb := ((T (A - B)).domRestrict _).le_of_opNorm_le hres ⟨v, hv⟩
    change ‖T (A - B) v‖ ≤ xi * ‖v‖ at hb
    simpa only [hvnorm, mul_one] using hb
  have hpos := (Matrix.isPositive_toEuclideanLin_iff.mpr
    (sub_minEigenvalue_smul_one_posSemidef hA)).re_inner_nonneg_right v
  change 0 ≤ (inner ℂ v (T (A - (minEigenvalue hA : ℂ) • 1) v)).re at hpos
  rw [map_sub, map_smul, map_one] at hpos
  simp only [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self,
    inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hvnorm,
    Complex.sub_re] at hpos
  norm_num at hpos
  have heigen : T B v = (minEigenvalue hB : ℂ) • v := by
    dsimp only [T, v]
    rw [hB.toEuclideanCLM_eigenvectorBasis, hi]
    rfl
  have hdiff : (inner ℂ v (T (A - B) v)).re =
      (inner ℂ v (T A v)).re - minEigenvalue hB := by
    rw [map_sub, _root_.sub_apply, heigen, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hvnorm]
    simp
  have hinner : (inner ℂ v (T (A - B) v)).re ≤ xi :=
    (re_inner_le_norm (𝕜 := ℂ) v (T (A - B) v)).trans
    (by simpa only [hvnorm, one_mul] using hbound)
  rw [hdiff] at hinner
  linarith only [hpos, hinner]

end Matrix

end SpectralResidualGroundEnergy

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

section TwoSidedResidual

/-!
# Two-sided residuals of a nearby operator

If an operator `M'` has two small residuals `‖M' ψ - z φ‖ ≤ ε` and `‖M'* φ - z ψ‖ ≤ ε` on unit
vectors `ψ, φ`, then every operator `M` with `‖M - M'‖ ≤ δ` has both residuals at most
`δ + ε`. This passes the two-sided Gaussian filter of the information reset to its localized
approximation.

Moved from TNLean, `TNLean/Lattice/RegionalReset.lean` at commit `e41c3b63`
(`norm_two_sided_le_of_norm_sub_le`), with vectors in `EuclideanSpace`.

## Main results

* `Matrix.norm_two_sided_le_of_norm_sub_le`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, proof of Lemma 3.3 (`lem:reset`), `02-information.tex`, lines 498–564,
  `eq:info-local-two-sided`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Two-sided residuals of a nearby operator.** If `‖M - M'‖ ≤ δ` and `M'` has residuals
`‖M' ψ - z φ‖ ≤ ε` and `‖M'* φ - z ψ‖ ≤ ε` on unit vectors `ψ, φ`, then `M` has both residuals
at most `δ + ε`. Polynomial PEPS approximation, `02-information.tex`, lines 498–564. -/
theorem norm_two_sided_le_of_norm_sub_le {M M' : Matrix n n ℂ} {ψ φ : EuclideanSpace ℂ n}
    {z : ℂ} {δ ε : ℝ} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hM : ‖M - M'‖ ≤ δ)
    (hfwd : ‖toEuclideanLin M' ψ - z • φ‖ ≤ ε) (hrev : ‖toEuclideanLin M'ᴴ φ - z • ψ‖ ≤ ε) :
    ‖toEuclideanLin M ψ - z • φ‖ ≤ δ + ε ∧ ‖toEuclideanLin Mᴴ φ - z • ψ‖ ≤ δ + ε := by
  have hop (A : Matrix n n ℂ) (x : EuclideanSpace ℂ n) :
      ‖toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ := by
    have h := (toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm x
    rw [l2_opNorm_toEuclideanCLM] at h
    exact h
  have hsplit (A A' : Matrix n n ℂ) (x w : EuclideanSpace ℂ n) :
      ‖toEuclideanLin A x - w‖ ≤ ‖toEuclideanLin (A - A') x‖ + ‖toEuclideanLin A' x - w‖ := by
    rw [map_sub, LinearMap.sub_apply]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  constructor
  · refine (hsplit M M' ψ _).trans (add_le_add ((hop _ ψ).trans ?_) hfwd)
    rw [hψ, mul_one]
    exact hM
  · refine (hsplit Mᴴ M'ᴴ φ _).trans (add_le_add ((hop _ φ).trans ?_) hrev)
    rw [hφ, mul_one, ← conjTranspose_sub, l2_opNorm_conjTranspose]
    exact hM

end Matrix

end TwoSidedResidual
