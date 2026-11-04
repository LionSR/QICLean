/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GroundEnergyBounds
import QICLean.Analysis.LowEnergyPerturbation
import QICLean.Analysis.EuclideanEigenvectorBasis
import Mathlib.Analysis.InnerProductSpace.Positive

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
