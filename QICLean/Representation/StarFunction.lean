/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaMarkedRatio
import QICLean.Representation.UniformHusimi

/-!
# Polynomial approximation of functions of the star operator

The proof of Lemma 6.4 of the area-law paper (*A two-dimensional area law from a global
spectral gap*, `05-replicas.tex`, lines 693–702) approximates the continuous functions
`u ↦ u_+^t` and `u ↦ max(u, δ)^{-t}` of the star operator `J_{Q,k}` uniformly on `[-1, 1]` by
polynomials, since "all star spectra lie in this interval". This file proves that interval
bound and the resulting operator-norm estimate
`‖φ(J_{Q,k}) - p(J_{Q,k})‖ ≤ sup_{[-1,1]} |φ - p|`.

## Main declarations

* `TensorPower.l2_opNorm_starOp_le` — `‖J‖ ≤ 1`.
* `TensorPower.abs_starValue_le_one` — every star eigenvalue lies in `[-1, 1]`.
* `TensorPower.l2_opNorm_cfc_starOp_sub_aeval_le` — the polynomial approximation estimate.
* `TensorPower.isHermitian_aeval_starOp`, `TensorPower.l2_opNorm_aeval_starOp_le`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 6.4 (`lem:symbol`), section file `05-replicas.tex`, lines 693–702.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation Polynomial
open scoped Matrix.Norms.L2Operator

namespace Matrix.IsOrthogonalResolution

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  {P : ι → Matrix n n ℂ} (hP : IsOrthogonalResolution P)
include hP

theorem hom_mul_self (c : ι → ℂ) (i : ι) : hP.hom c * P i = c i • P i := by
  rw [hom_apply, Finset.sum_mul, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, hP.mul_self]
  · intro j _ hj
    rw [smul_mul_assoc, hP.mul_of_ne hj, smul_zero]
  · simp

/-- On a nonzero part, the coefficient is bounded by the norm of `∑_i c_i P_i`. -/
theorem norm_le_l2_opNorm_hom {c : ι → ℂ} {i : ι} (hi : P i ≠ 0) : ‖c i‖ ≤ ‖hP.hom c‖ := by
  have hpos : 0 < ‖P i‖ := norm_pos_iff.mpr hi
  have h : ‖c i‖ * ‖P i‖ ≤ ‖hP.hom c‖ * ‖P i‖ := by
    rw [← norm_smul, ← hP.hom_mul_self]
    exact l2_opNorm_mul _ _
  exact le_of_mul_le_mul_right h hpos

end Matrix.IsOrthogonalResolution

namespace TensorPower

variable {F : Type*} [DecidableEq F] [Fintype F] {ι : F → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)]

/-- **The star operator has norm at most one**: it is `(m+1)⁻¹` times a sum of `m`
permutation operators. -/
theorem l2_opNorm_starOp_le {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (φ : Equiv.Perm (Fin (m + 1)) →* Equiv.Perm X) : ‖starOp φ‖ ≤ 1 := by
  rw [starOp]
  refine (norm_smul_le _ _).trans ?_
  have hsum : ‖∑ j : Fin m, permOp φ (Equiv.swap (Fin.castSucc j) (Fin.last m))‖ ≤ m := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin m, ‖permOp φ (Equiv.swap (Fin.castSucc j) (Fin.last m))‖
        ≤ ∑ _j : Fin m, (1 : ℝ) := Finset.sum_le_sum fun j _ => Matrix.l2_opNorm_permOp_le _ _
      _ = m := by simp
  rw [norm_inv, Complex.norm_natCast]
  calc ((m + 1 : ℕ) : ℝ)⁻¹ * ‖∑ j : Fin m, permOp φ (Equiv.swap (Fin.castSucc j) (Fin.last m))‖
      ≤ ((m + 1 : ℕ) : ℝ)⁻¹ * m := by gcongr
    _ ≤ 1 := by
      rw [inv_mul_le_iff₀ (by positivity)]
      push_cast
      linarith

/-- **Star spectra lie in `[-1, 1]`** (`05-replicas.tex`, line 697). -/
theorem abs_starValue_le_one (m : ℕ) (Q : Finset F)
    {p : IrrepLabel (Equiv.Perm (Fin (m + 1))) × IrrepLabel (Equiv.Perm (Fin m))}
    (hp : labelProj (subsystemPerm (m + 1) ι Q) p.1 *
      labelProj ((subsystemPerm (m + 1) ι Q).comp (firstCopies m)) p.2 ≠ 0) :
    |starValue p| ≤ 1 := by
  have h := (isOrthogonalResolution_branch (ι := ι) m Q).norm_le_l2_opNorm_hom
    (c := fun p => (starValue p : ℂ)) hp
  rw [← starOp_subsystemPerm_eq_hom, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.trans (l2_opNorm_starOp_le _)

/-- **Polynomial approximation of a function of the star operator** (`05-replicas.tex`,
lines 696–698): if `|φ - p| ≤ M` on `[-1, 1]`, then `‖φ(J_{Q,k}) - p(J_{Q,k})‖ ≤ M`. -/
theorem l2_opNorm_cfc_starOp_sub_aeval_le (m : ℕ) (Q : Finset F) (φ : ℝ → ℝ) (p : ℝ[X])
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |φ x - p.eval x| ≤ M) :
    ‖cfc φ (starOp (subsystemPerm (m + 1) ι Q)) -
        aeval (starOp (subsystemPerm (m + 1) ι Q)) p‖ ≤ M := by
  set hJ := isOrthogonalResolution_branch (ι := ι) m Q
  rw [starOp_subsystemPerm_eq_hom, hJ.cfc_hom (isHermitian_branch ι m Q), hJ.aeval_hom,
    ← map_sub]
  refine hJ.l2_opNorm_hom_le (isHermitian_branch ι m Q) hM0 fun q hq => ?_
  have h1 := abs_starValue_le_one m Q hq
  simp only [Pi.sub_apply]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hM _ (abs_le.mp h1)

/-- If `|p| ≤ M` on `[-1, 1]`, then `‖p(J_{Q,k})‖ ≤ M`. -/
theorem l2_opNorm_aeval_starOp_le (m : ℕ) (Q : Finset F) (p : ℝ[X]) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    ‖aeval (starOp (subsystemPerm (m + 1) ι Q)) p‖ ≤ M := by
  set hJ := isOrthogonalResolution_branch (ι := ι) m Q
  rw [starOp_subsystemPerm_eq_hom, hJ.aeval_hom]
  refine hJ.l2_opNorm_hom_le (isHermitian_branch ι m Q) hM0 fun q hq => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact hM _ (abs_le.mp (abs_starValue_le_one m Q hq))

theorem isHermitian_aeval_starOp (m : ℕ) (Q : Finset F) (p : ℝ[X]) :
    (aeval (starOp (subsystemPerm (m + 1) ι Q)) p).IsHermitian := by
  rw [starOp_subsystemPerm_eq_hom, (isOrthogonalResolution_branch m Q).aeval_hom]
  exact (isOrthogonalResolution_branch m Q).isHermitian_hom (isHermitian_branch ι m Q) _

theorem isHermitian_cfc_starOp (m : ℕ) (Q : Finset F) (φ : ℝ → ℝ) :
    (cfc φ (starOp (subsystemPerm (m + 1) ι Q))).IsHermitian := by
  rw [starOp_subsystemPerm_eq_hom, (isOrthogonalResolution_branch m Q).cfc_hom
    (isHermitian_branch ι m Q)]
  exact (isOrthogonalResolution_branch m Q).isHermitian_hom (isHermitian_branch ι m Q) _

end TensorPower
