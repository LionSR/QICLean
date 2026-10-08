/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.UnitaryTwirl
import QICLean.Analysis.CfcConjugation
import QICLean.Representation.SchurSurprisal
import QICLean.Analysis.OrthogonalResolutionCfc

/-!
# Real powers of tensor powers

For a positive semidefinite `ρ` and `t ≥ 0`, `(ρ^{⊗k})^t = (ρ^t)^{⊗k}`. Both sides are
diagonal in the tensor products of the eigenvectors of `ρ`, with eigenvalues
`(∏_j λ_{x_j})^t = ∏_j λ_{x_j}^t`. This is used for the compensators `W_{R,k}^{-1} (ρ_R^t)^{⊗k}`
in the proof of Lemma 6.3 of the area-law paper (*A two-dimensional area law from a global
spectral gap*, `05-replicas.tex`, lines 535–551).

The proofs are written from the standard theory; no Lean source was adapted.

## Main declarations

* `TensorPower.tensorPow_diagonal`, `TensorPower.tensorPow_mem_unitaryGroup`.
* `TensorPower.posSemidef_tensorPow`, `TensorPower.tensorPow_rpow`.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

omit [Fintype Ω] in
theorem tensorPow_diagonal (d : Ω → ℂ) :
    tensorPow (k := k) (diagonal d) = diagonal fun x => ∏ j, d (x j) := by
  ext x y
  rw [tensorPow_apply, diagonal_apply]
  by_cases h : x = y
  · subst h; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [ite_eq_right_iff.mpr (fun h' => absurd h' h),
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])]

theorem tensorPow_mem_unitaryGroup {U : Matrix Ω Ω ℂ} (hU : U ∈ unitaryGroup Ω ℂ) :
    tensorPow (k := k) U ∈ unitaryGroup (Fin k → Ω) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_tensorPow, ← tensorPow_mul,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hU, tensorPow_one]

theorem tensorPow_conj (U A : Matrix Ω Ω ℂ) :
    tensorPow (k := k) (U * A * star U) =
      tensorPow (k := k) U * tensorPow A * star (tensorPow (k := k) U) := by
  rw [tensorPow_mul, tensorPow_mul, star_eq_conjTranspose, star_eq_conjTranspose,
    conjTranspose_tensorPow]

/-- Spectral form of a positive semidefinite matrix. -/
theorem eq_unitary_conj_diagonal {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) :
    ρ = (hρ.isHermitian.eigenvectorUnitary : Matrix Ω Ω ℂ) *
      diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) *
        star (hρ.isHermitian.eigenvectorUnitary : Matrix Ω Ω ℂ) := by
  conv_lhs => rw [hρ.isHermitian.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  rfl

theorem rpow_eq_unitary_conj_diagonal {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) (t : ℝ) :
    ρ ^ t = (hρ.isHermitian.eigenvectorUnitary : Matrix Ω Ω ℂ) *
      diagonal (fun i => ((hρ.isHermitian.eigenvalues i ^ t : ℝ) : ℂ)) *
        star (hρ.isHermitian.eigenvectorUnitary : Matrix Ω Ω ℂ) := by
  rw [CFC.rpow_eq_cfc_real hρ.nonneg, hρ.isHermitian.cfc_eq, IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply]
  rfl

set_option linter.unusedFintypeInType false in
theorem posSemidef_tensorPow {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) :
    (tensorPow (k := k) ρ).PosSemidef := by
  set U := (hρ.isHermitian.eigenvectorUnitary : Matrix Ω Ω ℂ)
  have hD : (diagonal fun x : Fin k → Ω =>
      ∏ j, (hρ.isHermitian.eigenvalues (x j) : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun x => by
      rw [← Complex.ofReal_prod]
      exact Complex.zero_le_real.mpr (Finset.prod_nonneg fun j _ => hρ.eigenvalues_nonneg _)
  rw [eq_unitary_conj_diagonal hρ, tensorPow_conj, tensorPow_diagonal]
  have := hD.conjTranspose_mul_mul_same (star (tensorPow (k := k) U))
  rwa [star_eq_conjTranspose (tensorPow U), conjTranspose_conjTranspose] at this

/-- **Real powers of tensor powers**: `(ρ^{⊗k})^t = (ρ^t)^{⊗k}` for `ρ ≥ 0`. -/
theorem tensorPow_rpow {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    tensorPow (k := k) (ρ ^ t) = (tensorPow (k := k) ρ) ^ t := by
  set U := (hρ.isHermitian.eigenvectorUnitary : Matrix Ω Ω ℂ)
  have hU : U ∈ unitaryGroup Ω ℂ := hρ.isHermitian.eigenvectorUnitary.2
  set ev := hρ.isHermitian.eigenvalues
  have hD : (diagonal fun x : Fin k → Ω => ((∏ j, ev (x j) : ℝ) : ℂ)).PosSemidef :=
    PosSemidef.diagonal fun x =>
      Complex.zero_le_real.mpr (Finset.prod_nonneg fun j _ => hρ.eigenvalues_nonneg _)
  have h1 : tensorPow (k := k) ρ = tensorPow (k := k) U *
      diagonal (fun x : Fin k → Ω => ((∏ j, ev (x j) : ℝ) : ℂ)) *
        star (tensorPow (k := k) U) := by
    rw [eq_unitary_conj_diagonal hρ, tensorPow_conj, tensorPow_diagonal]
    push_cast
    rfl
  rw [rpow_eq_unitary_conj_diagonal hρ, tensorPow_conj, tensorPow_diagonal, h1,
    rpow_conj_unitary hD t ⟨_, tensorPow_mem_unitaryGroup hU⟩, CFC.rpow_eq_cfc_real hD.nonneg,
    cfc_diagonal _ _ (Real.continuous_rpow_const ht).continuousOn]
  have e : (fun x : Fin k → Ω => ∏ j, ((ev (x j) ^ t : ℝ) : ℂ)) =
      fun x => (((∏ j, ev (x j)) ^ t : ℝ) : ℂ) := funext fun x => by
    rw [← Real.finsetProd_rpow _ _ fun j _ => hρ.eigenvalues_nonneg _, Complex.ofReal_prod]
  rw [← e]

end TensorPower

namespace TensorPower

open PermutationRepresentation
open scoped Matrix.Norms.L2Operator

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

theorem trace_tensorPow (A : Matrix Ω Ω ℂ) : (tensorPow (k := k) A).trace = A.trace ^ k := by
  simp only [trace, diag_apply, tensorPow_apply]
  rw [show (∑ i, A i i) ^ k = ∏ _j : Fin k, ∑ a, A a a by simp, Fintype.prod_sum]

/-- **The compensator bound** (`05-replicas.tex`, lines 535–551): if `ρ` is a density matrix
and the label weights satisfy `w_λ^{-1} ≤ M d_λ^t` on the labels occurring in `Ω^{⊗k}`, then
`‖(∑_λ w_λ^{-1} π^λ) (ρ^t)^{⊗k}‖ ≤ M`. The eigenvalues `u` of `ρ^{⊗k}` in the `λ` block
satisfy `u d_λ ≤ 1`. -/
theorem l2_opNorm_labelObservable_mul_tensorPow_rpow_le {ρ : Matrix Ω Ω ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) {t : ℝ} (ht : 0 ≤ t) {w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ}
    (hw : ∀ l, 0 < w l) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ l, labelProj (copyPerm Ω k) l ≠ 0 → (w l)⁻¹ ≤ M * (l.dim : ℝ) ^ t) :
    ‖labelObservable (copyPerm Ω k) (fun l => (w l)⁻¹) * tensorPow (k := k) (ρ ^ t)‖ ≤ M := by
  set ρ' := tensorPow (k := k) ρ
  have hρ' : ρ'.PosSemidef := posSemidef_tensorPow hρ
  have hinv : ∀ g, Commute (permOp (copyPerm Ω k) g) ρ' := fun g =>
    commute_permOp_copyPerm_tensorPow ρ g
  have htr' : ρ'.trace = 1 := by rw [trace_tensorPow, htr, one_pow]
  set R := isOrthogonalResolution_joint hρ' hinv
  have h1 : tensorPow (k := k) (ρ ^ t) = R.hom fun p => (((p.1 : ℝ) ^ t : ℝ) : ℂ) := by
    rw [tensorPow_rpow hρ ht, CFC.rpow_eq_cfc_real hρ'.nonneg, hρ'.isHermitian.cfc_eq,
      ← joint_hom_fst hρ' hinv]
  have h2 : labelObservable (copyPerm Ω k) (fun l => (w l)⁻¹) =
      R.hom fun p => (((w p.2)⁻¹ : ℝ) : ℂ) := (joint_hom_snd hρ' hinv _).symm
  rw [h1, h2, ← map_mul]
  refine R.l2_opNorm_hom_le (isHermitian_joint hρ' hinv) hM fun p hp => ?_
  have hl : labelProj (copyPerm Ω k) p.2 ≠ 0 := fun h0 => hp (by rw [h0, Matrix.mul_zero])
  have hud := mul_dim_le_one_of_ne_zero hρ' hinv htr' p hp
  have hu := eigenvalue_nonneg hρ' p.1
  have hd : (0 : ℝ) < p.2.dim := by exact_mod_cast p.2.dim_pos
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (inv_pos.mpr (hw _)), abs_of_nonneg (Real.rpow_nonneg hu t)]
  calc (w p.2)⁻¹ * (p.1 : ℝ) ^ t ≤ M * (p.2.dim : ℝ) ^ t * (p.1 : ℝ) ^ t :=
        mul_le_mul_of_nonneg_right (hb _ hl) (Real.rpow_nonneg hu t)
    _ = M * ((p.1 : ℝ) * p.2.dim) ^ t := by
        rw [Real.mul_rpow hu hd.le]; ring
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one (mul_nonneg hu hd.le) hud ht) hM
    _ = M := mul_one M

end TensorPower
