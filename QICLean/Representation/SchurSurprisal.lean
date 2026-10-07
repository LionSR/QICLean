/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.CommutantDimension

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# The label observable bounds the surprisal of permutation-invariant states

This file proves part 5 of Lemma 6.1 (`lem:schur`) of the area-law paper
(*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
lines 124–130, with proof at lines 223–235). Let `ρ` be **any** permutation-invariant
density matrix on `Q^{⊗k}`, not necessarily a tensor power, and let `L_ρ = -log ρ` on
its support. Then the label observable `F_Q = ∑_λ (log d_λ) π^λ` commutes with `ρ`,
`0 ≤ F_Q ≤ L_ρ` on the support of `ρ`, and for `0 ≤ b ≤ 1`
`Tr ρ exp(b (L_ρ - F_Q)) ≤ (k+1)^{q²}`, where `q = dim Q`.

The polynomial is explicit and does not depend on `ρ`. The general statements hold for
every permutation representation of a finite group, with the polynomial replaced by the
total multiplicity `∑_λ m_λ`.

## Method

The spectral projections `E_u` of `ρ` commute with the label projectors `π^λ`, so the
products `E_u π^λ` form an orthogonal resolution of the identity. Every operator in the
statement is a function of this resolution, and the trace is the weighted sum
`∑_{u,λ} w(u,λ) tr(E_u π^λ)`. The range of `E_u π^λ` is an invariant subspace of the
`λ`-isotypic component, so when nonzero its dimension is at least `d_λ`; with `tr ρ = 1`
this gives `u d_λ ≤ 1`, the eigenvalue repetition of the paper.

Here `log 0 = 0`, so `-CFC.log ρ` is `-log ρ` on the support of `ρ` and zero on its
kernel, which is the paper's `L_ρ`.

## Main declarations

* `PermutationRepresentation.mul_dim_le_one_of_ne_zero` — the eigenvalue repetition.
* `PermutationRepresentation.posSemidef_labelEntropy` — `0 ≤ F`.
* `PermutationRepresentation.supportProj_mul_labelEntropy_mul_supportProj_le` —
  `F ≤ L_ρ` on the support of `ρ`.
* `PermutationRepresentation.re_trace_mul_exp_le_sum_multiplicity` — the moment bound.
* `TensorPower.re_trace_mul_exp_le` — **Lemma 6.1(5)** on `(ℂ^q)^{⊗k}`.
-/

open MonoidAlgebra Matrix Module
open scoped ComplexOrder MatrixOrder

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  (φ : G →* Equiv.Perm X)

/-- The label projectors form an orthogonal resolution of the identity. -/
theorem isOrthogonalResolution_labelProj :
    IsOrthogonalResolution fun l : IrrepLabel G => labelProj φ l where
  mul_eq := labelProj_mul_labelProj φ
  sum_eq := sum_labelProj φ

theorem labelObservable_eq_hom (f : IrrepLabel G → ℝ) :
    labelObservable φ f = (isOrthogonalResolution_labelProj φ).hom fun l => (f l : ℂ) := by
  rw [IsOrthogonalResolution.hom_apply, labelObservable]

/-- `0 ≤ F`: the label observable is positive semidefinite (`05-replicas.tex`,
line 127). -/
theorem posSemidef_labelEntropy : (labelEntropy φ).PosSemidef := by
  rw [labelEntropy, labelObservable_eq_hom]
  exact (isOrthogonalResolution_labelProj φ).posSemidef_hom (isHermitian_labelProj φ)
    fun l => Real.log_nonneg (by exact_mod_cast l.dim_pos)

variable {φ} {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef) (hinv : ∀ g, Commute (permOp φ g) ρ)
include hρ hinv

omit hρ in
/-- The label observable commutes with every permutation-invariant matrix
(`05-replicas.tex`, line 126). -/
theorem commute_labelEntropy : Commute (labelEntropy φ) ρ :=
  commute_labelObservable_of_forall_commute φ hinv _

theorem commute_spectralProj_labelProj (u : ℝ) (l : IrrepLabel G) :
    Commute (hρ.isHermitian.spectralProj u) (labelProj φ l) :=
  hρ.isHermitian.commute_spectralProj (commute_labelProj_of_forall_commute φ hinv l).symm u

/-- The joint resolution `E_u π^λ` of a permutation-invariant positive semidefinite
matrix and the label projectors. -/
theorem isOrthogonalResolution_joint :
    IsOrthogonalResolution fun p : hρ.isHermitian.eigenvalueSet × IrrepLabel G =>
      hρ.isHermitian.spectralProj p.1 * labelProj φ p.2 :=
  hρ.isHermitian.isOrthogonalResolution_spectralProj.prod (isOrthogonalResolution_labelProj φ)
    fun u l => commute_spectralProj_labelProj hρ hinv u l

/-- The joint projections are Hermitian. -/
theorem isHermitian_joint (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) :
    (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2).IsHermitian := by
  rw [IsHermitian, conjTranspose_mul, (isHermitian_labelProj φ p.2).eq,
    (hρ.isHermitian.isHermitian_spectralProj p.1).eq]
  exact (commute_spectralProj_labelProj hρ hinv p.1 p.2).eq.symm

/-- Functions of the eigenvalue factor of the joint resolution. -/
theorem joint_hom_fst (f : ℝ → ℝ) :
    (isOrthogonalResolution_joint hρ hinv).hom (fun p => (f p.1 : ℂ)) = hρ.isHermitian.cfc f := by
  rw [hρ.isHermitian.cfc_eq_hom, IsOrthogonalResolution.hom_apply,
    IsOrthogonalResolution.hom_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.smul_sum, ← Finset.mul_sum, sum_labelProj, mul_one]

/-- Functions of the label factor of the joint resolution. -/
theorem joint_hom_snd (f : IrrepLabel G → ℝ) :
    (isOrthogonalResolution_joint hρ hinv).hom (fun p => (f p.2 : ℂ)) = labelObservable φ f := by
  rw [labelObservable, IsOrthogonalResolution.hom_apply, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp_rw [← Finset.smul_sum, ← Finset.sum_mul, hρ.isHermitian.isOrthogonalResolution_spectralProj.sum_eq,
    one_mul]

/-- The trace of a joint projection is the dimension of its range. -/
theorem trace_joint (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) :
    (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2).trace =
      finrank ℂ (LinearMap.range (toLin' (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2))) :=
  trace_eq_finrank_range_of_mul_self ((isOrthogonalResolution_joint hρ hinv).mul_self p)

/-- A nonzero joint projection has rank at least `d_λ`: its range is an invariant
subspace of the `λ`-isotypic component. -/
theorem dim_le_finrank_joint (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G)
    (hp : hρ.isHermitian.spectralProj p.1 * labelProj φ p.2 ≠ 0) :
    p.2.dim ≤ finrank ℂ
      (LinearMap.range (toLin' (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2))) := by
  set P := hρ.isHermitian.spectralProj p.1 * labelProj φ p.2
  have hPg : ∀ g, Commute (permOp φ g) P := fun g =>
    (((hρ.isHermitian.commute_spectralProj (hinv g).symm p.1).symm).mul_right
      (commute_labelProj_permOp φ p.2 g).symm)
  refine dim_le_finrank_of_invariant φ p.2 (fun g w hw => ?_) (fun w hw => ?_) ?_
  · obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
    refine LinearMap.mem_range.mpr ⟨permOp φ g *ᵥ v, ?_⟩
    simp only [toLin'_apply, mulVec_mulVec, (hPg g).eq]
  · obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hw
    simp only [toLin'_apply, mulVec_mulVec, P]
    rw [← mul_assoc, ← (commute_spectralProj_labelProj hρ hinv p.1 p.2).eq, mul_assoc,
      labelProj_mul_self, (commute_spectralProj_labelProj hρ hinv p.1 p.2).eq]
  · rw [Ne, LinearMap.range_eq_bot, ← map_zero toLin', toLin'.injective.eq_iff]
    exact hp

omit [Fintype G] hinv in
theorem eigenvalue_nonneg (u : hρ.isHermitian.eigenvalueSet) : 0 ≤ (u : ℝ) := by
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp u.2
  rw [← hi]
  exact hρ.eigenvalues_nonneg i

/-- **Eigenvalue repetition** (`05-replicas.tex`, lines 223–226). If `tr ρ = 1` and the
eigenvalue `u` of `ρ` occurs in the `λ`-isotypic component, then `u d_λ ≤ 1`. -/
theorem mul_dim_le_one_of_ne_zero (htr : ρ.trace = 1)
    (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G)
    (hp : hρ.isHermitian.spectralProj p.1 * labelProj φ p.2 ≠ 0) :
    (p.1 : ℝ) * p.2.dim ≤ 1 := by
  set R := isOrthogonalResolution_joint hρ hinv
  set n : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℕ := fun p => finrank ℂ
    (LinearMap.range (toLin' (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2)))
  -- `tr ρ = ∑ u n(u, λ)`.
  have htrace : ∑ q, (q.1 : ℝ) * n q = 1 := by
    have h1 : ρ = R.hom fun q => ((q.1 : ℝ) : ℂ) := by
      have := joint_hom_fst hρ hinv id
      rw [cfc_id] at this
      exact this.symm
    have h2 := congrArg Matrix.trace h1
    rw [htr, IsOrthogonalResolution.trace_hom] at h2
    simp_rw [trace_joint hρ hinv] at h2
    have h3 := congrArg Complex.re h2
    simp only [Complex.one_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero] at h3
    exact h3.symm
  have hle : (p.1 : ℝ) * n p ≤ 1 := by
    rw [← htrace]
    exact Finset.single_le_sum (f := fun q => (q.1 : ℝ) * n q)
      (fun q _ => mul_nonneg (eigenvalue_nonneg hρ q.1) (Nat.cast_nonneg _))
      (Finset.mem_univ p)
  calc (p.1 : ℝ) * p.2.dim ≤ (p.1 : ℝ) * n p :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast dim_le_finrank_joint hρ hinv p hp)
          (eigenvalue_nonneg hρ p.1)
    _ ≤ 1 := hle

end PermutationRepresentation
