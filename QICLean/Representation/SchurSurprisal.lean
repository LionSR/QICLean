/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.PosSemidefSupport
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

/-- The scalar estimate behind the moment bound: for `0 < t ≤ 1` and `b ≤ 1`,
`t · exp(-b log t) ≤ 1`. -/
theorem _root_.Real.mul_exp_neg_mul_log_le_one {t b : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hb1 : b ≤ 1) :
    t * Real.exp (-(b * Real.log t)) ≤ 1 := by
  rw [← Real.exp_log ht, Real.log_exp, ← Real.exp_add]
  apply Real.exp_le_one_iff.mpr
  have := Real.log_nonpos ht.le ht1
  nlinarith

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
  have h := hρ.isHermitian.isOrthogonalResolution_spectralProj.prod_hom_fst
    (isOrthogonalResolution_labelProj φ)
    (isOrthogonalResolution_joint hρ hinv) (fun u => (f u : ℂ))
  exact h.trans (hρ.isHermitian.cfc_eq_hom f).symm

/-- Functions of the label factor of the joint resolution. -/
theorem joint_hom_snd (f : IrrepLabel G → ℝ) :
    (isOrthogonalResolution_joint hρ hinv).hom (fun p => (f p.2 : ℂ)) = labelObservable φ f := by
  have h := hρ.isHermitian.isOrthogonalResolution_spectralProj.prod_hom_snd
    (isOrthogonalResolution_labelProj φ)
    (isOrthogonalResolution_joint hρ hinv) (fun l => (f l : ℂ))
  exact h.trans (labelObservable_eq_hom φ f).symm

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
      rw [Matrix.IsHermitian.cfc_id] at this
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

/-- The support projection of `ρ` through the joint resolution. -/
theorem supportProj_eq_joint_hom :
    hρ.supportProj = (isOrthogonalResolution_joint hρ hinv).hom
      (fun p => ((if (p.1 : ℝ) ≠ 0 then 1 else 0 : ℝ) : ℂ)) := by
  rw [joint_hom_fst hρ hinv (fun x => if x ≠ 0 then 1 else 0), Matrix.IsHermitian.cfc_form,
    PosSemidef.supportProj,
    IsHermitian.supportProj]
  congr 3
  funext i
  split_ifs <;> simp

open scoped Matrix.Norms.L2Operator in
/-- The operator `L_ρ = -log ρ` (zero on the kernel) through the joint resolution. -/
theorem neg_log_eq_joint_hom :
    -CFC.log ρ = (isOrthogonalResolution_joint hρ hinv).hom
      (fun p => ((-Real.log (p.1 : ℝ) : ℝ) : ℂ)) := by
  rw [CFC.log, Matrix.IsHermitian.cfc_eq hρ.isHermitian, ← joint_hom_fst hρ hinv, ← map_neg]
  congr 1
  funext p
  push_cast
  rfl

theorem labelEntropy_eq_joint_hom :
    labelEntropy φ = (isOrthogonalResolution_joint hρ hinv).hom
      (fun p => ((Real.log p.2.dim : ℝ) : ℂ)) :=
  (joint_hom_snd hρ hinv _).symm

open scoped Matrix.Norms.L2Operator in
/-- **`F ≤ L_ρ` on the support of `ρ`** (`05-replicas.tex`, lines 126–127 and 223–226):
for a permutation-invariant density matrix `ρ`, the compression of the label observable
to the support of `ρ` is at most `-log ρ`. -/
theorem supportProj_mul_labelEntropy_mul_supportProj_le (htr : ρ.trace = 1) :
    hρ.supportProj * labelEntropy φ * hρ.supportProj ≤ -CFC.log ρ := by
  set R := isOrthogonalResolution_joint hρ hinv
  rw [Matrix.le_iff, supportProj_eq_joint_hom hρ hinv, labelEntropy_eq_joint_hom hρ hinv,
    neg_log_eq_joint_hom hρ hinv, ← map_mul, ← map_mul, ← map_sub]
  have hfun : ((fun p : hρ.isHermitian.eigenvalueSet × IrrepLabel G =>
        ((-Real.log (p.1 : ℝ) : ℝ) : ℂ)) -
      (fun p => ((if (p.1 : ℝ) ≠ 0 then 1 else 0 : ℝ) : ℂ)) *
        (fun p => ((Real.log p.2.dim : ℝ) : ℂ)) *
        (fun p => ((if (p.1 : ℝ) ≠ 0 then 1 else 0 : ℝ) : ℂ))) =
      fun p => (((-Real.log (p.1 : ℝ)) -
        (if (p.1 : ℝ) ≠ 0 then Real.log p.2.dim else 0) : ℝ) : ℂ) := by
    funext p
    simp only [Pi.sub_apply, Pi.mul_apply]
    split_ifs <;> push_cast <;> ring
  rw [hfun]
  refine R.posSemidef_hom_of_ne_zero (isHermitian_joint hρ hinv) fun p hp => ?_
  by_cases hu : (p.1 : ℝ) = 0
  · simp [hu]
  · simp only [ne_eq, hu, not_false_eq_true, ite_true]
    have hpos : 0 < (p.1 : ℝ) := lt_of_le_of_ne (eigenvalue_nonneg hρ p.1) (Ne.symm hu)
    have hd : (0 : ℝ) < p.2.dim := by exact_mod_cast p.2.dim_pos
    have h1 := mul_dim_le_one_of_ne_zero hρ hinv htr p hp
    have h2 : Real.log ((p.1 : ℝ) * p.2.dim) ≤ 0 :=
      Real.log_nonpos (mul_nonneg hpos.le hd.le) h1
    rw [Real.log_mul hpos.ne' hd.ne'] at h2
    linarith

open scoped Matrix.Norms.L2Operator in
/-- **Surprisal moment bound, general form** (`05-replicas.tex`, lines 128–130 and
227–235). For a permutation-invariant density matrix `ρ` and `b ≤ 1` (the paper
states `0 ≤ b ≤ 1`; the lower bound is not needed), `Tr ρ exp(b (L_ρ - F)) ≤ ∑_λ m_λ`. -/
theorem re_trace_mul_exp_le_sum_multiplicity (htr : ρ.trace = 1) {b : ℝ}
    (hb1 : b ≤ 1) :
    (ρ * NormedSpace.exp ((b : ℂ) • (-CFC.log ρ - labelEntropy φ))).trace.re ≤
      ∑ l, multiplicity φ l := by
  set R := isOrthogonalResolution_joint hρ hinv
  set n : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℕ := fun p => finrank ℂ
    (LinearMap.range (toLin' (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2)))
  set w : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℝ := fun p =>
    (p.1 : ℝ) * Real.exp (b * (-Real.log (p.1 : ℝ) - Real.log p.2.dim))
  have hρR : ρ = R.hom fun q => ((q.1 : ℝ) : ℂ) := by
    have := joint_hom_fst hρ hinv id
    rw [Matrix.IsHermitian.cfc_id] at this
    exact this.symm
  have hop : ρ * NormedSpace.exp ((b : ℂ) • (-CFC.log ρ - labelEntropy φ)) =
      R.hom fun p => ((w p : ℝ) : ℂ) := by
    rw [neg_log_eq_joint_hom hρ hinv, labelEntropy_eq_joint_hom hρ hinv, ← map_sub,
      ← map_smul, R.exp_hom]
    refine (congrArg (· * _) hρR).trans ?_
    rw [← map_mul]
    congr 1
    funext p
    simp only [w, Pi.mul_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    rfl
  -- The trace is `∑ w n`.
  have htr' : (ρ * NormedSpace.exp ((b : ℂ) • (-CFC.log ρ - labelEntropy φ))).trace.re =
      ∑ p, w p * n p := by
    rw [hop, R.trace_hom]
    simp_rw [trace_joint hρ hinv]
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.natCast_re,
      Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero]
    rfl
  -- Each term is at most `n / d`.
  have hterm : ∀ p, w p * n p ≤ (n p : ℝ) / p.2.dim := by
    intro p
    have hd : (0 : ℝ) < p.2.dim := by exact_mod_cast p.2.dim_pos
    by_cases hn : n p = 0
    · simp [hn]
    have hp : hρ.isHermitian.spectralProj p.1 * labelProj φ p.2 ≠ 0 := by
      intro h0
      apply hn
      change finrank ℂ (LinearMap.range (toLin' (hρ.isHermitian.spectralProj p.1 *
        labelProj φ p.2))) = 0
      rw [h0, map_zero, LinearMap.range_zero, finrank_bot]
    rw [le_div_iff₀ hd, mul_right_comm]
    refine le_of_le_of_eq (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) (one_mul _)
    by_cases hu : (p.1 : ℝ) = 0
    · simp [w, hu]
    have hpos : 0 < (p.1 : ℝ) := lt_of_le_of_ne (eigenvalue_nonneg hρ p.1) (Ne.symm hu)
    have h1 := mul_dim_le_one_of_ne_zero hρ hinv htr p hp
    have := Real.mul_exp_neg_mul_log_le_one (mul_pos hpos hd) h1 hb1
    rw [Real.log_mul hpos.ne' hd.ne'] at this
    calc w p * p.2.dim = (p.1 : ℝ) * p.2.dim *
          Real.exp (-(b * (Real.log (p.1 : ℝ) + Real.log p.2.dim))) := by
          simp only [w]; ring_nf
      _ ≤ 1 := this
  -- `∑_u n(u, λ) = d_λ m_λ`.
  have hsum : ∀ l : IrrepLabel G, ∑ u, n (u, l) = l.dim * multiplicity φ l := by
    intro l
    have h := trace_labelProj φ l
    rw [← one_mul (labelProj φ l), ← hρ.isHermitian.isOrthogonalResolution_spectralProj.sum_eq,
      Finset.sum_mul, trace_sum] at h
    simp_rw [trace_joint hρ hinv (_, l)] at h
    exact_mod_cast h
  rw [htr']
  calc ∑ p, w p * n p ≤ ∑ p, (n p : ℝ) / p.2.dim := Finset.sum_le_sum fun p _ => hterm p
    _ = ∑ l, ((∑ u, n (u, l) : ℕ) : ℝ) / l.dim := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        push_cast
        simp_rw [Finset.sum_div]
    _ = ∑ l, (multiplicity φ l : ℝ) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        have hd : (l.dim : ℝ) ≠ 0 := by exact_mod_cast l.dim_pos.ne'
        rw [hsum l]
        push_cast
        field_simp
    _ = ((∑ l, multiplicity φ l : ℕ) : ℝ) := by push_cast; rfl

end PermutationRepresentation

namespace TensorPower

open PermutationRepresentation

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ} {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}

open scoped Matrix.Norms.L2Operator in
/-- **Lemma 6.1(5)** (`05-replicas.tex`, lines 124–130, proof lines 223–235). Let `ρ` be
any permutation-invariant density matrix on `Q^{⊗k}` with `q = dim Q`, and let
`L_ρ = -log ρ` on its support. Then `F_Q` commutes with `ρ`, `0 ≤ F_Q`, `F_Q ≤ L_ρ` on the
support of `ρ`, and for `0 ≤ b ≤ 1` (indeed for every `b ≤ 1`),
`Tr ρ exp(b (L_ρ - F_Q)) ≤ (k+1)^{q²}`. The bound is uniform over all such `ρ`. -/
theorem schurSurprisal (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ σ, Commute (permOp (copyPerm Ω k) σ) ρ) :
    Commute (labelEntropy (copyPerm Ω k)) ρ ∧ (labelEntropy (copyPerm Ω k)).PosSemidef ∧
      hρ.supportProj * labelEntropy (copyPerm Ω k) * hρ.supportProj ≤ -CFC.log ρ ∧
      ∀ b : ℝ, b ≤ 1 →
        (ρ * NormedSpace.exp ((b : ℂ) • (-CFC.log ρ - labelEntropy (copyPerm Ω k)))).trace.re ≤
          ((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) :=
  ⟨commute_labelEntropy hinv, posSemidef_labelEntropy _,
    supportProj_mul_labelEntropy_mul_supportProj_le hρ hinv htr,
    fun _ hb1 => (re_trace_mul_exp_le_sum_multiplicity hρ hinv htr hb1).trans
      (by exact_mod_cast sum_multiplicity_le Ω k)⟩

end TensorPower
