/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.SchurSurprisal

/-!
# Entropy windows for the actual Schur labels

The selection argument in the OpenAI area-law manuscript,
`07-comparators.tex`, lines 255–273, combines concentration of the surprisal
with the exponential moment of its difference from the label observable.
The joint spectral projections permit both bounds to be applied to the
same label distribution, including density matrices with a kernel.
-/

open Matrix PermutationRepresentation Module
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  {φ : G →* Equiv.Perm X} {ρ : Matrix X X ℂ}

private noncomputable def jointWeight (hρ : ρ.PosSemidef)
    (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) : ℝ :=
  (p.1 : ℝ) * finrank ℂ
    (LinearMap.range (toLin' (hρ.isHermitian.spectralProj p.1 * labelProj φ p.2)))

private theorem jointWeight_nonneg (hρ : ρ.PosSemidef)
    (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) :
    0 ≤ jointWeight (φ := φ) hρ p :=
  mul_nonneg (eigenvalue_nonneg hρ p.1) (Nat.cast_nonneg _)

private theorem re_trace_mul_joint_hom (hρ : ρ.PosSemidef)
    (hinv : ∀ g, Commute (permOp φ g) ρ)
    (f : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℝ) :
    (ρ * (isOrthogonalResolution_joint hρ hinv).hom (fun p => (f p : ℂ))).trace.re =
      ∑ p, jointWeight (φ := φ) hρ p * f p := by
  let R := isOrthogonalResolution_joint hρ hinv
  have hρR : ρ = R.hom fun p => ((p.1 : ℝ) : ℂ) := by
    have h := joint_hom_fst hρ hinv id
    rw [Matrix.IsHermitian.cfc_id] at h
    exact h.symm
  have heq : ρ * R.hom (fun p => (f p : ℂ)) =
      R.hom ((fun p => ((p.1 : ℝ) : ℂ)) * (fun p => (f p : ℂ))) :=
    (congrArg (· * R.hom (fun p => (f p : ℂ))) hρR).trans (map_mul R.hom _ _).symm
  rw [heq, R.trace_hom]
  simp_rw [trace_joint hρ hinv]
  simp only [Pi.mul_apply, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.natCast_re, Complex.ofReal_im, Complex.natCast_im, mul_zero, sub_zero]
  unfold jointWeight
  apply Finset.sum_congr rfl
  intro p _
  ring

private theorem sum_jointWeight (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ g, Commute (permOp φ g) ρ) :
    ∑ p, jointWeight (φ := φ) hρ p = 1 := by
  have h := re_trace_mul_joint_hom hρ hinv (fun _ => 1)
  have hfun : (fun _ : hρ.isHermitian.eigenvalueSet × IrrepLabel G => ((1 : ℝ) : ℂ)) = 1 := rfl
  rw [hfun, map_one, Matrix.mul_one, htr, Complex.one_re] at h
  simpa only [mul_one] using h.symm

private theorem re_trace_surprisalTail_joint (hρ : ρ.PosSemidef)
    (hinv : ∀ g, Commute (permOp φ g) ρ) (a w : ℝ) :
    (ρ * cfc (fun t : ℝ => if w < |t - a| then 1 else 0) (-CFC.log ρ)).trace.re =
      ∑ p, jointWeight (φ := φ) hρ p *
        (if w < |-Real.log (p.1 : ℝ) - a| then 1 else 0) := by
  let f : ℝ → ℝ := fun t => if w < |t - a| then 1 else 0
  have hcomp : cfc f (-CFC.log ρ) = cfc (fun t => f (-Real.log t)) ρ := by
    rw [CFC.log, ← cfc_neg]
    exact (cfc_comp' f (fun t : ℝ => -Real.log t) ρ
      ((ρ.finite_real_spectrum.image _).continuousOn f)
      (ρ.finite_real_spectrum.continuousOn _) hρ.isHermitian.isSelfAdjoint).symm
  change (ρ * cfc f (-CFC.log ρ)).trace.re = _
  rw [hcomp, hρ.isHermitian.cfc_eq, ← joint_hom_fst hρ hinv]
  exact re_trace_mul_joint_hom hρ hinv _

end PermutationRepresentation

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  {φ : G →* Equiv.Perm X} {ρ : Matrix X X ℂ}

private theorem re_trace_exp_remainder_joint (hρ : ρ.PosSemidef)
    (hinv : ∀ g, Commute (permOp φ g) ρ) :
    (ρ * NormedSpace.exp ((1 / 2 : ℂ) • (-CFC.log ρ - labelEntropy φ))).trace.re =
      ∑ p, jointWeight (φ := φ) hρ p *
        Real.exp ((-Real.log (p.1 : ℝ) - Real.log p.2.dim) / 2) := by
  let R := isOrthogonalResolution_joint hρ hinv
  have hop : NormedSpace.exp ((1 / 2 : ℂ) • (-CFC.log ρ - labelEntropy φ)) =
      R.hom (fun p => (Real.exp ((-Real.log (p.1 : ℝ) - Real.log p.2.dim) / 2) : ℂ)) := by
    rw [neg_log_eq_joint_hom hρ hinv, labelEntropy_eq_joint_hom hρ hinv,
      ← map_sub, ← map_smul, R.exp_hom]
    congr 1
    funext p
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hop]
  exact re_trace_mul_joint_hom hρ hinv _

private theorem jointWeight_bad_label_le (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ g, Commute (permOp φ g) ρ) (a : ℝ) {w : ℝ} (hw : 0 ≤ w)
    (p : hρ.isHermitian.eigenvalueSet × IrrepLabel G) :
    jointWeight (φ := φ) hρ p *
        (if 2 * w < |Real.log p.2.dim - a| then 1 else 0) ≤
      jointWeight (φ := φ) hρ p *
          (if w < |-Real.log (p.1 : ℝ) - a| then 1 else 0) +
        Real.exp (-w / 2) * (jointWeight (φ := φ) hρ p *
          Real.exp ((-Real.log (p.1 : ℝ) - Real.log p.2.dim) / 2)) := by
  have hn := jointWeight_nonneg (φ := φ) hρ p
  by_cases hz : jointWeight (φ := φ) hρ p = 0
  · simp [hz]
  have hu : (p.1 : ℝ) ≠ 0 := by
    intro h
    apply hz
    simp [jointWeight, h]
  have hP : hρ.isHermitian.spectralProj p.1 * labelProj φ p.2 ≠ 0 := by
    intro h
    apply hz
    simp [jointWeight, h]
  have hpos := lt_of_le_of_ne (eigenvalue_nonneg hρ p.1) (Ne.symm hu)
  have hd : (0 : ℝ) < p.2.dim := by exact_mod_cast p.2.dim_pos
  have hlog := Real.log_nonpos (mul_nonneg hpos.le hd.le)
    (mul_dim_le_one_of_ne_zero hρ hinv htr p hP)
  rw [Real.log_mul hu hd.ne'] at hlog
  by_cases hb : 2 * w < |Real.log p.2.dim - a|
  · simp only [hb, ite_true, mul_one]
    by_cases ht : w < |-Real.log (p.1 : ℝ) - a|
    · simp only [ht, ite_true, mul_one]
      exact le_add_of_nonneg_right (by positivity)
    · simp only [ht, ite_false, mul_zero, zero_add]
      have ht' := abs_le.mp (le_of_not_gt ht)
      have hb' := lt_abs.mp hb
      have hdiff : w ≤ -Real.log (p.1 : ℝ) - Real.log p.2.dim := by
        rcases hb' with h | h <;> linarith
      have he : 1 ≤ Real.exp (-w / 2) *
          Real.exp ((-Real.log (p.1 : ℝ) - Real.log p.2.dim) / 2) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        linarith
      calc jointWeight (φ := φ) hρ p = jointWeight (φ := φ) hρ p * 1 := by ring
        _ ≤ jointWeight (φ := φ) hρ p * (Real.exp (-w / 2) *
            Real.exp ((-Real.log (p.1 : ℝ) - Real.log p.2.dim) / 2)) :=
          mul_le_mul_of_nonneg_left he hn
        _ = _ := by ring
  · simp only [hb, ite_false, mul_zero]
    positivity

end PermutationRepresentation

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  {φ : G →* Equiv.Perm X} {ρ : Matrix X X ℂ}

private theorem re_trace_labelObservable_joint (hρ : ρ.PosSemidef)
    (hinv : ∀ g, Commute (permOp φ g) ρ) (f : IrrepLabel G → ℝ) :
    (∑ l, f l * (ρ * labelProj φ l).trace.re) =
      ∑ p, jointWeight (φ := φ) hρ p * f p.2 := by
  have h := re_trace_mul_joint_hom hρ hinv (fun p => f p.2)
  rw [joint_hom_snd hρ hinv, labelObservable, Matrix.mul_sum, trace_sum,
    Complex.re_sum] at h
  simpa only [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using h

private theorem labelWindow_mass_ge (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ g, Commute (permOp φ g) ρ) (a : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    1 - (ρ * cfc (fun t : ℝ => if w < |t - a| then 1 else 0) (-CFC.log ρ)).trace.re -
        Real.exp (-w / 2) * (ρ * NormedSpace.exp
          ((1 / 2 : ℂ) • (-CFC.log ρ - labelEntropy φ))).trace.re ≤
      ∑ l, if |Real.log l.dim - a| ≤ 2 * w then (ρ * labelProj φ l).trace.re else 0 := by
  let good : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℝ :=
    fun p => if |Real.log p.2.dim - a| ≤ 2 * w then 1 else 0
  let bad : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℝ :=
    fun p => if 2 * w < |Real.log p.2.dim - a| then 1 else 0
  have hpartition : (∑ p, jointWeight (φ := φ) hρ p * good p) +
      (∑ p, jointWeight (φ := φ) hρ p * bad p) = 1 := by
    rw [← Finset.sum_add_distrib]
    convert sum_jointWeight hρ htr hinv using 1
    apply Finset.sum_congr rfl
    intro p _
    by_cases hg : |Real.log p.2.dim - a| ≤ 2 * w
    · simp [good, bad, hg, not_lt.mpr hg]
    · simp [good, bad, hg, lt_of_not_ge hg]
  have hbound := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) =>
    jointWeight_bad_label_le hρ htr hinv a hw p)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← re_trace_surprisalTail_joint hρ hinv a w,
    ← re_trace_exp_remainder_joint hρ hinv] at hbound
  have hgood := re_trace_labelObservable_joint hρ hinv
    (fun l => if |Real.log l.dim - a| ≤ 2 * w then 1 else 0)
  simp only [ite_mul, one_mul, zero_mul] at hgood
  rw [hgood]
  change _ ≤ ∑ p, jointWeight (φ := φ) hρ p * good p
  change (∑ p, jointWeight (φ := φ) hρ p * bad p) ≤ _ at hbound
  linarith

end PermutationRepresentation

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
  {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}

/-- A finite entropy-window criterion for an actual Schur sector.
The quantitative hypothesis is on the actual surprisal tail of the density matrix;
it is not a prescribed label distribution. This is the joint spectral selection
step in the OpenAI area-law manuscript, `07-comparators.tex`, lines 255–273,
`comparator:high-label`. Its independent-copy specialization removes this
finite tail criterion for all sufficiently large copy numbers. -/
theorem exists_labelProj_mass_entropy_window (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (hinv : ∀ σ, Commute (permOp (copyPerm Ω k) σ) ρ)
    (a : ℝ) {w : ℝ} (hw : 0 ≤ w)
    (hsmall : (ρ * cfc (fun t : ℝ => if w < |t - a| then 1 else 0)
        (-CFC.log ρ)).trace.re +
      (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ) * Real.exp (-w / 2) ≤ 1 / 2) :
    ∃ l : IrrepLabel (Equiv.Perm (Fin k)),
      (2 * (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ))⁻¹ ≤
        (ρ * labelProj (copyPerm Ω k) l).trace.re ∧
      |Real.log l.dim - a| ≤ 2 * w := by
  classical
  let m := fun l => (ρ * labelProj (copyPerm Ω k) l).trace.re
  let L := Finset.univ.filter fun l : IrrepLabel (Equiv.Perm (Fin k)) =>
    labelProj (copyPerm Ω k) l ≠ 0 ∧ |Real.log l.dim - a| ≤ 2 * w
  let N : ℝ := (((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ) : ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hm (l) : 0 ≤ m l :=
    (Complex.nonneg_iff.mp (hρ.trace_mul_nonneg
      ((isHermitian_labelProj _ l).posSemidef_of_mul_self
        (labelProj_mul_self _ l)))).1
  have hsum : 1 / 2 ≤ ∑ l ∈ L, m l := by
    have hwindow := PermutationRepresentation.labelWindow_mass_ge hρ htr hinv a hw
    have hmoment := (schurSurprisal hρ htr hinv).2.2.2 (1 / 2) (by norm_num)
    have hmoment' := mul_le_mul_of_nonneg_left hmoment (Real.exp_pos (-w / 2)).le
    norm_num at hmoment'
    have heq : (∑ l ∈ L, m l) =
        ∑ l, if |Real.log l.dim - a| ≤ 2 * w then m l else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hz : labelProj (copyPerm Ω k) l = 0
      · simp [m, hz]
      · simp [hz]
    rw [heq]
    change _ ≤ ∑ l, if |Real.log l.dim - a| ≤ 2 * w then m l else 0 at hwindow
    push_cast at hsmall
    linarith
  have hL : L.Nonempty := by
    obtain ⟨l, hl, _⟩ := (Finset.sum_pos_iff_of_nonneg (fun l _ => hm l)).mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hsum)
    exact ⟨l, hl⟩
  have hc : (L.card : ℝ) ≤ N := by
    apply le_trans (Nat.cast_le.mpr (Finset.card_le_card (show L ⊆
      Finset.univ.filter (fun l => labelProj (copyPerm Ω k) l ≠ 0) from
        fun l hl => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hl).2.1⟩)))
    dsimp only [N]
    exact_mod_cast card_labelProj_ne_zero_le Ω k
  obtain ⟨l, hl, hmL⟩ := Finset.exists_le_of_sum_le hL
    (f := fun _ => (2 * N)⁻¹) (g := m) (by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply le_trans (mul_le_mul_of_nonneg_right hc (by positivity))
      have hhalf : N * (2 * N)⁻¹ = (1 / 2 : ℝ) := by field_simp
      rwa [hhalf])
  exact ⟨l, hmL, (Finset.mem_filter.mp hl).2.2⟩

end TensorPower
