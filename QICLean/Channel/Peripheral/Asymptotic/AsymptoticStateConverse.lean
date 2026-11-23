/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.Asymptotic.AsymptoticStateConvergence
import QICLean.Analysis.FunctionalCalculus.TraceCFC

/-!
# The converse comparison for convergence towards asymptotic states

This file formalizes the converse half of Wolf's comparison between trace-norm convergence
of states and Hilbert--Schmidt operator-norm convergence: Equations (8.113) and (8.117).

Every matrix `X` is a combination `X = P₀ - P₁ + i P₂ - i P₃` of four positive semidefinite
matrices with `‖P_j‖₂ ≤ ‖X‖₂`: the positive and negative parts of the Hermitian and
skew-Hermitian parts of `X`. Together with `‖·‖₂ ≤ ‖·‖₁` this bounds the Hilbert--Schmidt
`2 → 2` norm of a superoperator by four times its trace-norm action on positive matrices of
Hilbert--Schmidt norm at most one (Equation (8.117)). Such a matrix has trace at most `√d`, so
after normalization to a density operator one obtains Equation (8.113).

## Main results

* `Matrix.exists_four_posSemidef_frobenius_norm_le`: the four-positive-parts decomposition
  with Hilbert--Schmidt control.
* `Matrix.hilbertSchmidtOperatorNorm_le_four_mul_of_posSemidef`: Equation (8.117).
* `Matrix.hilbertSchmidtOperatorNorm_pow_sub_le_of_forall_traceNormAsymptoticDistance_le`:
  Equation (8.113), for every upper bound of the asymptotic distances.
* `Matrix.hilbertSchmidtOperatorNorm_pow_sub_le_sSup_traceNormAsymptoticDistance`:
  Equation (8.113) with the supremum over density operators.
* `Matrix.transferMatrix_l2_opNorm_pow_sub_le_sSup_traceNormAsymptoticDistance`:
  Equation (8.113) with Wolf's transfer-matrix norm.

## References

Michael M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8,
Proposition "Convergence towards asymptotic states", Equations (8.112)--(8.117);
local source `Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1319--1364.
-/

open scoped Matrix Matrix.Norms.Frobenius ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A bound on the action of a superoperator in the Hilbert--Schmidt norm bounds its
Hilbert--Schmidt `2 → 2` operator norm. -/
theorem hilbertSchmidtOperatorNorm_le_of_forall {α β : Type*} [Fintype α] [Fintype β]
    (S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ X, ‖S X‖ ≤ M * ‖X‖) : hilbertSchmidtOperatorNorm S ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x ↦ ?_
  have hx := h ((frobeniusEquivEuclidean α α).symm x)
  have happ := frobeniusEuclideanMap_apply S ((frobeniusEquivEuclidean α α).symm x)
  rw [LinearIsometryEquiv.apply_symm_apply] at happ
  rw [LinearMap.coe_toContinuousLinearMap', happ, LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using hx

/-- The Hilbert--Schmidt norm of `f(H)` for Hermitian `H` is `(∑ f(λ_i)²)^{1/2}`. -/
private theorem IsHermitian.frobenius_norm_cfc_sq {H : Mat} (hH : H.IsHermitian)
    (f : ℝ → ℝ) : ‖cfc f H‖ ^ 2 = ∑ i, f (hH.eigenvalues i) ^ 2 := by
  have hsa : IsSelfAdjoint (cfc f H) := _root_.cfc_predicate f H
  have hcont : ContinuousOn f (spectrum ℝ H) := H.finite_real_spectrum.continuousOn _
  rw [← trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq,
    show (cfc f H)ᴴ = cfc f H from hsa.isHermitian.eq,
    ← _root_.cfc_mul f f H hcont hcont, hH.cfc_eq]
  have h := hH.trace_cfc_eq_sum_re (fun x ↦ f x * f x)
  simp only [RCLike.re_to_complex] at h
  rw [h]
  simp only [pow_two]

/-- A function with `|f x| ≤ |x|` does not increase the Hilbert--Schmidt norm of a Hermitian
matrix under the functional calculus. -/
private theorem IsHermitian.frobenius_norm_cfc_le {H : Mat} (hH : H.IsHermitian)
    {f : ℝ → ℝ} (hf : ∀ x, |f x| ≤ |x|) : ‖cfc f H‖ ≤ ‖H‖ := by
  have hsq : ‖cfc f H‖ ^ 2 ≤ ‖H‖ ^ 2 := by
    have hid := hH.frobenius_norm_cfc_sq id
    rw [_root_.cfc_id ℝ H] at hid
    rw [hH.frobenius_norm_cfc_sq f, hid]
    exact Finset.sum_le_sum fun i _ ↦ sq_le_sq.mpr (hf _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- A Hermitian matrix is the difference of two positive semidefinite matrices whose
Hilbert--Schmidt norms are at most its own. -/
private theorem IsHermitian.exists_posSemidef_sub {H : Mat} (hH : H.IsHermitian) :
    ∃ P N : Mat, P.PosSemidef ∧ N.PosSemidef ∧ ‖P‖ ≤ ‖H‖ ∧ ‖N‖ ≤ ‖H‖ ∧ H = P - N := by
  refine ⟨cfc (fun x : ℝ ↦ max x 0) H, cfc (fun x : ℝ ↦ max (-x) 0) H, ?_, ?_, ?_, ?_, ?_⟩
  · exact nonneg_iff_posSemidef.mp (_root_.cfc_nonneg fun x _ ↦ le_max_right _ _)
  · exact nonneg_iff_posSemidef.mp (_root_.cfc_nonneg fun x _ ↦ le_max_right _ _)
  · refine hH.frobenius_norm_cfc_le fun x ↦ ?_
    rcases le_total x 0 with h | h
    · simp [max_eq_right h]
    · simp [max_eq_left h]
  · refine hH.frobenius_norm_cfc_le fun x ↦ ?_
    rcases le_total x 0 with h | h
    · simp [max_eq_left (neg_nonneg.mpr h), abs_neg]
    · simp [max_eq_right (neg_nonpos.mpr h)]
  · rw [← _root_.cfc_sub (fun x : ℝ ↦ max x 0) (fun x : ℝ ↦ max (-x) 0) H]
    conv_lhs => rw [← _root_.cfc_id' ℝ H]
    refine _root_.cfc_congr fun x _ ↦ ?_
    rcases le_total x 0 with h | h
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]

/-- **Four positive parts with Hilbert--Schmidt control.** Every matrix is
`X = P₀ - P₁ + i P₂ - i P₃` with positive semidefinite `P_j` and `‖P_j‖₂ ≤ ‖X‖₂`. The `P_j` are
the positive and negative parts of the Hermitian and skew-Hermitian parts of `X`.

Source: Wolf, proof of Equation (8.117); local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1356--1361. -/
theorem exists_four_posSemidef_frobenius_norm_le (X : Mat) :
    ∃ P : Fin 4 → Mat, (∀ j, (P j).PosSemidef ∧ ‖P j‖ ≤ ‖X‖) ∧
      X = P 0 - P 1 + Complex.I • P 2 - Complex.I • P 3 := by
  let H : Mat := (1 / 2 : ℂ) • (X + Xᴴ)
  let K : Mat := (1 / (2 * Complex.I)) • (X - Xᴴ)
  have hHerm : H.IsHermitian := by
    simp only [IsHermitian, H, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose]
    rw [add_comm]
    congr 1
    simp
  have hKerm : K.IsHermitian := by
    simp only [IsHermitian, K, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose]
    have hstar : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
      simp
    rw [hstar, neg_smul, ← smul_neg, neg_sub]
  have hnormH : ‖H‖ ≤ ‖X‖ := by
    calc
      ‖H‖ ≤ ‖(1 / 2 : ℂ)‖ * ‖X + Xᴴ‖ := norm_smul_le _ _
      _ ≤ ‖(1 / 2 : ℂ)‖ * (‖X‖ + ‖Xᴴ‖) := by gcongr; exact norm_add_le _ _
      _ = ‖X‖ := by rw [frobenius_norm_conjTranspose]; norm_num; ring
  have hnormK : ‖K‖ ≤ ‖X‖ := by
    calc
      ‖K‖ ≤ ‖(1 / (2 * Complex.I))‖ * ‖X - Xᴴ‖ := norm_smul_le _ _
      _ ≤ ‖(1 / (2 * Complex.I))‖ * (‖X‖ + ‖Xᴴ‖) := by gcongr; exact norm_sub_le _ _
      _ = ‖X‖ := by rw [frobenius_norm_conjTranspose]; norm_num; ring
  obtain ⟨P0, P1, hP0, hP1, hn0, hn1, hH⟩ := hHerm.exists_posSemidef_sub
  obtain ⟨P2, P3, hP2, hP3, hn2, hn3, hK⟩ := hKerm.exists_posSemidef_sub
  refine ⟨![P0, P1, P2, P3], fun j ↦ ?_, ?_⟩
  · fin_cases j
    · exact ⟨hP0, hn0.trans hnormH⟩
    · exact ⟨hP1, hn1.trans hnormH⟩
    · exact ⟨hP2, hn2.trans hnormK⟩
    · exact ⟨hP3, hn3.trans hnormK⟩
  · have hX : X = H + Complex.I • K := by
      simp only [H, K, smul_smul]
      rw [show Complex.I * (1 / (2 * Complex.I)) = (1 / 2 : ℂ) by field_simp, ← smul_add]
      rw [show X + Xᴴ + (X - Xᴴ) = (2 : ℂ) • X by rw [two_smul]; abel, smul_smul]
      norm_num
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    rw [hX, hH, hK, smul_sub]
    abel

/-- **Wolf Equation (8.117).** If a superoperator `S` satisfies `‖S P‖₁ ≤ c` for every positive
semidefinite `P` with `‖P‖₂ ≤ 1`, then its Hilbert--Schmidt `2 → 2` norm is at most `4 c`.

Source: Wolf, Equation (8.117); local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1355--1362. -/
theorem hilbertSchmidtOperatorNorm_le_four_mul_of_posSemidef (S : Module.End ℂ Mat) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ P : Mat, P.PosSemidef → ‖P‖ ≤ 1 → traceNorm (S P) ≤ c) :
    hilbertSchmidtOperatorNorm S ≤ 4 * c := by
  -- Homogeneity: `‖S P‖₁ ≤ c ‖P‖₂` for every positive semidefinite `P`.
  have hhom : ∀ P : Mat, P.PosSemidef → traceNorm (S P) ≤ c * ‖P‖ := by
    intro P hP
    rcases eq_or_ne P 0 with rfl | hP0
    · simp [traceNorm_zero]
    · have hpos : 0 < ‖P‖ := norm_pos_iff.mpr hP0
      let r : ℂ := (((‖P‖)⁻¹ : ℝ) : ℂ)
      have hr : 0 ≤ r := Complex.zero_le_real.mpr (inv_nonneg.mpr hpos.le)
      have hrn : ‖r‖ = (‖P‖)⁻¹ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
      have hQ := h (r • P) (hP.smul hr) (by rw [norm_smul, hrn, inv_mul_cancel₀ hpos.ne'])
      rw [map_smul, traceNorm_smul, hrn, inv_mul_le_iff₀ hpos] at hQ
      linarith
  refine hilbertSchmidtOperatorNorm_le_of_forall S (by positivity) fun X ↦ ?_
  obtain ⟨P, hP, hX⟩ := exists_four_posSemidef_frobenius_norm_le X
  have hterm : ∀ j, ‖S (P j)‖ ≤ c * ‖X‖ := fun j ↦
    (frobenius_norm_le_traceNorm _).trans ((hhom _ (hP j).1).trans
      (mul_le_mul_of_nonneg_left (hP j).2 hc))
  conv_lhs => rw [hX, map_sub, map_add, map_sub, map_smul, map_smul]
  have hI : ∀ Y : Mat, ‖Complex.I • Y‖ = ‖Y‖ := fun Y ↦ by
    rw [norm_smul, Complex.norm_I, one_mul]
  calc
    ‖S (P 0) - S (P 1) + Complex.I • S (P 2) - Complex.I • S (P 3)‖ ≤
        ‖S (P 0) - S (P 1) + Complex.I • S (P 2)‖ + ‖Complex.I • S (P 3)‖ := norm_sub_le _ _
    _ ≤ ‖S (P 0) - S (P 1)‖ + ‖Complex.I • S (P 2)‖ + ‖Complex.I • S (P 3)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖S (P 0)‖ + ‖S (P 1)‖ + ‖S (P 2)‖ + ‖S (P 3)‖ := by
      rw [hI, hI]
      gcongr
      exact norm_sub_le _ _
    _ ≤ 4 * c * ‖X‖ := by linarith [hterm 0, hterm 1, hterm 2, hterm 3]

/-- For a positive iterate, `Δ_T(Tⁿρ)` is the trace norm of `(Tⁿ - T_ϕⁿ) ρ`. -/
private theorem traceNormAsymptoticDistance_pow_eq_traceNorm_sub_apply
    (T : Module.End ℂ Mat) (ρ : Mat) {n : ℕ} (hn : 0 < n) :
    traceNormAsymptoticDistance T ((T ^ n) ρ) =
      traceNorm (((T ^ n) - T.peripheralWeightedProjection ^ n) ρ) := by
  have hP : IsIdempotentElem T.peripheralProjection := T.isIdempotentElem_peripheralProjection
  have hcomm : Commute T T.peripheralProjection := T.commute_peripheralProjection.symm
  have hWpow : T.peripheralWeightedProjection ^ n = T ^ n * T.peripheralProjection := by
    rw [Module.End.peripheralWeightedProjection, ← Module.End.mul_eq_comp, hcomm.mul_pow,
      hP.pow_eq hn.ne']
  rw [traceNormAsymptoticDistance_pow_eq, LinearMap.sub_apply, hWpow, Module.End.mul_apply,
    map_sub]

/-- **Wolf Equation (8.113), bound form.** Let `0 < d`. If `c` bounds `Δ_T(Tⁿρ)` for every
density operator `ρ`, then `‖Tⁿ - T_ϕⁿ‖_{2→2} ≤ 4 √d c`. No positivity of `T` is needed for this
direction, and the statement holds at `n = 0`, where the superoperator difference vanishes.

Source: Wolf, Equations (8.113) and (8.117); local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1329--1332 and 1355--1363. -/
theorem hilbertSchmidtOperatorNorm_pow_sub_le_of_forall_traceNormAsymptoticDistance_le
    (T : Module.End ℂ Mat) (hD : 0 < D) (n : ℕ) {c : ℝ}
    (hc : ∀ ρ ∈ densityMatrices D, traceNormAsymptoticDistance T ((T ^ n) ρ) ≤ c) :
    1 / (4 * Real.sqrt D) *
        hilbertSchmidtOperatorNorm ((T ^ n) - T.peripheralWeightedProjection ^ n) ≤ c := by
  let S : Module.End ℂ Mat := (T ^ n) - T.peripheralWeightedProjection ^ n
  have hsqrt : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  -- A density operator exists, so `c ≥ 0`.
  let : NeZero D := ⟨hD.ne'⟩
  let ρ₀ : Mat := ((D : ℂ)⁻¹) • 1
  have hρ₀ : ρ₀ ∈ densityMatrices D := by
    refine ⟨PosSemidef.one.smul (by positivity), ?_⟩
    simp only [ρ₀, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
    exact inv_mul_cancel₀ (by exact_mod_cast hD.ne')
  have hc0 : 0 ≤ c := (traceNorm_nonneg _).trans (hc ρ₀ hρ₀)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hS : (T ^ 0) - T.peripheralWeightedProjection ^ 0 = 0 := by simp
    rw [hS]
    have h0 : hilbertSchmidtOperatorNorm (0 : Module.End ℂ Mat) = 0 := by
      simp [hilbertSchmidtOperatorNorm, frobeniusEuclideanMap]
    rw [h0, mul_zero]
    exact hc0
  -- `‖S P‖₁ ≤ √d c` for positive semidefinite `P` with `‖P‖₂ ≤ 1`.
  have hP : ∀ P : Mat, P.PosSemidef → ‖P‖ ≤ 1 → traceNorm (S P) ≤ Real.sqrt D * c := by
    intro P hP hP1
    rcases eq_or_ne P 0 with rfl | hP0
    · simp only [map_zero, traceNorm_zero]
      positivity
    · have htrace : P.trace = ((traceNorm P : ℝ) : ℂ) := by
        rw [traceNorm_eq_re_trace_abs, CFC.abs_of_nonneg P (nonneg_iff_posSemidef.mpr hP)]
        exact (Complex.ext rfl (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm)
      have ht : 0 < traceNorm P := (traceNorm_pos_iff P).mpr hP0
      have htle : traceNorm P ≤ Real.sqrt D :=
        (traceNorm_le_sqrt_dim_mul_frobenius_norm P).trans
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hP1 hsqrt.le)
      let ρ : Mat := ((traceNorm P : ℝ)⁻¹ : ℂ) • P
      have hρ : ρ ∈ densityMatrices D := by
        refine ⟨hP.smul (by
          rw [← Complex.ofReal_inv]
          exact Complex.zero_le_real.mpr (inv_nonneg.mpr ht.le)), ?_⟩
        simp only [ρ, trace_smul, htrace, smul_eq_mul]
        rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne',
          Complex.ofReal_one]
      have hSP : S P = ((traceNorm P : ℝ) : ℂ) • S ρ := by
        simp only [ρ, map_smul, smul_smul]
        rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne',
          Complex.ofReal_one, one_smul]
      have hdist := hc ρ hρ
      rw [traceNormAsymptoticDistance_pow_eq_traceNorm_sub_apply T ρ hn] at hdist
      rw [hSP, traceNorm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      exact mul_le_mul htle hdist (traceNorm_nonneg _) hsqrt.le
  have hfour := hilbertSchmidtOperatorNorm_le_four_mul_of_posSemidef S
    (mul_nonneg hsqrt.le hc0) hP
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-- **Wolf Proposition, Equation (8.113).** For a positive trace-preserving map `T` on
`M_d(ℂ)` with `0 < d`, the supremum of `Δ_T(Tⁿρ)` over density operators is at least
`‖Tⁿ - T_ϕⁿ‖_{2→2} / (4 √d)`. The supremum is finite, by the upper bound (8.112).

Source: Wolf, Equation (8.113); local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1329--1332 and 1355--1363. -/
theorem hilbertSchmidtOperatorNorm_pow_sub_le_sSup_traceNormAsymptoticDistance
    (T : Module.End ℂ Mat) (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hD : 0 < D) (n : ℕ) :
    1 / (4 * Real.sqrt D) *
        hilbertSchmidtOperatorNorm ((T ^ n) - T.peripheralWeightedProjection ^ n) ≤
      sSup ((fun ρ ↦ traceNormAsymptoticDistance T ((T ^ n) ρ)) '' densityMatrices D) := by
  let : NeZero D := ⟨hD.ne'⟩
  -- The asymptotic distance of a density operator is at most two.
  have hΔ : ∀ ρ ∈ densityMatrices D, traceNormAsymptoticDistance T ρ ≤ 2 := by
    intro ρ hρ
    have hρφ : T.peripheralProjection ρ ∈ densityMatrices D :=
      ⟨hPos.peripheralProjection_isPositiveMap hTP ρ hρ.1,
        by rw [hPos.peripheralProjection_isTracePreservingMap hTP, hρ.2]⟩
    have hnorm : ∀ σ ∈ densityMatrices D, traceNorm σ = 1 := by
      intro σ hσ
      rw [traceNorm_eq_re_trace_abs, CFC.abs_of_nonneg σ (nonneg_iff_posSemidef.mpr hσ.1),
        hσ.2, Complex.one_re]
    calc
      traceNormAsymptoticDistance T ρ ≤ traceNorm ρ + traceNorm (T.peripheralProjection ρ) := by
        rw [traceNormAsymptoticDistance, sub_eq_add_neg]
        refine (traceNorm_add_le _ _).trans_eq ?_
        rw [show -T.peripheralProjection ρ = (-1 : ℂ) • T.peripheralProjection ρ by simp,
          traceNorm_smul, norm_neg, norm_one, one_mul]
      _ = 2 := by rw [hnorm ρ hρ, hnorm _ hρφ]; norm_num
  have hbdd : BddAbove
      ((fun ρ ↦ traceNormAsymptoticDistance T ((T ^ n) ρ)) '' densityMatrices D) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨2, ?_⟩
      rintro _ ⟨ρ, hρ, rfl⟩
      simpa using hΔ ρ hρ
    · refine ⟨Real.sqrt ((D : ℝ) / 2) *
        hilbertSchmidtOperatorNorm ((T ^ n) - T.peripheralWeightedProjection ^ n) * 2, ?_⟩
      rintro _ ⟨ρ, hρ, rfl⟩
      exact (traceNormAsymptoticDistance_pow_le_hilbertSchmidtOperatorNorm T hPos hTP hρ hn).trans
        (mul_le_mul_of_nonneg_left (hΔ ρ hρ) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
  exact hilbertSchmidtOperatorNorm_pow_sub_le_of_forall_traceNormAsymptoticDistance_le T hD n
    fun ρ hρ ↦ le_csSup hbdd ⟨ρ, hρ, rfl⟩

section TransferMatrixNorm

open scoped Matrix.Norms.L2Operator

/-- **Wolf Proposition, Equation (8.113), transfer-matrix form.** For a positive
trace-preserving map `T` on `M_d(ℂ)` with `0 < d`, the supremum of `Δ_T(Tⁿρ)` over density
operators is at least `‖T̂ⁿ - T̂_ϕⁿ‖_∞ / (4 √d)`, with the largest-singular-value norm of Wolf's
transfer matrices.

Source: Wolf, Equation (8.113); local source
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 1329--1332 and 1355--1363. -/
theorem transferMatrix_l2_opNorm_pow_sub_le_sSup_traceNormAsymptoticDistance
    (T : Module.End ℂ Mat) (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hD : 0 < D) (n : ℕ) :
    1 / (4 * Real.sqrt D) *
        ‖transferMatrix T ^ n - transferMatrix T.peripheralWeightedProjection ^ n‖ ≤
      sSup ((fun ρ ↦ traceNormAsymptoticDistance T ((T ^ n) ρ)) '' densityMatrices D) := by
  have h := hilbertSchmidtOperatorNorm_pow_sub_le_sSup_traceNormAsymptoticDistance
    T hPos hTP hD n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : hilbertSchmidtOperatorNorm (0 : Module.End ℂ Mat) = 0 := by
      simp [hilbertSchmidtOperatorNorm, frobeniusEuclideanMap]
    simp only [pow_zero, sub_self] at h ⊢
    rw [h0, mul_zero] at h
    let iN : NormedAddCommGroup (Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :=
      Matrix.instL2OpNormedAddCommGroup
    have hz : ‖(0 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)‖ = 0 :=
      @norm_zero _ iN.toNormedAddGroup.toSeminormedAddGroup
    rw [hz, mul_zero]
    exact h
  · rwa [transferMatrix_pow_sub_peripheralWeightedProjection_pow T hn,
      ← transferMatrix_pow, l2_opNorm_transferMatrix_eq_hilbertSchmidtOperatorNorm,
      ← T.pow_sub_peripheralWeightedProjection_pow hn]

end TransferMatrixNorm

end Matrix
