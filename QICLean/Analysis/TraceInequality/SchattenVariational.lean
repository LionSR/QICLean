/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceInequality.TraceHolderSchatten
import QICLean.Analysis.TraceNorm.TraceNormAbs
import QICLean.Analysis.Isometry.PolarUnitaryCorrection
import Mathlib.Analysis.MeanInequalities

/-!
# Variational characterizations of Schatten norms

For a complex square matrix `A` and `p > 0` the Schatten `p`-norm is
`‖A‖_p = (tr |A|^p)^{1/p} = (∑ᵢ sᵢ(A)^p)^{1/p}`, with `|A| = √(A†A)`. This file proves Wolf's
Hölder inequality for Schatten norms and the remaining parts of Wolf's Theorem 8.3, "Variational
ways to `p`-norms":

* Equation (8.6): `|tr[A†B]| ≤ ‖A‖_p ‖B‖_q` for Hölder conjugate `p, q`, including `p = 1`,
  `q = ∞` with the operator norm.
* Equation (8.10): `‖A‖_p = sup {|tr[A†B]| : ‖B‖_q = 1}`, for `p > 1` and for `p = 1`
  (where `‖B‖_∞` is the operator norm). The supremum is attained for nonempty index types.
* Equation (8.12): `‖A‖_∞ = sup {|⟨ψ|A|φ⟩| : ‖ψ‖ = ‖φ‖ = 1}`.
* Equation (8.13), corrected: `‖P‖_p^p / p = sup_{X ≥ 0} [tr[PX] − ‖X‖_q^q / q]` for `P ≥ 0`
  and `p > 1`.

Equation (8.11) is `Matrix.traceNorm_eq_sSup_norm_trace_conjTranspose_mul_unitary` in
`QICLean.Analysis.TraceNorm.Variational`.

**Local fix (Equation 8.13):** Wolf prints `‖P‖_p^p = (1/p) sup_{X ≥ 0}[tr[PX] − ‖X‖_q^q / q]`.
For `d = 1` and `P = t ≥ 0` the supremum of `tx − x^q/q` over `x ≥ 0` is `t^p/p`, attained at
`x = t^{p-1}`, so the factor `1/p` belongs on the left-hand side. The equation also needs
`p > 1`, so that `q < ∞`. Documented in `docs/paper-gaps/wolf_ch8_variational_pnorm_constant.tex`.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 8.1, local source
  `Notes/WolfNoteTexSource/ch08_distance_measures.tex`: Schatten norms, lines 65--69;
  Equation (8.6), lines 144--148; Theorem "Variational ways to `p`-norms", lines 178--194.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder InnerProductSpace

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

-- The matrix functional calculus behind `CFC.abs` needs `DecidableEq n`.
set_option linter.unusedDecidableInType false in
/-- The absolute value `|A| = √(A†A)` is positive semidefinite. -/
theorem abs_posSemidef (A : Matrix n n ℂ) : (CFC.abs A).PosSemidef :=
  nonneg_iff_posSemidef.mp (CFC.abs_nonneg A)

/-- The **Schatten `p`-norm** `‖A‖_p = (tr |A|^p)^{1/p}`, `|A| = √(A†A)`, computed by the
functional calculus; this is `(∑ᵢ sᵢ(A)^p)^{1/p}` over the singular values.
Wolf §8.1, `ch08_distance_measures.tex` lines 65--69. -/
noncomputable def schattenNorm (A : Matrix n n ℂ) (p : ℝ) : ℝ :=
  (cfc (fun x : ℝ ↦ x ^ p) (CFC.abs A)).trace.re ^ p⁻¹


/-- The real trace of a functional calculus is the sum over the eigenvalues. -/
theorem IsHermitian.re_trace_cfc {P : Matrix n n ℂ} (hP : P.IsHermitian) (f : ℝ → ℝ) :
    (cfc f P).trace.re = ∑ i, f (hP.eigenvalues i) := by
  rw [hP.cfc_eq]
  exact hP.trace_cfc_eq_sum_re f

/-- `‖A‖_p = (∑ᵢ μᵢ^p)^{1/p}` over the eigenvalues `μᵢ` of `|A|`, the singular values. -/
theorem schattenNorm_eq_sum (A : Matrix n n ℂ) (p : ℝ) :
    schattenNorm A p =
      (∑ i, (abs_posSemidef A).isHermitian.eigenvalues i ^ p) ^ p⁻¹ := by
  rw [schattenNorm, (abs_posSemidef A).isHermitian.re_trace_cfc]

/-- Schatten norms are nonnegative. -/
theorem schattenNorm_nonneg (A : Matrix n n ℂ) (p : ℝ) : 0 ≤ schattenNorm A p := by
  rw [schattenNorm_eq_sum]
  exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ ↦
    Real.rpow_nonneg ((abs_posSemidef A).eigenvalues_nonneg i) _) _

/-- For `p ≠ 0`, `‖A‖_p` is the Schatten weight `‖|A|‖_{1/θ}` with `θ = 1/p` used by the
multi-factor trace Hölder inequality. -/
theorem schattenNorm_eq_schattenWeight (A : Matrix n n ℂ) {p : ℝ} (hp : p ≠ 0) :
    schattenNorm A p = schattenWeight (CFC.abs A) p⁻¹ := by
  rw [schattenWeight_of_ne_zero _ (inv_ne_zero hp), schattenNorm, one_div, inv_inv]

theorem schattenWeight_nonneg {X : Matrix n n ℂ} (hX : X.PosSemidef) (θ : ℝ) :
    0 ≤ schattenWeight X θ := by
  by_cases hθ : θ = 0
  · rw [hθ, schattenWeight_of_eq_zero]; exact norm_nonneg _
  · rw [schattenWeight_of_ne_zero _ hθ, hX.isHermitian.re_trace_cfc]
    exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ ↦
      Real.rpow_nonneg (hX.eigenvalues_nonneg i) _) _

/-- Polar decomposition `A = U |A|`. -/
theorem exists_unitary_mul_abs (A : Matrix n n ℂ) :
    ∃ U ∈ unitaryGroup n ℂ, A = U * CFC.abs A := by
  obtain ⟨U, hA, -⟩ := exists_unitary_polar_correction A
  exact ⟨U, U.2, hA⟩

private theorem unitary_norm_le_one {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) :
    ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim U 0, norm_zero]; exact zero_le_one
  · exact (CStarRing.norm_of_mem_unitary hU).le

/-- **Hölder's inequality with weights.** For `θ, φ ≥ 0` with `θ + φ = 1`,
`|tr[A†B]| ≤ ‖A‖_{1/θ} ‖B‖_{1/φ}`, with the operator norm for a zero weight. -/
theorem norm_trace_conjTranspose_mul_le_schattenWeight (A B : Matrix n n ℂ) {θ φ : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hsum : θ + φ = 1) :
    ‖(Aᴴ * B).trace‖ ≤ schattenWeight (CFC.abs A) θ * schattenWeight (CFC.abs B) φ := by
  obtain ⟨U, hU, hA⟩ := exists_unitary_mul_abs A
  obtain ⟨W, hW, hB⟩ := exists_unitary_mul_abs B
  have hP : (CFC.abs A)ᴴ = CFC.abs A := (abs_posSemidef A).isHermitian.eq
  have hprod : Aᴴ * B = (List.ofFn fun j : Fin 2 ↦
      (![1, Uᴴ * W] j) * (![CFC.abs A, CFC.abs B] j)).prod := by
    conv_lhs => rw [hA, hB]
    simp [List.ofFn_succ, conjTranspose_mul, hP, Matrix.mul_assoc]
  have hUW : Uᴴ * W ∈ unitaryGroup n ℂ := Submonoid.mul_mem _ (Unitary.star_mem hU) hW
  have h := norm_trace_list_prod_mul_le_of_posSemidef ![1, Uᴴ * W] ![CFC.abs A, CFC.abs B]
    (fun j ↦ by fin_cases j <;> simp [abs_posSemidef]) ![θ, φ]
    (fun j ↦ by fin_cases j <;> simp [hθ, hφ]) (by simp [Fin.sum_univ_two, hsum])
  rw [hprod]
  refine h.trans ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h1 : ‖(1 : Matrix n n ℂ)‖ ≤ 1 := unitary_norm_le_one (one_mem _)
  have h2 : ‖Uᴴ * W‖ ≤ 1 := unitary_norm_le_one hUW
  have hS : 0 ≤ schattenWeight (CFC.abs A) θ * schattenWeight (CFC.abs B) φ :=
    mul_nonneg (schattenWeight_nonneg (abs_posSemidef A) θ)
      (schattenWeight_nonneg (abs_posSemidef B) φ)
  calc ‖(1 : Matrix n n ℂ)‖ * ‖Uᴴ * W‖ *
        (schattenWeight (CFC.abs A) θ * schattenWeight (CFC.abs B) φ)
      ≤ 1 * (schattenWeight (CFC.abs A) θ * schattenWeight (CFC.abs B) φ) :=
        mul_le_mul_of_nonneg_right
          ((mul_le_mul h1 h2 (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) hS
    _ = _ := one_mul _

/-- **Hölder's inequality, Wolf Eq. (8.6).** `|tr[A†B]| ≤ ‖A‖_p ‖B‖_q` for Hölder conjugate
`p, q`. Wolf, `ch08_distance_measures.tex` lines 144--148. -/
theorem norm_trace_conjTranspose_mul_le_schattenNorm (A B : Matrix n n ℂ) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ‖(Aᴴ * B).trace‖ ≤ schattenNorm A p * schattenNorm B q := by
  rw [schattenNorm_eq_schattenWeight A hpq.ne_zero,
    schattenNorm_eq_schattenWeight B hpq.symm.ne_zero]
  exact norm_trace_conjTranspose_mul_le_schattenWeight A B hpq.inv_nonneg hpq.symm.inv_nonneg
    hpq.inv_add_inv_eq_one

/-- **Hölder's inequality, Wolf Eq. (8.6), `p = 1`, `q = ∞`.** `|tr[A†B]| ≤ ‖A‖_1 ‖B‖_∞`
with the operator norm `‖B‖_∞`. -/
theorem norm_trace_conjTranspose_mul_le_schattenNorm_one (A B : Matrix n n ℂ) :
    ‖(Aᴴ * B).trace‖ ≤ schattenNorm A 1 * ‖B‖ := by
  have h := norm_trace_conjTranspose_mul_le_schattenWeight A B zero_le_one le_rfl (add_zero 1)
  rwa [schattenWeight_of_eq_zero, CFC.norm_abs, ← inv_one,
    ← schattenNorm_eq_schattenWeight A one_ne_zero] at h

section Attainment

variable {P : Matrix n n ℂ} (hP : P.PosSemidef)

private theorem spectrum_finite (P : Matrix n n ℂ) : (spectrum ℝ P).Finite :=
  Matrix.finite_real_spectrum

/-- For `P ≥ 0`, `g ≥ 0` on the eigenvalues and `U` unitary, `|U g(P)| = g(P)`. -/
private theorem abs_unitary_mul_cfc {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (g : ℝ → ℝ) (hg : ∀ i, 0 ≤ g (hP.isHermitian.eigenvalues i)) :
    CFC.abs (U * cfc g P) = cfc g P := by
  have hY : 0 ≤ cfc g P := cfc_nonneg fun x hx ↦ by
    rw [hP.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hg i
  have hYh : star (cfc g P) = cfc g P := hY.isSelfAdjoint.star_eq
  have hUU : star U * U = 1 := Unitary.star_mul_self_of_mem hU
  have : star (U * cfc g P) * (U * cfc g P) = cfc g P * cfc g P := by
    rw [star_mul, hYh, Matrix.mul_assoc, ← Matrix.mul_assoc (star U), hUU, Matrix.one_mul]
  rw [CFC.abs, this, CFC.sqrt_mul_self _ hY]

/-- The `q`-th power trace of `g(P)`: `tr g(P)^q = ∑ᵢ g(λᵢ)^q`. -/
private theorem re_trace_rpow_cfc (g : ℝ → ℝ) {q : ℝ} :
    (cfc (fun x : ℝ ↦ x ^ q) (cfc g P)).trace.re =
      ∑ i, g (hP.isHermitian.eigenvalues i) ^ q := by
  rw [← cfc_comp' (fun x : ℝ ↦ x ^ q) g P ((spectrum_finite _).image _ |>.continuousOn _)
    ((spectrum_finite _).continuousOn _), hP.isHermitian.re_trace_cfc]

/-- `tr[P g(P)] = ∑ᵢ λᵢ g(λᵢ)`. -/
private theorem trace_mul_cfc (g : ℝ → ℝ) :
    (P * cfc g P).trace = ((∑ i, hP.isHermitian.eigenvalues i *
      g (hP.isHermitian.eigenvalues i) : ℝ) : ℂ) := by
  have h : P * cfc g P = cfc (fun x ↦ x * g x) P := by
    rw [cfc_mul (fun x : ℝ ↦ x) g P ((spectrum_finite _).continuousOn _)
      ((spectrum_finite _).continuousOn _), cfc_id' ℝ P]
  rw [h, hP.isHermitian.cfc_eq, hP.isHermitian.trace_cfc_eq_sum]
  push_cast
  rfl

end Attainment

/-- The trace `tr[A†(U g(|A|))] = ∑ᵢ μᵢ g(μᵢ)` for the polar unitary `U` of `A`. -/
private theorem trace_conjTranspose_mul_polar {A U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (hA : A = U * CFC.abs A) (g : ℝ → ℝ) :
    (Aᴴ * (U * cfc g (CFC.abs A))).trace =
      ((∑ i, (abs_posSemidef A).isHermitian.eigenvalues i *
        g ((abs_posSemidef A).isHermitian.eigenvalues i) : ℝ) : ℂ) := by
  have hP : (CFC.abs A)ᴴ = CFC.abs A := (abs_posSemidef A).isHermitian.eq
  have hUU : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have : Aᴴ * (U * cfc g (CFC.abs A)) = CFC.abs A * cfc g (CFC.abs A) := by
    rw [show Aᴴ = (U * CFC.abs A)ᴴ from congrArg _ hA]
    rw [conjTranspose_mul, hP, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hUU, Matrix.one_mul]
  rw [this, trace_mul_cfc (abs_posSemidef A)]

/-- **Attainment in Wolf's Eq. (8.10)**, `p > 1`: some `B` with `‖B‖_q = 1` realizes
`tr[A†B] = ‖A‖_p`. Wolf's maximizer is `B = U P^{p-1} / tr[P^p]^{1/q}` for `A = U P`; for
`A = 0` any `B` of unit `q`-norm works. -/
theorem exists_schattenNorm_eq_one_trace_eq [Nonempty n] (A : Matrix n n ℂ) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    ∃ B, schattenNorm B q = 1 ∧ (Aᴴ * B).trace = (schattenNorm A p : ℂ) := by
  obtain ⟨U, hU, hA⟩ := exists_unitary_mul_abs A
  have hPA := abs_posSemidef A
  set μ := hPA.isHermitian.eigenvalues
  have hμ : ∀ i, 0 ≤ μ i := hPA.eigenvalues_nonneg
  set S := ∑ i, μ i ^ p
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hμ i) _
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hnorm : schattenNorm A p = S ^ p⁻¹ := schattenNorm_eq_sum A p
  rcases hS.eq_or_lt with hS0 | hSpos
  · -- `A = 0`: all singular values vanish; use a scalar multiple of the identity.
    have hμ0 : ∀ i, μ i = 0 := fun i ↦ by
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ Real.rpow_nonneg (hμ i) p).mp
        hS0.symm i (Finset.mem_univ _)
      exact (Real.rpow_eq_zero (hμ i) hp.ne').mp this
    set c : ℝ := (Fintype.card n : ℝ) ^ (-q⁻¹)
    have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg _) _
    refine ⟨U * cfc (fun _ ↦ c) (CFC.abs A), ?_, ?_⟩
    · rw [schattenNorm, abs_unitary_mul_cfc hPA hU _ (fun _ ↦ hc), re_trace_rpow_cfc hPA]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp only [c]
      rw [← Real.rpow_mul (Nat.cast_nonneg _), neg_mul, inv_mul_cancel₀ hq.ne',
        Real.rpow_neg_one, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
        Real.one_rpow]
    · rw [trace_conjTranspose_mul_polar hU hA, hnorm, ← hS0, Real.zero_rpow (inv_ne_zero hp.ne')]
      simp [μ] at hμ0
      simp [hμ0]
  · set c : ℝ := S ^ (-q⁻¹)
    have hc : 0 ≤ c := Real.rpow_nonneg hS _
    set g : ℝ → ℝ := fun x ↦ c * x ^ (p - 1)
    have hg : ∀ i, 0 ≤ g (μ i) := fun i ↦ mul_nonneg hc (Real.rpow_nonneg (hμ i) _)
    refine ⟨U * cfc g (CFC.abs A), ?_, ?_⟩
    · rw [schattenNorm, abs_unitary_mul_cfc hPA hU _ hg, re_trace_rpow_cfc hPA]
      have : ∀ i, g (μ i) ^ q = S⁻¹ * μ i ^ p := fun i ↦ by
        simp only [g, c]
        rw [Real.mul_rpow hc (Real.rpow_nonneg (hμ i) _), ← Real.rpow_mul hS,
          ← Real.rpow_mul (hμ i),
          neg_mul, inv_mul_cancel₀ hq.ne', Real.rpow_neg_one, hpq.sub_one_mul_conj]
      change (∑ i, g (μ i) ^ q) ^ q⁻¹ = 1
      simp only [this, ← Finset.mul_sum]
      rw [inv_mul_cancel₀ hSpos.ne', Real.one_rpow]
    · rw [trace_conjTranspose_mul_polar hU hA, hnorm]
      have : ∀ i, μ i * g (μ i) = c * μ i ^ p := fun i ↦ by
        simp only [g]
        have h1 : μ i ^ p = μ i ^ (1 + (p - 1)) := by ring_nf
        rw [h1, Real.rpow_add' (hμ i) (by ring_nf; exact hp.ne'), Real.rpow_one]
        ring
      change ((∑ i, μ i * g (μ i) : ℝ) : ℂ) = ((S ^ p⁻¹ : ℝ) : ℂ)
      congr 1
      simp only [this, ← Finset.mul_sum, c]
      rw [← Real.rpow_add_one' hS (by rw [← hpq.one_sub_inv]; ring_nf; exact inv_ne_zero hp.ne'),
        ← hpq.one_sub_inv]
      ring_nf

/-- **Attainment in Wolf's Eq. (8.10)**, `p = 1`, `q = ∞`: the polar unitary `U` of `A` has
operator norm one and `tr[A†U] = ‖A‖_1`. -/
theorem exists_norm_eq_one_trace_eq_schattenNorm_one [Nonempty n] (A : Matrix n n ℂ) :
    ∃ B : Matrix n n ℂ, ‖B‖ = 1 ∧ (Aᴴ * B).trace = (schattenNorm A 1 : ℂ) := by
  obtain ⟨U, hU, hA⟩ := exists_unitary_mul_abs A
  refine ⟨U, CStarRing.norm_of_mem_unitary hU, ?_⟩
  have h := trace_conjTranspose_mul_polar hU hA (fun _ ↦ 1)
  rw [cfc_const_one ℝ (CFC.abs A) (CFC.abs_nonneg A).isSelfAdjoint, Matrix.mul_one] at h
  rw [h, schattenNorm_eq_sum]
  simp

private theorem sSup_eq_zero_of_subset {S : Set ℝ} (h : S ⊆ {0}) : sSup S = 0 := by
  rcases Set.subset_singleton_iff_eq.mp h with rfl | rfl
  · exact Real.sSup_empty
  · exact csSup_singleton 0

private theorem schattenNorm_of_isEmpty [IsEmpty n] (A : Matrix n n ℂ) {p : ℝ} (hp : p ≠ 0) :
    schattenNorm A p = 0 := by
  rw [schattenNorm_eq_sum, Finset.univ_eq_empty, Finset.sum_empty,
    Real.zero_rpow (inv_ne_zero hp)]

/-- **Wolf's Eq. (8.10)**, attained, `p > 1`: for nonempty index types, `‖A‖_p` is the greatest
value of `|tr[A†B]|` over `‖B‖_q = 1`. -/
theorem isGreatest_norm_trace_conjTranspose_mul_schattenNorm [Nonempty n] (A : Matrix n n ℂ)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    IsGreatest {r | ∃ B, schattenNorm B q = 1 ∧ r = ‖(Aᴴ * B).trace‖} (schattenNorm A p) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨B, hB, htr⟩ := exists_schattenNorm_eq_one_trace_eq A hpq
    exact ⟨B, hB, by rw [htr, Complex.norm_real, Real.norm_of_nonneg (schattenNorm_nonneg _ _)]⟩
  · rintro r ⟨B, hB, rfl⟩
    simpa [hB] using norm_trace_conjTranspose_mul_le_schattenNorm A B hpq

/-- **Wolf's Eq. (8.10)**, `p > 1`: `‖A‖_p = sup {|tr[A†B]| : ‖B‖_q = 1}` for Hölder conjugate
`p, q`. Wolf, Theorem "Variational ways to `p`-norms", `ch08_distance_measures.tex`
lines 178--194. -/
theorem schattenNorm_eq_sSup_norm_trace_conjTranspose_mul (A : Matrix n n ℂ) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    schattenNorm A p = sSup {r | ∃ B, schattenNorm B q = 1 ∧ r = ‖(Aᴴ * B).trace‖} := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [schattenNorm_of_isEmpty A hpq.ne_zero]
    refine (sSup_eq_zero_of_subset ?_).symm
    rintro r ⟨B, -, rfl⟩
    simp [Matrix.trace]
  · exact (isGreatest_norm_trace_conjTranspose_mul_schattenNorm A hpq).csSup_eq.symm

/-- **Wolf's Eq. (8.10)**, attained, `p = 1`, `q = ∞`: for nonempty index types, `‖A‖_1` is the
greatest value of `|tr[A†B]|` over operator-norm-one `B`. -/
theorem isGreatest_norm_trace_conjTranspose_mul_opNorm [Nonempty n] (A : Matrix n n ℂ) :
    IsGreatest {r | ∃ B : Matrix n n ℂ, ‖B‖ = 1 ∧ r = ‖(Aᴴ * B).trace‖} (schattenNorm A 1) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨B, hB, htr⟩ := exists_norm_eq_one_trace_eq_schattenNorm_one A
    exact ⟨B, hB, by rw [htr, Complex.norm_real, Real.norm_of_nonneg (schattenNorm_nonneg _ _)]⟩
  · rintro r ⟨B, hB, rfl⟩
    simpa [hB] using norm_trace_conjTranspose_mul_le_schattenNorm_one A B

/-- **Wolf's Eq. (8.10)**, `p = 1`, `q = ∞`: `‖A‖_1 = sup {|tr[A†B]| : ‖B‖_∞ = 1}` with the
operator norm `‖B‖_∞`. Wolf, `ch08_distance_measures.tex` lines 178--194. -/
theorem schattenNorm_one_eq_sSup_norm_trace_conjTranspose_mul (A : Matrix n n ℂ) :
    schattenNorm A 1 = sSup {r | ∃ B : Matrix n n ℂ, ‖B‖ = 1 ∧ r = ‖(Aᴴ * B).trace‖} := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [schattenNorm_of_isEmpty A one_ne_zero]
    refine (sSup_eq_zero_of_subset ?_).symm
    rintro r ⟨B, -, rfl⟩
    simp [Matrix.trace]
  · exact (isGreatest_norm_trace_conjTranspose_mul_opNorm A).csSup_eq.symm

/-- **Wolf's Eq. (8.12).** The operator norm is
`‖A‖_∞ = sup {|⟨ψ|A|φ⟩| : ‖ψ‖ = ‖φ‖ = 1}`. Wolf, `ch08_distance_measures.tex` lines 86--90
and 178--194. -/
theorem l2_opNorm_eq_sSup_norm_inner (A : Matrix n n ℂ) :
    ‖A‖ = sSup {r | ∃ ψ φ : EuclideanSpace ℂ n, ‖ψ‖ = 1 ∧ ‖φ‖ = 1 ∧
      r = ‖⟪ψ, toEuclideanLin A φ⟫_ℂ‖} := by
  set T := (toEuclideanLin (𝕜 := ℂ) (m := n) (n := n)).trans LinearMap.toContinuousLinearMap A
  have hT : ‖A‖ = ‖T‖ := rfl
  have hTφ : ∀ φ, T φ = toEuclideanLin A φ := fun _ ↦ rfl
  set Sset := {r | ∃ ψ φ : EuclideanSpace ℂ n, ‖ψ‖ = 1 ∧ ‖φ‖ = 1 ∧
      r = ‖⟪ψ, toEuclideanLin A φ⟫_ℂ‖} with hSset
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Subsingleton.elim A 0, norm_zero]
    refine (sSup_eq_zero_of_subset ?_).symm
    rintro r ⟨ψ, φ, hψ, -, rfl⟩
    rw [Subsingleton.elim ψ 0, norm_zero] at hψ
    exact absurd hψ zero_ne_one
  · obtain ⟨i⟩ := hn
    have hunit : ‖EuclideanSpace.single i (1 : ℂ)‖ = 1 := by simp
    have hmem : ‖⟪EuclideanSpace.single i (1 : ℂ),
        toEuclideanLin A (EuclideanSpace.single i 1)⟫_ℂ‖ ∈ Sset := ⟨_, _, hunit, hunit, rfl⟩
    rw [hT]
    refine (csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨_, hmem⟩ ?_ ?_).symm
    · rintro r ⟨ψ, φ, hψ, hφ, rfl⟩
      calc ‖⟪ψ, toEuclideanLin A φ⟫_ℂ‖ ≤ ‖ψ‖ * ‖T φ‖ := norm_inner_le_norm _ _
        _ ≤ ‖ψ‖ * (‖T‖ * ‖φ‖) := mul_le_mul_of_nonneg_left (T.le_opNorm φ) (norm_nonneg _)
        _ = ‖T‖ := by rw [hψ, hφ, one_mul, mul_one]
    · intro r hr
      rcases lt_or_ge r 0 with hr0 | hr0
      · exact ⟨_, hmem, hr0.trans_le (norm_nonneg _)⟩
      obtain ⟨x, hx1, hrx⟩ := T.exists_lt_apply_of_lt_opNorm hr
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hrx
        linarith
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      set φ : EuclideanSpace ℂ n := ((‖x‖⁻¹ : ℝ) : ℂ) • x
      have hφ : ‖φ‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le),
          inv_mul_cancel₀ hxpos.ne']
      have hTφ' : ‖T φ‖ = ‖x‖⁻¹ * ‖T x‖ := by
        rw [T.map_smul, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le)]
      have hrφ : r < ‖T φ‖ := by
        rw [hTφ']
        refine hrx.trans_le ?_
        calc ‖T x‖ = 1 * ‖T x‖ := (one_mul _).symm
          _ ≤ ‖x‖⁻¹ * ‖T x‖ := mul_le_mul_of_nonneg_right
            ((one_le_inv₀ hxpos).mpr hx1.le) (norm_nonneg _)
      have hTφ0 : 0 < ‖T φ‖ := hr0.trans_lt hrφ
      set ψ : EuclideanSpace ℂ n := ((‖T φ‖⁻¹ : ℝ) : ℂ) • T φ
      have hψ : ‖ψ‖ = 1 := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hTφ0.le),
          inv_mul_cancel₀ hTφ0.ne']
      refine ⟨_, ⟨ψ, φ, hψ, hφ, rfl⟩, ?_⟩
      rw [← hTφ, inner_smul_left, inner_self_eq_norm_sq_to_K]
      convert hrφ using 1
      simp only [norm_mul, RCLike.norm_conj, norm_pow, Complex.norm_real, RCLike.norm_ofReal,
        abs_norm, Real.norm_eq_abs, abs_inv]
      field_simp

/-- **Wolf's Eq. (8.13), corrected.** For `P ≥ 0` and Hölder conjugate `p, q` (so `p > 1`),
`‖P‖_p^p / p` is the greatest value of `tr[PX] − ‖X‖_q^q / q` over `X ≥ 0`, attained at
`X = P^{p-1}`.

**Local fix (constant):** Wolf prints `‖P‖_p^p = (1/p) sup_{X ≥ 0}[tr[PX] − ‖X‖_q^q / q]`;
the factor `1/p` belongs to the left-hand side, as the case `d = 1` shows. Documented in
`docs/paper-gaps/wolf_ch8_variational_pnorm_constant.tex`. Wolf, `ch08_distance_measures.tex`
lines 178--194. -/
theorem isGreatest_re_trace_mul_sub_schattenNorm_rpow {P : Matrix n n ℂ} (hP : P.PosSemidef)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    IsGreatest {r | ∃ X : Matrix n n ℂ, X.PosSemidef ∧
        r = (P * X).trace.re - schattenNorm X q ^ q / q}
      (schattenNorm P p ^ p / p) := by
  have hp := hpq.pos
  have hq := hpq.symm.pos
  have hPabs : CFC.abs P = P := CFC.abs_of_nonneg P hP.nonneg
  set ev := hP.isHermitian.eigenvalues
  have hev : ∀ i, 0 ≤ ev i := hP.eigenvalues_nonneg
  set S := ∑ i, ev i ^ p
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hev i) _
  have hPnorm : schattenNorm P p ^ p = S := by
    rw [schattenNorm, hPabs, hP.isHermitian.re_trace_cfc, Real.rpow_inv_rpow hS hp.ne']
  refine ⟨?_, ?_⟩
  · set g : ℝ → ℝ := fun x ↦ x ^ (p - 1)
    have hX : 0 ≤ cfc g P := cfc_nonneg fun x hx ↦ by
      rw [hP.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      exact Real.rpow_nonneg (hev i) _
    refine ⟨cfc g P, nonneg_iff_posSemidef.mp hX, ?_⟩
    have hXnorm : schattenNorm (cfc g P) q ^ q = S := by
      rw [schattenNorm, CFC.abs_of_nonneg _ hX, re_trace_rpow_cfc hP]
      have : ∀ i, g (ev i) ^ q = ev i ^ p := fun i ↦ by
        simp only [g]
        rw [← Real.rpow_mul (hev i), hpq.sub_one_mul_conj]
      change ((∑ i, g (ev i) ^ q) ^ q⁻¹) ^ q = S
      simp only [this]
      exact Real.rpow_inv_rpow hS hq.ne'
    have htr : (P * cfc g P).trace.re = S := by
      rw [trace_mul_cfc hP, Complex.ofReal_re]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      change ev i * ev i ^ (p - 1) = ev i ^ p
      conv_rhs => rw [show p = 1 + (p - 1) by ring]
      rw [Real.rpow_add' (hev i) (by ring_nf; exact hp.ne'), Real.rpow_one]
    rw [hXnorm, htr, hPnorm]
    have := hpq.inv_add_inv_eq_one
    simp only [div_eq_mul_inv]
    linear_combination S * this
  · rintro r ⟨X, hX, rfl⟩
    have hXabs : CFC.abs X = X := CFC.abs_of_nonneg X hX.nonneg
    have hhold := norm_trace_conjTranspose_mul_le_schattenNorm P X hpq
    rw [hP.isHermitian.eq] at hhold
    have hyoung := Real.young_inequality_of_nonneg (schattenNorm_nonneg P p)
      (schattenNorm_nonneg X q) hpq
    have := (Complex.re_le_norm (P * X).trace).trans (hhold.trans hyoung)
    linarith

/-- **Wolf's Eq. (8.13), corrected**, as a supremum:
`‖P‖_p^p = p · sup_{X ≥ 0} [tr[PX] − ‖X‖_q^q / q]`. -/
theorem schattenNorm_rpow_eq_mul_sSup {P : Matrix n n ℂ} (hP : P.PosSemidef)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    schattenNorm P p ^ p = p * sSup {r | ∃ X : Matrix n n ℂ, X.PosSemidef ∧
        r = (P * X).trace.re - schattenNorm X q ^ q / q} := by
  rw [(isGreatest_re_trace_mul_sub_schattenNorm_rpow hP hpq).csSup_eq,
    mul_div_cancel₀ _ hpq.ne_zero]

end Matrix
