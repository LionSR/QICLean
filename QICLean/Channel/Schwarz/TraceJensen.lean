/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.TraceConvexFunctions
import QICLean.Analysis.OrthogonalResolution
import QICLean.Analysis.HermitianEigenbasisFunctionalCalculus
import QICLean.Analysis.CfcConjugation
import QICLean.Channel.Basic

/-!
# Convex functions and positive maps under the trace

Wolf's Theorem 5.17 (Chapter 5, "Convex functions and positive maps under the trace",
Equation (5.51)) states that for positive maps `Tᵢ`, a function `f` convex on an interval `I`,
Hermitian `Xᵢ` with spectra in `I`, and positive semidefinite `C`,

`tr[C f(∑ᵢ Tᵢ(Xᵢ))] ≤ ∑ᵢ tr[C Tᵢ(f(Xᵢ))]`,

provided either `∑ᵢ Tᵢ(1) = 1`, or `∑ᵢ Tᵢ(1) ≤ 1` and `f(0) ≤ 0`.

**Local fix (commutation hypothesis):** the printed statement asks that `C` commute with
`f(∑ᵢ Tᵢ(Xᵢ))`. The proof, however, evaluates `f` at an eigenvalue of `∑ᵢ Tᵢ(Xᵢ)` itself:
Equation (5.52) needs `ψ` to be an eigenvector of `∑ᵢ Tᵢ(Xᵢ)`, not merely of its image under
`f`. With the printed hypothesis the theorem is false:
`Matrix.trace_jensen_commute_cfc_counterexample` gives positive maps from `M₁` to `M₂` with
`∑ᵢ Tᵢ(1) = 1`, the convex function `|x|` on `[-2, 2]`, and a positive semidefinite `C`
commuting with `f(∑ᵢ Tᵢ(Xᵢ)) = 1` for which the inequality fails. The corrected theorem
`Matrix.re_trace_mul_cfc_sum_map_le_of_commute` assumes that `C` commutes with
`∑ᵢ Tᵢ(Xᵢ)`; this implies commutation with `f(∑ᵢ Tᵢ(Xᵢ))`, and is equivalent to it whenever
`f` is injective on `I`. In the subunital alternative the source evaluates `f(0)`, so `0 ∈ I`
is part of that alternative. Both points are recorded in
`docs/paper-gaps/wolf_ch5_trace_jensen_commutation.tex`.

## Main results

* `ConvexOn.mul_map_le_sum_of_sum_eq`, `ConvexOn.mul_map_le_sum_of_sum_le`: the scalar Jensen
  steps of Equation (5.53), with unnormalized weights.
* `Matrix.re_trace_mul_cfc_sum_map_le_of_commute`: the corrected Theorem 5.17.
* `Matrix.trace_jensen_commute_cfc_counterexample`: the printed commutation hypothesis is not
  sufficient.

## Reference

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5, Theorem 5.17,
  Equations (5.51)–(5.53)][Wolf2012QChannels];
  `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, lines 1039–1078.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Finset

noncomputable section

/-- Scalar Jensen inequality with unnormalized weights of total mass `c`, the inequality in
Wolf's Equation (5.53) for `∑ᵢ Tᵢ(1) = 1`. -/
theorem ConvexOn.mul_map_le_sum_of_sum_eq {κ : Type*} {I : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ I f) (t : Finset κ) {q μ : κ → ℝ} (hq : ∀ k ∈ t, 0 ≤ q k)
    (hμ : ∀ k ∈ t, μ k ∈ I) {c y : ℝ} (hsum : ∑ k ∈ t, q k = c)
    (hmean : ∑ k ∈ t, q k * μ k = c * y) :
    c * f y ≤ ∑ k ∈ t, q k * f (μ k) := by
  have hc : 0 ≤ c := hsum ▸ Finset.sum_nonneg hq
  rcases hc.eq_or_lt with hc0 | hcpos
  · have hz : ∀ k ∈ t, q k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hq).mp (hsum.trans hc0.symm)
    rw [← hc0, zero_mul, Finset.sum_eq_zero fun k hk => by rw [hz k hk, zero_mul]]
  · have hw0 : ∀ k ∈ t, 0 ≤ q k / c := fun k hk => div_nonneg (hq k hk) hcpos.le
    have hw1 : ∑ k ∈ t, q k / c = 1 := by
      rw [← Finset.sum_div, hsum, div_self hcpos.ne']
    have hj := hf.map_sum_le hw0 hw1 hμ
    simp only [smul_eq_mul] at hj
    have hy : ∑ k ∈ t, q k / c * μ k = y := by
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, hmean, mul_div_cancel_left₀ _ hcpos.ne']
    have hfy : ∑ k ∈ t, q k / c * f (μ k) = (∑ k ∈ t, q k * f (μ k)) / c := by
      simp_rw [div_mul_eq_mul_div]
      rw [Finset.sum_div]
    rw [hy, hfy, le_div_iff₀ hcpos] at hj
    linarith

/-- Scalar Jensen inequality with unnormalized weights of total mass at most `c`, the
inequality in Wolf's Equation (5.53) for `∑ᵢ Tᵢ(1) ≤ 1` and `f(0) ≤ 0`: the missing mass is
placed at the point `0 ∈ I`. -/
theorem ConvexOn.mul_map_le_sum_of_sum_le {κ : Type*} {I : Set ℝ} {f : ℝ → ℝ}
    (hf : ConvexOn ℝ I f) (h0I : (0 : ℝ) ∈ I) (hf0 : f 0 ≤ 0) (t : Finset κ) {q μ : κ → ℝ}
    (hq : ∀ k ∈ t, 0 ≤ q k) (hμ : ∀ k ∈ t, μ k ∈ I) {c y : ℝ} (hsum : ∑ k ∈ t, q k ≤ c)
    (hmean : ∑ k ∈ t, q k * μ k = c * y) :
    c * f y ≤ ∑ k ∈ t, q k * f (μ k) := by
  classical
  let q' : Option κ → ℝ := fun o => o.elim (c - ∑ k ∈ t, q k) q
  let μ' : Option κ → ℝ := fun o => o.elim 0 μ
  have hq' : ∀ o ∈ t.insertNone, 0 ≤ q' o := by
    intro o ho
    cases o with
    | none => exact sub_nonneg.mpr hsum
    | some k => exact hq k (Finset.some_mem_insertNone.mp ho)
  have hμ' : ∀ o ∈ t.insertNone, μ' o ∈ I := by
    intro o ho
    cases o with
    | none => exact h0I
    | some k => exact hμ k (Finset.some_mem_insertNone.mp ho)
  have hsum' : ∑ o ∈ t.insertNone, q' o = c := by
    rw [Finset.sum_insertNone]
    simp [q']
  have hmean' : ∑ o ∈ t.insertNone, q' o * μ' o = c * y := by
    rw [Finset.sum_insertNone]
    simpa [q', μ'] using hmean
  have h := hf.mul_map_le_sum_of_sum_eq t.insertNone hq' hμ' hsum' hmean'
  rw [Finset.sum_insertNone] at h
  have hnone : q' none * f (μ' none) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hsum) hf0
  simp only [q', μ', Option.elim] at h hnone
  linarith

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The eigenspace projections of a Hermitian matrix are positive semidefinite. -/
private lemma spectralProj_posSemidef {A : Matrix m m ℂ} (hA : A.IsHermitian) (u : ℝ) :
    (hA.spectralProj u).PosSemidef := by
  rw [IsHermitian.spectralProj, ← hA.cfc_eq, ← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg fun x _ => by split_ifs <;> norm_num

/-- Every element of the eigenvalue set lies in the spectrum. -/
private lemma mem_spectrum_of_mem_eigenvalueSet {A : Matrix m m ℂ} (hA : A.IsHermitian)
    {u : ℝ} (hu : u ∈ hA.eigenvalueSet) : u ∈ spectrum ℝ A := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hu
  exact hA.eigenvalues_mem_spectrum_real i

omit [DecidableEq n] in
private lemma re_quad_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) (v : n → ℂ) :
    0 ≤ (star v ⬝ᵥ (M *ᵥ v)).re :=
  (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg v)).1

/-- The real trace of `S M S` as a sum of quadratic forms of `M` at the vectors `S eₖ`, for a
Hermitian `S` and the eigenbasis `eₖ` of a Hermitian `Y`. -/
private lemma re_trace_conj_eq_sum {Y S : Matrix n n ℂ} (hY : Y.IsHermitian)
    (hS : S.IsHermitian) (M : Matrix n n ℂ) :
    (S * M * S).trace.re = ∑ k, (star (S *ᵥ WithLp.ofLp (hY.eigenvectorBasis k)) ⬝ᵥ
      (M *ᵥ (S *ᵥ WithLp.ofLp (hY.eigenvectorBasis k)))).re := by
  rw [← hY.sum_re_quad_eq_trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [star_mulVec, hS.eq, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

/-- **Wolf's Theorem 5.17, Equation (5.51), with the corrected commutation hypothesis.**
Let `Tᵢ` be finitely many positive maps, `f` convex on `I`, `Xᵢ` Hermitian with spectra in
`I`, and `C` positive semidefinite commuting with `∑ᵢ Tᵢ(Xᵢ)`. If either `∑ᵢ Tᵢ(1) = 1`, or
`∑ᵢ Tᵢ(1) ≤ 1`, `0 ∈ I` and `f(0) ≤ 0`, then

`Re tr[C f(∑ᵢ Tᵢ(Xᵢ))] ≤ ∑ᵢ Re tr[C Tᵢ(f(Xᵢ))]`.

**Local fix (commutation hypothesis):** Wolf, Chapter 5, lines 1039–1078, asks only that `C`
commute with `f(∑ᵢ Tᵢ(Xᵢ))`; `Matrix.trace_jensen_commute_cfc_counterexample` shows that this
is insufficient, and the proof's Equation (5.52) uses commutation with `∑ᵢ Tᵢ(Xᵢ)`. The
condition `0 ∈ I` makes the source's `f(0)` meaningful. See
`docs/paper-gaps/wolf_ch5_trace_jensen_commutation.tex`. -/
theorem re_trace_mul_cfc_sum_map_le_of_commute {ι : Type*} [Fintype ι]
    {T : ι → Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ} (hT : ∀ i, IsPositiveMap (T i))
    {I : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {X : ι → Matrix m m ℂ} (hX : ∀ i, (X i).IsHermitian) (hXI : ∀ i, spectrum ℝ (X i) ⊆ I)
    {C : Matrix n n ℂ} (hC : C.PosSemidef) (hCY : Commute C (∑ i, T i (X i)))
    (hnorm : ∑ i, T i 1 = 1 ∨ (∑ i, T i 1 ≤ 1 ∧ (0 : ℝ) ∈ I ∧ f 0 ≤ 0)) :
    (C * cfc f (∑ i, T i (X i))).trace.re ≤ ∑ i, (C * T i (cfc f (X i))).trace.re := by
  set Y := ∑ i, T i (X i) with hYdef
  have hY : Y.IsHermitian := by
    rw [hYdef]
    exact (isSelfAdjoint_sum Finset.univ fun i _ =>
      ((hT i).map_isHermitian (hX i)).isSelfAdjoint).isHermitian
  -- Reduce the right-hand side to a single trace.
  have hR : ∑ i, (C * T i (cfc f (X i))).trace.re =
      (C * ∑ i, T i (cfc f (X i))).trace.re := by
    rw [Finset.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [hR]
  -- The square root of `C` commutes with `Y` and with `f(Y)`.
  set S := CFC.sqrt C with hSdef
  have hC0 : 0 ≤ C := hC.nonneg
  have hS : S.IsHermitian := (CFC.sqrt_nonneg C).isSelfAdjoint.isHermitian
  have hSS : S * S = C := CFC.sqrt_mul_sqrt_self C hC0
  have hYS : Commute Y S := by
    rw [hSdef, CFC.sqrt_eq_real_sqrt C hC0, cfcₙ_eq_cfc]
    exact (Commute.cfc hCY (by rw [hC.isHermitian.isSelfAdjoint.star_eq]; exact hCY)
      Real.sqrt).symm
  have hfYS : Commute (cfc f Y) S :=
    Commute.cfc hYS (by rw [hY.isSelfAdjoint.star_eq]; exact hYS) f
  have htr : ∀ M : Matrix n n ℂ, (C * M).trace.re = (S * M * S).trace.re := by
    intro M
    rw [← hSS, Matrix.mul_assoc, Matrix.trace_mul_comm S, Matrix.mul_assoc]
  rw [htr, htr, re_trace_conj_eq_sum hY hS, re_trace_conj_eq_sum hY hS]
  refine Finset.sum_le_sum fun k _ => ?_
  set e : n → ℂ := WithLp.ofLp (hY.eigenvectorBasis k)
  set v : n → ℂ := S *ᵥ e with hv
  set y : ℝ := hY.eigenvalues k
  have hYv : Y *ᵥ v = (y : ℂ) • v := by
    rw [hv, mulVec_mulVec, hYS.eq, ← mulVec_mulVec, hY.mulVec_eigenvectorBasis,
      RCLike.real_smul_eq_coe_smul (K := ℂ), mulVec_smul]
    rfl
  have hfYv : cfc f Y *ᵥ v = (f y : ℂ) • v := by
    rw [hv, mulVec_mulVec, hfYS.eq, ← mulVec_mulVec, hY.cfc_mulVec_eigenvectorBasis,
      mulVec_smul]
  set t : ℝ := (star v ⬝ᵥ v).re
  have hL : (star v ⬝ᵥ (cfc f Y *ᵥ v)).re = t * f y := by
    rw [hfYv, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, mul_comm]
  have hmeanY : (star v ⬝ᵥ (Y *ᵥ v)).re = t * y := by
    rw [hYv, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul, mul_comm]
  -- Spectral weights of `v` with respect to the family `Tᵢ` and the eigenprojections of `Xᵢ`.
  let κ := Σ i : ι, (hX i).eigenvalueSet
  let q : κ → ℝ := fun p => (star v ⬝ᵥ (T p.1 ((hX p.1).spectralProj p.2) *ᵥ v)).re
  let μ : κ → ℝ := fun p => p.2
  have hquad : ∀ g : ℝ → ℝ,
      (star v ⬝ᵥ ((∑ i, T i (cfc g (X i))) *ᵥ v)).re = ∑ p, q p * g (μ p) := by
    intro g
    rw [re_dotProduct_sum_mulVec, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hX i).cfc_eq, (hX i).cfc_eq_sum_smul_spectralProj g, map_sum,
      re_dotProduct_sum_mulVec]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, Complex.coe_smul, re_dotProduct_smul_mulVec, mul_comm]
  have hq : ∀ p ∈ (Finset.univ : Finset κ), 0 ≤ q p := fun p _ =>
    re_quad_nonneg ((hT p.1) _ (spectralProj_posSemidef (hX p.1) p.2)) v
  have hμ : ∀ p ∈ (Finset.univ : Finset κ), μ p ∈ I := fun p _ =>
    hXI p.1 (mem_spectrum_of_mem_eigenvalueSet (hX p.1) p.2.2)
  have hsumq : ∑ p, q p = (star v ⬝ᵥ ((∑ i, T i 1) *ᵥ v)).re := by
    have h := hquad (fun _ => 1)
    simp only [mul_one] at h
    rw [← h]
    congr 3
    exact Finset.sum_congr rfl fun i _ => by rw [cfc_const_one ℝ (X i)]
  have hmean : ∑ p, q p * μ p = t * y := by
    have h := hquad id
    simp only [id_eq] at h
    rw [← h, ← hmeanY]
    congr 3
    exact Finset.sum_congr rfl fun i _ => by rw [cfc_id' ℝ (X i) (hX i).isSelfAdjoint]
  have hZ : ∑ p, q p * f (μ p) = (star v ⬝ᵥ ((∑ i, T i (cfc f (X i))) *ᵥ v)).re :=
    (hquad f).symm
  rw [hL, ← hZ]
  rcases hnorm with h1 | ⟨h1, h0I, hf0⟩
  · refine hf.mul_map_le_sum_of_sum_eq Finset.univ hq hμ ?_ hmean
    rw [hsumq, h1, one_mulVec]
  · refine hf.mul_map_le_sum_of_sum_le h0I hf0 Finset.univ hq hμ ?_ hmean
    rw [hsumq]
    have hpsd := re_quad_nonneg (Matrix.le_iff.mp h1) v
    rw [sub_mulVec, dotProduct_sub, Complex.sub_re, one_mulVec, sub_nonneg] at hpsd
    exact hpsd

end Matrix

namespace Matrix

/-! ### The printed commutation hypothesis is insufficient -/

/-- Positive semidefinite weights summing to the identity, used in
`Matrix.trace_jensen_commute_cfc_counterexample`. -/
private def traceJensenCexWeight : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => (1 / 16 : ℝ) • (vecMulVec ![2, 1] (star ![2, 1]) + diagonal ![5, 0])
  | 1 => (1 / 16 : ℝ) • (vecMulVec ![1, 2] (star ![1, 2]) + diagonal ![0, 5])
  | 2 => (1 / 16 : ℝ) • (vecMulVec ![2, -2] (star ![2, -2]) + diagonal ![2, 2])

private lemma traceJensenCexWeight_posSemidef (i : Fin 3) :
    (traceJensenCexWeight i).PosSemidef := by
  have h16 : (0 : ℝ) ≤ 1 / 16 := by norm_num
  fin_cases i <;> exact ((posSemidef_vecMulVec_self_star _).add (by simp)).smul h16

/-- The positive map `M₁ → M₂`, `x ↦ x Pᵢ`, used in
`Matrix.trace_jensen_commute_cfc_counterexample`. -/
private def traceJensenCexMap (i : Fin 3) :
    Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := X 0 0 • traceJensenCexWeight i
  map_add' X Y := by simp [add_smul]
  map_smul' c X := by simp [mul_smul]

/-- **The printed hypothesis of Wolf's Theorem 5.17 is insufficient.** There are positive maps
`Tᵢ : M₁ → M₂` with `∑ᵢ Tᵢ(1) = 1`, the convex function `|x|` on `[-2, 2]`, scalars
`Xᵢ ∈ {2, -2, 0}`, and a positive semidefinite `C` commuting with `f(∑ᵢ Tᵢ(Xᵢ))` such that
`∑ᵢ Re tr[C Tᵢ(f(Xᵢ))] < Re tr[C f(∑ᵢ Tᵢ(Xᵢ))]`.

Here `∑ᵢ Tᵢ(Xᵢ) = diag(1, -1)`, so `f(∑ᵢ Tᵢ(Xᵢ)) = 1` commutes with every `C`; the vector
`(1, -1)` is not an eigenvector of `∑ᵢ Tᵢ(Xᵢ)`. This contradicts Wolf, Chapter 5,
Theorem 5.17, Equation (5.51), lines 1039–1055, as printed; see
`docs/paper-gaps/wolf_ch5_trace_jensen_commutation.tex`. -/
theorem trace_jensen_commute_cfc_counterexample :
    ∃ (T : Fin 3 → Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
      (X : Fin 3 → Matrix (Fin 1) (Fin 1) ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ i, IsPositiveMap (T i)) ∧ ∑ i, T i 1 = 1 ∧
      ConvexOn ℝ (Set.Icc (-2) 2) (fun x : ℝ => |x|) ∧
      (∀ i, (X i).IsHermitian) ∧ (∀ i, spectrum ℝ (X i) ⊆ Set.Icc (-2) 2) ∧
      C.PosSemidef ∧ Commute C (cfc (fun x : ℝ => |x|) (∑ i, T i (X i))) ∧
      ∑ i, (C * T i (cfc (fun x : ℝ => |x|) (X i))).trace.re <
        (C * cfc (fun x : ℝ => |x|) (∑ i, T i (X i))).trace.re := by
  let x : Fin 3 → ℝ := ![2, -2, 0]
  let X : Fin 3 → Matrix (Fin 1) (Fin 1) ℂ := fun i => algebraMap ℝ _ (x i)
  let C : Matrix (Fin 2) (Fin 2) ℂ := vecMulVec ![1, -1] (star ![1, -1])
  have hY : ∑ i, traceJensenCexMap i (X i) = diagonal (fun j => ((![1, -1] j : ℝ) : ℂ)) := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [traceJensenCexMap, traceJensenCexWeight, X, x, Fin.sum_univ_three, vecMulVec,
        algebraMap_matrix_apply, map_ofNat] <;> norm_num
  have hfY : cfc (fun x : ℝ => |x|) (∑ i, traceJensenCexMap i (X i)) = 1 := by
    rw [hY, cfc_diagonal _ (fun x : ℝ => |x|) continuous_abs.continuousOn]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  refine ⟨traceJensenCexMap, X, C, ?_, ?_, convexOn_norm (convex_Icc _ _), ?_, ?_,
    posSemidef_vecMulVec_self_star _, ?_, ?_⟩
  · intro i A hA
    exact (traceJensenCexWeight_posSemidef i).smul hA.diag_nonneg
  · ext a b
    fin_cases a <;> fin_cases b <;>
      simp [traceJensenCexMap, traceJensenCexWeight, Fin.sum_univ_three, vecMulVec,
        map_ofNat] <;> norm_num
  · intro i
    exact (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all (x i))).isHermitian
  · intro i
    rw [spectrum.scalar_eq]
    fin_cases i <;> simp [x]
  · rw [hfY]
    exact Commute.one_right C
  · have hC : C = !![1, -1; -1, 1] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [C, vecMulVec]
    have hZ : ∑ i, traceJensenCexMap i (cfc (fun x : ℝ => |x|) (X i)) =
        !![(5 / 4 : ℂ), 1 / 2; 1 / 2, 5 / 4] := by
      simp only [X, cfc_algebraMap]
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [traceJensenCexMap, traceJensenCexWeight, x, Fin.sum_univ_three, vecMulVec,
          algebraMap_matrix_apply, map_ofNat] <;> norm_num
    rw [hfY, ← Complex.re_sum, ← trace_sum, ← Finset.mul_sum, hZ, hC]
    simp [trace_fin_two]
    norm_num

end Matrix
