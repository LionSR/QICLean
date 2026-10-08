/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Defs

/-!
# The exact derivative of the filtered norm

For the interpolated tree of one round, with root `M(p)` and a nonzero vector `pre`,
$$-\partial_p\log N(p)^2=\sum_h w_h\int_{\mathbb R}m_{1/4}(u)
  \operatorname{Tr}(\sigma_{h,u}\log C_h)\,du$$
(area-law paper, Proposition 7.4, display `transport:exact-derivative`,
`06-transport.tex` lines 402--408, proof lines 438--494).

The proof is split as in the source:

* the terminal weights of the interpolated tree (lines 275--286);
* the derivative at an interpolating vertex and at the root,
  `M^{-1/2} ∂_p M M^{-1/2} = ∑_h w_h Φ_{(h,old)}(log C_h)` (lines 442--468);
* the derivative of the norm through the Fourier multiplier `g_{1/4}` (lines 470--489);
* passage to the trace adjoint (lines 490--494);
* continuity of `N` on `[0, 1]` and integration over closed subintervals (lines 769--779).

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open MeasureTheory Set

namespace Matrix

namespace MeanTree

section Bind

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The weight of a label after substitution, when only the subtree at `h₀` carries it. -/
theorem weight_bind_of_forall_ne (T : MeanTree ι) {f : ι → MeanTree κ} {h₀ : ι} {j : κ}
    (hf : ∀ h ≠ h₀, (f h).weight j = 0) : (T.bind f).weight j = T.weight h₀ * (f h₀).weight j := by
  induction T with
  | leaf h =>
    by_cases hh : h = h₀
    · subst hh; simp [bind]
    · simp [bind, hf h hh, Pi.single_eq_of_ne' hh]
  | node p l r ihl ihr =>
    simp only [bind, weight_node, ihl, ihr]; ring

omit [DecidableEq ι] in
/-- The weight of a label carried by no substituted subtree is zero. -/
theorem weight_bind_eq_zero (T : MeanTree ι) {f : ι → MeanTree κ} {j : κ}
    (hf : ∀ h, (f h).weight j = 0) : (T.bind f).weight j = 0 := by
  induction T with
  | leaf h => exact hf h
  | node p l r ihl ihr => simp only [bind, weight_node, ihl, ihr]; ring

theorem weight_map_apply (T : MeanTree ι) {g : ι → κ} (hg : Function.Injective g) (c : ι) :
    (T.map g).weight (g c) = T.weight c := by
  rw [map, weight_bind_of_forall_ne T (h₀ := c)]
  · simp
  · intro h hh
    simp [Pi.single_eq_of_ne' (hg.ne hh)]

theorem weight_map_of_forall_ne (T : MeanTree ι) {g : ι → κ} {j : κ} (hj : ∀ c, g c ≠ j) :
    (T.map g).weight j = 0 :=
  weight_bind_eq_zero T fun h => by simp [Pi.single_eq_of_ne' (hj h)]

end Bind

variable {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)]

/-- Terminal weight `π_{(h,old)} = (1 - p) w_h` (`06-transport.tex`, display
`transport:terminal-weights`). -/
theorem weight_interpTree_old (T : MeanTree H) (S : ∀ h, MeanTree (C h)) (p : I) (h : H) :
    (interpTree T S p).weight ⟨h, none⟩ = (1 - (p : ℝ)) * T.weight h := by
  rw [interpTree, weight_bind_of_forall_ne T (h₀ := h)]
  · rw [weight_node, weight_map_of_forall_ne _ (by simp)]
    simp; ring
  · intro h' hh'
    rw [weight_node, weight_map_of_forall_ne _ (by simp [hh'])]
    simp [Pi.single_eq_of_ne' (by simp [hh'] : (⟨h', none⟩ : Σ h, Option (C h)) ≠ ⟨h, none⟩)]

/-- Terminal weight `π_{(h,c,new)} = p w_h q_{c|h}` (`06-transport.tex`, display
`transport:terminal-weights`). -/
theorem weight_interpTree_new (T : MeanTree H) (S : ∀ h, MeanTree (C h)) (p : I) (h : H)
    (c : C h) :
    (interpTree T S p).weight ⟨h, some c⟩ = (p : ℝ) * T.weight h * (S h).weight c := by
  rw [interpTree, weight_bind_of_forall_ne T (h₀ := h)]
  · rw [weight_node, weight_map_apply (S h) (g := fun c => (⟨h, some c⟩ : Σ h, Option (C h)))
      (fun a b hab => by simpa using hab)]
    simp; ring
  · intro h' hh'
    rw [weight_node, weight_map_of_forall_ne _ (by simp [hh'])]
    simp [Pi.single_eq_of_ne' (by simp [hh'] : (⟨h', none⟩ : Σ h, Option (C h)) ≠ ⟨h, some c⟩)]

end MeanTree

namespace Transport

open MeanTree

variable {n : Type*} [Fintype n] [DecidableEq n]
  {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*} [∀ h, Fintype (C h)]
  [∀ h, DecidableEq (C h)]

/-- The interpolation path `q ↦ M(proj q)` on the real line, clamped to `[0, 1]`. -/
noncomputable def interpPath (T : MeanTree H) (S : ∀ h, MeanTree (C h))
    (A : H → Matrix n n ℂ) (A' : ∀ h, C h → Matrix n n ℂ) (q : ℝ) : Matrix n n ℂ :=
  interpRoot T S A A' (projIcc (0 : ℝ) 1 zero_le_one q)

theorem posDef_interpRoot {T : MeanTree H} {S : ∀ h, MeanTree (C h)} {A : H → Matrix n n ℂ}
    {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef) (hA' : ∀ h c, (A' h c).PosDef)
    (p : I) : (interpRoot T S A A' p).PosDef :=
  posDef_eval (fun j => match j with
    | ⟨h, none⟩ => hA h
    | ⟨h, some c⟩ => hA' h c) _

/-- **The derivative at the root** (`06-transport.tex`, displays
`transport:node-p-derivative` and `transport:root-p-derivative`, lines 442--468):
`𝖧 = M^{-1/2} ∂_p M M^{-1/2} = ∑_h w_h Φ_{(h,old)}(log C_h)`. The coefficient is `w_h`,
not the terminal weight `(1 - p) w_h`. -/
theorem exists_hasDerivAt_interpPath {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (hT : ∀ h, 0 < T.weight h) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    ∃ D : Matrix n n ℂ, HasDerivAt (interpPath T S A A') D p ∧
      interpPath T S A A' p ^ (-(1 / 2) : ℝ) * D * interpPath T S A A' p ^ (-(1 / 2) : ℝ) =
        ∑ h, T.weight h • (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)).leafMap
          (interpInput A A') ⟨h, none⟩ (CFC.log (relRatio S A A' h)) := by
  sorry

/-- **The derivative of the filtered norm** (`06-transport.tex`, display
`transport:norm-derivative` and the Fourier formula `transport:g-fourier`,
lines 470--491): for a differentiable path of positive definite matrices with
`M(p)^{-1/2} M'(p) M(p)^{-1/2} = 𝖧`,
`-∂_p log N² = ∫ m_{1/4}(u) ⟨M^{-iu} v, 𝖧 M^{-iu} v⟩ du`. -/
theorem hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt {M : ℝ → Matrix n n ℂ}
    {D : Matrix n n ℂ} {p : ℝ} (hM : ∀ q, (M q).PosDef) (hD : HasDerivAt M D p)
    {pre : n → ℂ} (hpre : pre ≠ 0) :
    HasDerivAt (fun q => -Real.log (filteredNormSq (M q) pre))
      (∫ u, fourierWeight u *
        (star (imagPow (M p) u *ᵥ filteredVector (M p) pre) ⬝ᵥ
          ((M p ^ (-(1 / 2) : ℝ) * D * M p ^ (-(1 / 2) : ℝ)) *ᵥ
            (imagPow (M p) u *ᵥ filteredVector (M p) pre))).re) p := by
  sorry

omit [DecidableEq n] in
/-- Moving a positive map to its trace adjoint: `⟨w, Φ(Z) w⟩ = Tr(Φ^*(|w⟩⟨w|) Z)`
(`06-transport.tex` lines 490--494). -/
theorem star_dotProduct_mulVec_eq_trace_traceAdjointMap
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (Z : Matrix n n ℂ) (w : n → ℂ) :
    star w ⬝ᵥ (Φ Z *ᵥ w) = (traceAdjointMap Φ (vecMulVec w (star w)) * Z).trace := by
  rw [trace_traceAdjointMap_mul, vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec,
    dotProduct_comm]

/-- **Exact derivative** (area-law paper, Proposition 7.4, display
`transport:exact-derivative`, `06-transport.tex` lines 402--408): for `0 < p < 1` and
nonzero `pre`,
`-∂_p log N(p)² = ∑_h w_h ∫ m_{1/4}(u) Tr(σ_{h,u} log C_h) du`. -/
theorem hasDerivAt_neg_log_filteredNormSq {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (hT : ∀ h, 0 < T.weight h) {p : ℝ} (hp : p ∈ Ioo 0 1)
    {pre : n → ℂ} (hpre : pre ≠ 0) :
    HasDerivAt (fun q => -Real.log (filteredNormSq (interpPath T S A A' q) pre))
      (∑ h, T.weight h * ∫ u, fourierWeight u *
        (transportState (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)) (interpInput A A')
            (filteredVector (interpPath T S A A' p) pre) ⟨h, none⟩ u *
          CFC.log (relRatio S A A' h)).trace.re) p := by
  obtain ⟨D, hD, hDH⟩ := exists_hasDerivAt_interpPath hA hA' hT hp
  have hM : ∀ q, (interpPath T S A A' q).PosDef := fun q => posDef_interpRoot hA hA' _
  have h1 := hasDerivAt_neg_log_filteredNormSq_of_hasDerivAt hM hD hpre
  convert h1 using 1
  -- Insert `transport:root-p-derivative` and move each leaf map to its trace adjoint.
  sorry

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] in
/-- `M^{-iu}` is unitary. -/
theorem conjTranspose_imagPow_mul_imagPow (M : Matrix n n ℂ) (u : ℝ) :
    (imagPow M u)ᴴ * imagPow M u = 1 := by
  have hlog : (CFC.log M).IsHermitian := by
    unfold CFC.log; exact cfc_predicate _ _
  exact mul_eq_one_comm.mp (hermitianUnitaryPath_mul_conjTranspose _ hlog _)

/-- The transport states are density matrices (`06-transport.tex` line 491, from
Lemma 7.2): positive semidefinite, with trace `‖v‖²`. -/
theorem posSemidef_transportState {J : Type*} [DecidableEq J] {T' : MeanTree J}
    {A : J → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) (v : n → ℂ) (j : J) (u : ℝ) :
    (transportState T' A v j u).PosSemidef :=
  posSemidef_traceAdjoint_leafMap hA T' j (posSemidef_vecMulVec_self_star _)

theorem trace_transportState {J : Type*} [DecidableEq J] {T' : MeanTree J}
    {A : J → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) {j : J} (hw : T'.weight j ≠ 0)
    (v : n → ℂ) (u : ℝ) :
    (transportState T' A v j u).trace = star v ⬝ᵥ v := by
  rw [transportState, trace_traceAdjoint_leafMap hA T' hw, trace_vecMulVec, dotProduct_comm,
    star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, conjTranspose_imagPow_mul_imagPow, one_mulVec]

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] in
theorem filteredNormSq_pos {M : Matrix n n ℂ} (hM : M.PosDef) {pre : n → ℂ} (hpre : pre ≠ 0) :
    0 < filteredNormSq M pre := by
  have hne : filteredRaw M pre ≠ 0 := by
    intro h0
    apply hpre
    have : M ^ (1 / 4 : ℝ) *ᵥ filteredRaw M pre = pre := by
      rw [filteredRaw, mulVec_mulVec, hM.rpow_mul_rpow_neg, one_mulVec]
    rw [← this, h0, mulVec_zero]
  exact (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hne)).1

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] in
/-- `star (M^{-1/4} pre) ⬝ᵥ M^{-1/4} pre = N²` as a complex number. -/
theorem star_dotProduct_filteredRaw (M : Matrix n n ℂ) (pre : n → ℂ) :
    star (filteredRaw M pre) ⬝ᵥ filteredRaw M pre = (filteredNormSq M pre : ℂ) := by
  have h0 : 0 ≤ star (filteredRaw M pre) ⬝ᵥ filteredRaw M pre := dotProduct_star_self_nonneg _
  apply Complex.ext
  · simp [filteredNormSq]
  · simpa [filteredNormSq] using (Complex.nonneg_iff.mp h0).2.symm

omit [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] in
/-- The filtered vector is a unit vector. -/
theorem star_dotProduct_filteredVector {M : Matrix n n ℂ} (hM : M.PosDef) {pre : n → ℂ}
    (hpre : pre ≠ 0) : star (filteredVector M pre) ⬝ᵥ filteredVector M pre = 1 := by
  have hN := filteredNormSq_pos hM hpre
  rw [filteredVector, star_smul, smul_dotProduct, dotProduct_smul, star_dotProduct_filteredRaw]
  simp only [smul_eq_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← mul_assoc,
    ← mul_inv, Real.mul_self_sqrt hN.le, inv_mul_cancel₀ hN.ne', Complex.ofReal_one]

/-- `N²` is positive and continuous on `[0, 1]` (`06-transport.tex` lines 769--771). -/
theorem continuous_filteredNormSq_interpPath {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (pre : n → ℂ) :
    Continuous fun q => filteredNormSq (interpPath T S A A' q) pre := by
  sorry

/-- **Integration over a closed subinterval** (`06-transport.tex` lines 427--429 and
769--779): the derivative of `-log N²` is interval integrable on `[p₀, p₁] ⊆ [0, 1]`, and
its integral is the difference of the continuous endpoint values. -/
theorem log_filteredNormSq_sub_eq_integral {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (hT : ∀ h, 0 < T.weight h) {pre : n → ℂ} (hpre : pre ≠ 0)
    {p₀ p₁ : ℝ} (h0 : 0 ≤ p₀) (h01 : p₀ ≤ p₁) (h1 : p₁ ≤ 1) :
    IntervalIntegrable (fun p => ∑ h, T.weight h * ∫ u, fourierWeight u *
        (transportState (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)) (interpInput A A')
            (filteredVector (interpPath T S A A' p) pre) ⟨h, none⟩ u *
          CFC.log (relRatio S A A' h)).trace.re) volume p₀ p₁ ∧
    Real.log (filteredNormSq (interpPath T S A A' p₀) pre) -
        Real.log (filteredNormSq (interpPath T S A A' p₁) pre) =
      ∫ p in p₀..p₁, ∑ h, T.weight h * ∫ u, fourierWeight u *
        (transportState (interpTree T S (projIcc (0 : ℝ) 1 zero_le_one p)) (interpInput A A')
            (filteredVector (interpPath T S A A' p) pre) ⟨h, none⟩ u *
          CFC.log (relRatio S A A' h)).trace.re := by
  sorry

end Transport

end Matrix
