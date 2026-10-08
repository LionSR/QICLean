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

variable {H : Type*} [DecidableEq H] {C : H → Type*} [∀ h, DecidableEq (C h)]

/-- Terminal weight `π_{(h,old)} = (1 - p) w_h` (`06-transport.tex`, display
`transport:terminal-weights`). -/
theorem weight_interpTree_old (T : MeanTree H) (S : ∀ h, MeanTree (C h)) (p : I) (h : H) :
    (interpTree T S p).weight ⟨h, none⟩ = (1 - (p : ℝ)) * T.weight h := by
  sorry

/-- Terminal weight `π_{(h,c,new)} = p w_h q_{c|h}` (`06-transport.tex`, display
`transport:terminal-weights`). -/
theorem weight_interpTree_new (T : MeanTree H) (S : ∀ h, MeanTree (C h)) (p : I) (h : H)
    (c : C h) :
    (interpTree T S p).weight ⟨h, some c⟩ = (p : ℝ) * T.weight h * (S h).weight c := by
  sorry

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

/-- Moving a positive map to its trace adjoint: `⟨w, Φ(Z) w⟩ = Tr(Φ^*(|w⟩⟨w|) Z)`
(`06-transport.tex` lines 490--494). -/
theorem star_dotProduct_mulVec_eq_trace_traceAdjointMap
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (Z : Matrix n n ℂ) (w : n → ℂ) :
    star w ⬝ᵥ (Φ Z *ᵥ w) = (traceAdjointMap Φ (vecMulVec w (star w)) * Z).trace := by
  sorry

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

/-- The transport states are density matrices (`06-transport.tex` line 491, from
Lemma 7.2): positive semidefinite, with trace `‖v‖²`. -/
theorem posSemidef_transportState {J : Type*} [DecidableEq J] {T' : MeanTree J}
    {A : J → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) (v : n → ℂ) (j : J) (u : ℝ) :
    (transportState T' A v j u).PosSemidef := by
  sorry

theorem trace_transportState {J : Type*} [DecidableEq J] {T' : MeanTree J}
    {A : J → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef) {j : J} (hw : T'.weight j ≠ 0)
    (v : n → ℂ) (u : ℝ) :
    (transportState T' A v j u).trace = star v ⬝ᵥ v := by
  sorry

/-- `N²` is positive and continuous on `[0, 1]` (`06-transport.tex` lines 769--771). -/
theorem continuous_filteredNormSq_interpPath {T : MeanTree H} {S : ∀ h, MeanTree (C h)}
    {A : H → Matrix n n ℂ} {A' : ∀ h, C h → Matrix n n ℂ} (hA : ∀ h, (A h).PosDef)
    (hA' : ∀ h c, (A' h c).PosDef) (pre : n → ℂ) :
    Continuous fun q => filteredNormSq (interpPath T S A A' q) pre := by
  sorry

theorem filteredNormSq_pos {M : Matrix n n ℂ} (hM : M.PosDef) {pre : n → ℂ} (hpre : pre ≠ 0) :
    0 < filteredNormSq M pre := by
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
