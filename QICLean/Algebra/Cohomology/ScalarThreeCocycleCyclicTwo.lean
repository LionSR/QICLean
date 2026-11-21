/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import QICLean.Algebra.Cohomology.LSymbol
import QICLean.Algebra.Cohomology.ScalarThreeCocycleInversion

/-!
# Scalar three-cocycles for Z₂

This file proves the scalar part of the Z₂ anomaly calculation in
arXiv:2502.20257, Appendix `app:Z2`, lines 5327--5341. It identifies the
inversion scalar with a ratio of normalized L-symbols and classifies normalized
scalar three-cocycles on `Multiplicative (ZMod 2)` by their value at the
nonidentity generator.

The explicit representatives `ωₚ(a,b,c) = (-1)^(pabc)`, for `p = 0, 1`, are normalized,
unit-modulus scalar three-cocycles with distinct gauge classes. Here `a, b, c` are bits, written
multiplicatively as elements of `Multiplicative (ZMod 2)`; only the triple of nonidentity
elements can carry a value other than one.

## References

* arXiv:2502.20257, Appendix `app:Z2`, lines 5327--5341.
* arXiv:2405.00439, lines 1676--1778, equation `3cocycleeq` and the coboundary convention.

Moved from TNLean, `TNLean/Algebra/ScalarThreeCocycleCyclicTwo.lean` and
`TNLean/Algebra/ScalarThreeCocycleCyclicTwoExamples.lean` at commit `49b78ed821`
(Apache-2.0).
Changes: the two modules are merged; the `TNLean` namespace prefix is dropped; docstrings
rewritten.
-/

variable {G : Type} {X : Type*} [Group G] [MulAction G X]

namespace LSymbol

/-- For normalized L-symbols, the inversion scalar is the ratio

`σ(g) = Lˣ_{g⁻¹,g} / L^{g • x}_{g,g⁻¹}`.

This is the scalar calculation after `eq:sigmadiag` in arXiv:2502.20257,
Appendix `app:Z2`, lines 5327--5329. -/
theorem sigma_eq_div {L : LSymbol G X} {ω : ScalarThreeCochain G}
    (hL : IsCompatible L ω) (hLn : IsNormalized L) (x : X) (g : G) :
    ScalarThreeCochain.sigma ω g = L x g⁻¹ g / L (g • x) g g⁻¹ := by
  have h := hL x g g⁻¹ g
  simp only [inv_mul_cancel, mul_inv_cancel, hLn.1, hLn.2, one_mul, mul_one] at h
  simp only [ScalarThreeCochain.sigma, div_eq_mul_inv, h]
  group

end LSymbol

namespace ScalarThreeCochain

local notation "s₂" => (Multiplicative.ofAdd 1 : Multiplicative (ZMod 2))

private lemma z2_cases (g : Multiplicative (ZMod 2)) : g = 1 ∨ g = s₂ := by
  revert g
  decide

private lemma z2_generator_inv : s₂⁻¹ = s₂ := by
  decide

private lemma z2_generator_mul_self : s₂ * s₂ = 1 := by
  decide

/-- A normalized scalar three-cochain on Z₂ has trivial gauge class exactly
when its inversion scalar at the nonidentity generator is one.

For the forward implication, the gauge two-cochain need not be normalized.
Normalization of its coboundary instead forces both identity-axis restrictions
to equal one common constant, by `isNormalized_coboundary_iff`; at the triple
of nonidentity elements this constant and the remaining self-pair factor
cancel. This formalizes the normalized-cochain classification used in
arXiv:2502.20257, Appendix `app:Z2`, lines 5340--5341. -/
theorem isTrivialGaugeClass_iff_sigma_generator_eq_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2))} (hωn : IsNormalized ω) :
    IsTrivialGaugeClass ω ↔ sigma ω s₂ = 1 := by
  constructor
  · rintro ⟨β, hβ⟩
    have hcob_eq : coboundary β = ω := by
      funext g h k
      simpa only [fusionGauge, mul_one] using congrFun (congrFun (congrFun hβ g) h) k
    have hcob : IsNormalized (coboundary β) := hcob_eq ▸ hωn
    obtain ⟨c, hleft, hright⟩ := (isNormalized_coboundary_iff β).1 hcob
    have hvalue := congrFun (congrFun (congrFun hβ s₂) s₂) s₂
    simp only [fusionGauge, coboundary, z2_generator_mul_self, hleft, hright,
      mul_one] at hvalue
    simp only [sigma, z2_generator_inv, ← hvalue]
    rw [mul_comm c]
    exact div_self' _
  · intro hsigma
    have hω : ω = fun _ _ _ => 1 := by
      funext g h k
      rcases z2_cases g with rfl | rfl <;>
        rcases z2_cases h with rfl | rfl <;>
          rcases z2_cases k with rfl | rfl
      all_goals first
        | simp only [hωn.1, hωn.2.1, hωn.2.2]
        | simpa only [sigma, z2_generator_inv] using hsigma
    rw [hω]
    exact CohomologousTo.refl _

/-- The inversion scalar of a normalized scalar three-cocycle on Z₂ is either
one or minus one. This is the scalar counterpart of the two signs stated in
arXiv:2502.20257, Appendix `app:Z2`, lines 5335 and 5340. -/
theorem sigma_generator_eq_one_or_eq_neg_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2))} (hω : IsCocycle ω)
    (hωn : IsNormalized ω) :
    sigma ω s₂ = 1 ∨ sigma ω s₂ = -1 := by
  have hinv := sigma_inv ω hω hωn s₂
  rw [z2_generator_inv] at hinv
  exact (Units.inv_eq_self_iff _).mp hinv.symm

/-- A normalized scalar three-cocycle on Z₂ has nontrivial gauge class exactly
when its inversion scalar at the nonidentity generator is minus one.

This is the scalar cohomology step in the proof at arXiv:2502.20257,
Appendix `app:Z2`, lines 5340--5341. -/
theorem not_isTrivialGaugeClass_iff_sigma_generator_eq_neg_one
    {ω : ScalarThreeCochain (Multiplicative (ZMod 2))} (hω : IsCocycle ω)
    (hωn : IsNormalized ω) :
    ¬ IsTrivialGaugeClass ω ↔ sigma ω s₂ = -1 := by
  rw [not_congr (isTrivialGaugeClass_iff_sigma_generator_eq_one hωn)]
  rcases sigma_generator_eq_one_or_eq_neg_one hω hωn with hone | hneg
  · simp [hone]
  · simp [hneg]

/-! ### The explicit representatives `(-1)^(pabc)` -/

/-- The representative ωₚ(a,b,c) = (-1)^(pabc), with bit parameter p. -/
def cyclicTwoCocycle (p : Fin 2) : ScalarThreeCochain (Multiplicative (ZMod 2)) :=
  fun a b c => if a = s₂ ∧ b = s₂ ∧ c = s₂ then (-1) ^ p.val else 1

/-- The value of ωₚ on the generator triple is (-1)^p. -/
@[simp]
theorem cyclicTwoCocycle_generator (p : Fin 2) :
    cyclicTwoCocycle p s₂ s₂ s₂ = (-1) ^ p.val := by
  simp [cyclicTwoCocycle]

/-- The parameter zero gives the constant cocycle one. -/
@[simp]
theorem cyclicTwoCocycle_zero : cyclicTwoCocycle 0 = fun _ _ _ => 1 := by
  funext a b c
  simp [cyclicTwoCocycle]

/-- Each representative is normalized in all three arguments. -/
theorem cyclicTwoCocycle_isNormalized (p : Fin 2) :
    IsNormalized (cyclicTwoCocycle p) := by
  have h : (1 : Multiplicative (ZMod 2)) ≠ s₂ := by decide
  exact ⟨fun _ _ => by simp [cyclicTwoCocycle, h],
    fun _ _ => by simp [cyclicTwoCocycle, h],
    fun _ _ => by simp [cyclicTwoCocycle, h]⟩

/-- The representatives satisfy the scalar three-cocycle equation. -/
theorem cyclicTwoCocycle_isCocycle (p : Fin 2) : IsCocycle (cyclicTwoCocycle p) := by
  have hs : s₂ * s₂ = 1 := by decide
  have hn : (1 : Multiplicative (ZMod 2)) ≠ s₂ := by decide
  intro a b c d
  rcases z2_cases a with rfl | rfl <;>
    rcases z2_cases b with rfl | rfl <;>
      rcases z2_cases c with rfl | rfl <;>
        rcases z2_cases d with rfl | rfl <;>
          fin_cases p <;> simp [cyclicTwoCocycle, hs, hn]

/-- All values of the representatives are phases. -/
theorem cyclicTwoCocycle_norm (p : Fin 2) (a b c : Multiplicative (ZMod 2)) :
    ‖(cyclicTwoCocycle p a b c : ℂ)‖ = 1 := by
  unfold cyclicTwoCocycle
  split_ifs <;> simp

/-- The inversion scalar is precisely the sign (-1)^p. -/
@[simp]
theorem cyclicTwoCocycle_sigma_generator (p : Fin 2) :
    sigma (cyclicTwoCocycle p) s₂ = (-1) ^ p.val := by
  have hs : s₂⁻¹ = s₂ := by decide
  simp [sigma, hs]

/-- The sign-minus representative has nontrivial scalar gauge class, even when
arbitrary (not necessarily normalized) scalar two-cochains are allowed. -/
theorem cyclicTwoCocycle_one_not_isTrivialGaugeClass :
    ¬ IsTrivialGaugeClass (cyclicTwoCocycle 1) := by
  rw [isTrivialGaugeClass_iff_sigma_generator_eq_one (cyclicTwoCocycle_isNormalized 1)]
  simp

/-- The two explicit representatives are cohomologous exactly when their
parameters agree. The gauge two-cochain is not required to be normalized. -/
theorem cyclicTwoCocycle_cohomologousTo_iff (p q : Fin 2) :
    CohomologousTo (cyclicTwoCocycle p) (cyclicTwoCocycle q) ↔ p = q := by
  constructor
  · intro h
    fin_cases p <;> fin_cases q
    · rfl
    · exact False.elim (cyclicTwoCocycle_one_not_isTrivialGaugeClass
        (by
          change CohomologousTo (cyclicTwoCocycle 0) (cyclicTwoCocycle 1) at h
          simpa only [IsTrivialGaugeClass, cyclicTwoCocycle_zero] using h.symm))
    · exact False.elim (cyclicTwoCocycle_one_not_isTrivialGaugeClass
        (by
          change CohomologousTo (cyclicTwoCocycle 1) (cyclicTwoCocycle 0) at h
          simpa only [IsTrivialGaugeClass, cyclicTwoCocycle_zero] using h))
    · rfl
  · rintro rfl
    exact CohomologousTo.refl _

/-- A normalized gauge leaves the generator-triple sign unchanged. -/
theorem cyclicTwoCocycle_fusionGauge_generator (p : Fin 2)
    {β : ScalarCocycle (Multiplicative (ZMod 2))} (hβ : β.IsNormalized) :
    fusionGauge β (cyclicTwoCocycle p) s₂ s₂ s₂ = (-1) ^ p.val := by
  have hs : s₂ * s₂ = 1 := by decide
  simp [fusionGauge, coboundary, hs, hβ.1, hβ.2]

end ScalarThreeCochain
