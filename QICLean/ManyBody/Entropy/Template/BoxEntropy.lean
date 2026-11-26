/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Log
import QICLean.ManyBody.Entropy.Template.CappedDyadicEntropyCover
import QICLean.ManyBody.Sites.Template.CoreCounts
import QICLean.ManyBody.Sites.Template.ShellCover
import QICLean.ManyBody.Sites.Template.SafeRectangles
import QICLean.ManyBody.Entropy.Template.TemplateEntropy

/-!
# Template entropy from a safe-box estimate

The actual dyadic partition induces disjoint native rectangle regions whose union
is the physical filtered region. Subadditivity, the pointwise safe-box input,
and the proved weighted coverings bound the core and shells. The existing
partial-row theorem then bounds arbitrary prefixes. The input is an estimate
for every safe rectangle, not for the desired template regions.

These results use natural clearance. The final theorem additionally assumes
box estimates at every exponent in `(0, 1)`. The corresponding statement
at one fixed positive exponent and real clearance is proved by
`template_entropy_bounds_of_real_safe_box` in `TemplateBoxEntropyReal`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4, `08-scanner.tex`, lines 574–590 and 641–667,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Original formalization from the manuscript; no upstream Lean proof text reused.
This conditional entropy component does not assert the full lemma or derive
an arbitrary exponent from the initial existential safe-box exponent.
-/

open ManyBody (ambientDilation)

open ManyBody (IntRect IsSafe rectRegion)

namespace ManyBody

/-- Core entropy from a uniform estimate on every safe native rectangle.
The weighted count and safety are derived from the actual template. -/
theorem Template.regionEntropy_core_le_of_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1)
    (A : Finset ↥Λ) {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (K : ℕ) (hlo : 2 ^ K ≤ s₀) (hhi : s₀ < 2 ^ (K + 1))
    (e C : ℝ) (he : 0 < e) (hCbox : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      ManyBody.regionEntropy Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    ManyBody.regionEntropy Ω (A.filter fun x ↦ x.1 ∈ T.points) ≤
      C * (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e := by
  have h := regionEntropy_filter_le_weighted_cover Λ q D₀ Ω hΩ A T.points K e C
    (fun c hc ↦ hsep.isSafe_cappedDyadicPartition_core hD K c.1 c.2 hlo hc) hbox
  have hw := mul_le_mul_of_nonneg_left
    (T.sum_rpow_cappedDyadicPartition_core_le hC K hlo hhi e he) hCbox
  exact h.trans (by simpa only [mul_assoc] using hw)

/-- Shell entropy from the same safe-box estimate, including the empty shell. -/
theorem Template.regionEntropy_shell_le_of_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1)
    (A : Finset ↥Λ) {Ctpl : ℝ} {n s₀ : ℕ}
    (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j L K : ℕ) (hj : j ≤ L) (hL : L ≤ s₀)
    (hlo : 2 ^ K ≤ L) (hhi : L < 2 ^ (K + 1))
    (e C : ℝ) (he : 0 < e) (hCbox : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      ManyBody.regionEntropy Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    ManyBody.regionEntropy Ω
      (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points) ≤
      C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e := by
  have h := regionEntropy_filter_le_weighted_cover Λ q D₀ Ω hΩ A
    (ambientDilation T.points j \ T.points) K e C
    (fun c hc ↦ hsep.isSafe_cappedDyadicPartition_shell hD j K c.1 c.2
      (hj.trans hL) (hlo.trans hL) hc) hbox
  have hw := mul_le_mul_of_nonneg_left
    (T.sum_rpow_cappedDyadicPartition_shell_le hC j L K hj hL hlo hhi e he) hCbox
  exact h.trans (by simpa only [mul_assoc] using hw)

/-- A partial final row adds at most `n log q` to the shell entropy estimate.
This includes arbitrary subsets of that row; no row-order hypothesis is added. -/
theorem Template.regionEntropy_prefix_le_of_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (hq : 1 ≤ q)
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1) (A : Finset ↥Λ)
    {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀) (hC : 24 ≤ Ctpl)
    (hsep : T.IsSeparated D₀ (boundaryEndpoints Λ A)) (hD : 1 ≤ D₀)
    (j L K : ℕ) (hj : 1 ≤ j) (hjL : j ≤ L) (hL : L ≤ s₀)
    (hlo : 2 ^ K ≤ L) (hhi : L < 2 ^ (K + 1))
    (Y : Finset (ℤ × ℤ))
    (hY : Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1))
    (e C : ℝ) (he : 0 < e) (hCbox : 0 ≤ C)
    (hbox : ∀ Q : IntRect, IsSafe Λ A D₀ Q →
      ManyBody.regionEntropy Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    ManyBody.regionEntropy Ω
      (A.filter fun x ↦ x.1 ∈ (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
      C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e + n * Real.log q := by
  have hs := Template.regionEntropy_shell_le_of_safe_box Λ q D₀ Ω hΩ A T hC hsep hD
    (j - 1) L K (by omega) hL hlo hhi e C he hCbox hbox
  have hp := template_partial_row_entropy_le Λ q hq Ω hΩ T hC A j hj
    (hjL.trans hL) Y hY
  have hu := (abs_le.mp hp).2
  linarith

/-- A safe-box estimate explicitly quantified over every source exponent supplies
one nonnegative constant, uniform over all actual templates, for the core,
full shells and partial-row prefixes. The geometric factors remain explicit.
This is conditional on that safe-box input; it does not produce it from the
existence of a single initial exponent. -/
theorem exists_template_entropy_bounds_of_arbitrary_safe_box
    (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ) (hq : 1 ≤ q) (hD : 1 ≤ D₀)
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1) (A : Finset ↥Λ)
    (hbox : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : IntRect, IsSafe Λ A D₀ Q →
        ManyBody.regionEntropy Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + ε))
    (e : ℝ) (he : 0 < e) (he₁ : e < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
      24 ≤ Ctpl → T.IsSeparated D₀ (boundaryEndpoints Λ A) →
      (ManyBody.regionEntropy Ω (A.filter fun x ↦ x.1 ∈ T.points) ≤
        C * (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e) ∧
      (∀ j L : ℕ, 1 ≤ L → j ≤ L → L ≤ s₀ →
        ManyBody.regionEntropy Ω
          (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points) ≤
          C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e) ∧
      (∀ j L : ℕ, 1 ≤ j → j ≤ L → L ≤ s₀ →
        ∀ Y : Finset (ℤ × ℤ),
          Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1) →
          ManyBody.regionEntropy Ω
            (A.filter fun x ↦ x.1 ∈ (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
            C * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e + n * Real.log q) := by
  obtain ⟨C, hCbox, hb⟩ := hbox e he he₁
  refine ⟨C, hCbox, ?_⟩
  intro Ctpl n s₀ T hC hsep
  refine ⟨?_, ?_, ?_⟩
  · exact Template.regionEntropy_core_le_of_safe_box Λ q D₀ Ω hΩ A T hC hsep hD
      (Nat.log 2 s₀) (Nat.pow_log_le_self 2 (Nat.ne_of_gt T.s₀_pos))
      (Nat.lt_pow_succ_log_self (by decide) s₀) e C he hCbox hb
  · intro j L hLpos hj hL
    exact Template.regionEntropy_shell_le_of_safe_box Λ q D₀ Ω hΩ A T hC hsep hD
      j L (Nat.log 2 L) hj hL (Nat.pow_log_le_self 2 (by omega))
      (Nat.lt_pow_succ_log_self (by decide) L) e C he hCbox hb
  · intro j L hj hjL hL Y hY
    exact Template.regionEntropy_prefix_le_of_safe_box Λ q D₀ hq Ω hΩ A T hC hsep hD
      j L (Nat.log 2 L) hj hjL hL (Nat.pow_log_le_self 2 (by omega))
      (Nat.lt_pow_succ_log_self (by decide) L) Y hY e C he hCbox hb

end ManyBody

/-!
# Template entropy from a box estimate at real clearance

A pointwise rectangle entropy estimate at one fixed positive exponent bounds
an actual template core, its complete shells and its partial-row prefixes.
The clearance is real, and the constants are uniform over the templates.
The sufficient assumptions are a normalized pure state and the pointwise box
estimate; the Hamiltonian hypotheses enter only in obtaining that estimate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Lemma 9.4 (`scanner:templates`), `08-scanner.tex`,
lines 574–590 and 641–667; the standing real safety parameter is specified
in `02-initial.tex`, lines 223–228. Revision:
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

open ManyBody (ambientDilation)

open ManyBody (IntRect cast_supDist rectRegion supDist)

namespace ManyBody

/-- The core, shell and prefix entropy estimates of Lemma 9.4 for real
clearance and one fixed exponent. The pointwise box hypothesis is required
only at that exponent. Replacing its constant by `max C 0` requires no sign
assumption on the supplied constant. The estimate holds for every positive exponent and
clearance at least one, hence in particular for the source range `0 < e < 1`
and its standing clearance `D₀ > 2R+10`.
Source: `scanner:templates`, `08-scanner.tex`, lines 574–590 and 641–667. -/
theorem template_entropy_bounds_of_real_safe_box
    (Λ : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q)
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1) (A : Finset ↥Λ)
    (D₀ e C : ℝ) (hD : 1 ≤ D₀) (he : 0 < e)
    (hbox : ∀ Q : IntRect,
      (∀ x ∈ Q.toFinset, ∀ z ∈ boundaryEndpoints Λ A,
        D₀ * (Q.size : ℝ) < (supDist x z : ℝ)) →
      ManyBody.regionEntropy Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e)) :
    ∀ {Ctpl : ℝ} {n s₀ : ℕ} (T : Template Ctpl n s₀),
      24 ≤ Ctpl → T.IsSeparated D₀ (boundaryEndpoints Λ A) →
      (ManyBody.regionEntropy Ω (A.filter fun x ↦ x.1 ∈ T.points) ≤
        max C 0 * (18 + 4 / ((2 : ℝ) ^ e - 1)) * n * (s₀ : ℝ) ^ e) ∧
      (∀ j L : ℕ, 1 ≤ L → j ≤ L → L ≤ s₀ →
        ManyBody.regionEntropy Ω
          (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points) ≤
          max C 0 * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e) ∧
      (∀ j L : ℕ, 1 ≤ j → j ≤ L → L ≤ s₀ →
        ∀ Y : Finset (ℤ × ℤ),
          Y ⊆ ambientDilation T.points j \ ambientDilation T.points (j - 1) →
          ManyBody.regionEntropy Ω
            (A.filter fun x ↦ x.1 ∈ (ambientDilation T.points (j - 1) \ T.points) ∪ Y) ≤
            max C 0 * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e + n * Real.log q) := by
  classical
  intro Ctpl n s₀ T hC hsep
  have hcover (S : Finset (ℤ × ℤ)) (j K : ℕ) (hj : j ≤ s₀)
      (hcap : 2 ^ K ≤ s₀) (hS : S ⊆ ambientDilation T.points j) :
      ManyBody.regionEntropy Ω (A.filter fun x ↦ x.1 ∈ S) ≤
        max C 0 * (cappedDyadicPartition S K).sum
          (fun c ↦ ((2 : ℝ) ^ c.1) ^ (1 + e)) := by
    refine regionEntropy_filter_le_weighted_cover_of_forall Λ q Ω hΩ A S K e
      (max C 0) fun c hc ↦ ?_
    obtain ⟨hk, hsub, _⟩ := (mem_cappedDyadicPartition S K c.1 c.2).mp hc
    have hsize : (latticeDyadicRect c.1 c.2).size ≤ s₀ := by
      simpa only [size_latticeDyadicRect] using
        (Nat.pow_le_pow_right (by decide) hk).trans hcap
    have hclear : ∀ x ∈ (latticeDyadicRect c.1 c.2).toFinset,
        ∀ z ∈ boundaryEndpoints Λ A,
          D₀ * ((latticeDyadicRect c.1 c.2).size : ℝ) < (supDist x z : ℝ) := by
      intro x hx z hz
      simpa only [cast_supDist] using
        hsep.side_lt_dist_of_mem_ambientDilation hD hj hsize
          (hS (hsub (by simpa only [toFinset_latticeDyadicRect] using hx))) hz
    exact (hbox (latticeDyadicRect c.1 c.2) hclear).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 0)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hshell (j L : ℕ) (hLpos : 1 ≤ L) (hj : j ≤ L) (hL : L ≤ s₀) :
      ManyBody.regionEntropy Ω
        (A.filter fun x ↦ x.1 ∈ ambientDilation T.points j \ T.points) ≤
        max C 0 * (2 + 14 / ((2 : ℝ) ^ e - 1)) * n * (L : ℝ) ^ e := by
    refine (hcover (ambientDilation T.points j \ T.points) j (Nat.log 2 L)
      (hj.trans hL) ((Nat.pow_log_le_self 2 (by omega)).trans hL) Finset.sdiff_subset).trans ?_
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (T.sum_rpow_cappedDyadicPartition_shell_le hC j L (Nat.log 2 L) hj hL
        (Nat.pow_log_le_self 2 (by omega))
        (Nat.lt_pow_succ_log_self (by decide) L) e he) (le_max_right C 0)
  refine ⟨?_, hshell, ?_⟩
  · refine (hcover T.points 0 (Nat.log 2 s₀) (Nat.zero_le _)
      (Nat.pow_log_le_self 2 (Nat.ne_of_gt T.s₀_pos)) (by simp)).trans ?_
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (T.sum_rpow_cappedDyadicPartition_core_le hC (Nat.log 2 s₀)
        (Nat.pow_log_le_self 2 (Nat.ne_of_gt T.s₀_pos))
        (Nat.lt_pow_succ_log_self (by decide) s₀) e he) (le_max_right C 0)
  · intro j L hj hjL hL Y hY
    have hs := hshell (j - 1) L (hj.trans hjL) (by omega) hL
    have hp := template_partial_row_entropy_le Λ q hq Ω hΩ T hC A j hj
      (hjL.trans hL) Y hY
    linarith only [hs, (abs_le.mp hp).2]

end ManyBody
