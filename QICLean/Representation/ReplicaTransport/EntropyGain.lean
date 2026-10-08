/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.CoherentLog
import QICLean.Representation.ReplicaTransport.Prerequisites
import QICLean.Representation.ReplicaTransport.States

/-!
# The entropy-gain lower bound of the transport estimate

Area-law paper, Proposition 7.4, display `transport:entropy-gain` (`06-transport.tex`
lines 409--416, proof lines 495--583):
$$-\partial_p\log N(p)^2\ge ka\sum_{h,g}w_h\int m_{1/4}(u)\int\sum_c q_{c|h}
  \eta_{h,c,g}\,d\mu_{\sigma_{h,u}}\,du-CkaKa^{1/4}\ell^C-\beta_k,$$
with `β_k = O(log(k+1))` independent of `p` and `pre`.

Proof outline:

* `cfc_log_relRatio_eq_sum` — band factorization `log C_h = ∑_g log C_{h,g}`
  (display `transport:relative-factorization`, Lemma 7.1);
* `bandRelRatio_eq_eval` — congruence covariance identifies `C_{h,g}` with the
  conditional choice tree of the single-move relative metrics;
* `smul_coherentProj_le_bandRelRatio` — Lemma 6.4 and projection transfer give the
  conditional pin (display `transport:conditional-pin`);
* `coherentIntegral_sub_log_le_re_trace_mul_log` — the logarithmic passage
  (display `transport:log-relative`);
* `exists_entropyGain_le_exactDerivative` — summation over bands and histories, with
  `∑_h w_h = 1` and `∫ m_{1/4} = 1/2`.

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

/-- The entropy of a move is continuous in the one-copy vector. -/
theorem continuous_moveEta (π : PYF V) (m : Move V) :
    Continuous fun θ : SiteConfig n → ℂ => moveEta n π m ((EuclideanSpace.equiv _ ℂ).symm θ) := by
  sorry

namespace TransportData

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)

variable (n) in
/-- The band relative ratio `C_{h,g} = A_{h,g}^{-1/2} B_{h,g} A_{h,g}^{-1/2}`, where `B_{h,g}`
is the conditional choice tree of the new band-`g` metrics (`06-transport.tex`, display
`transport:relative-factorization`). -/
def bandRelRatio (t : ℝ) (k : ℕ) (h : H) (g : Fin K) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ) *
    (D.choiceTree h).eval (fun c => bandMetric n t k (D.new h c g)) *
      bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ)

/-- **Band factorization** `log C_h = ∑_g log C_{h,g}` (`06-transport.tex`, display
`transport:relative-factorization`, lines 501--509). -/
theorem cfc_log_relRatio_eq_sum (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) (h : H) :
    CFC.log (D.relRatio n t k h) = ∑ g, CFC.log (D.bandRelRatio n t k h g) := by
  sorry

theorem posDef_bandRelRatio (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (g : Fin K) : (D.bandRelRatio n t k h g).PosDef := by
  sorry

theorem commute_permOp_bandRelRatio {t : ℝ} (k : ℕ) (h : H) (g : Fin K)
    (s : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (SiteConfig n) k) s) (D.bandRelRatio n t k h g) := by
  sorry

/-- **Congruence covariance** (`06-transport.tex` lines 510--512): `C_{h,g}` is the
conditional choice tree of the single-move relative metrics
`A_{h,g}^{-1/2} A_{h,c,g} A_{h,g}^{-1/2}`. -/
theorem bandRelRatio_eq_eval (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (h : H)
    (g : Fin K) :
    D.bandRelRatio n t k h g = (D.choiceTree h).eval (fun c =>
      bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ) * bandMetric n t k (D.new h c g) *
        bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ)) := by
  sorry

/-- **Conditional pin** (`06-transport.tex`, display `transport:conditional-pin`,
lines 513--531): from per-move pins with common `b > 0` and error `E`, projection transfer
gives `C_{h,g} ≥ b exp(k a [∑_c q_{c|h} η_{h,c,g}(θ) - E]) P_{θ,k}`. -/
theorem smul_coherentProj_le_bandRelRatio (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t)
    (k : ℕ) (h : H) (g : Fin K) {b Err : ℝ} (hb : 0 < b) (θ : SiteConfig n → ℂ)
    (hpin : ∀ c, (b * Real.exp ((k : ℝ) * (2 * t) *
        (moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) - Err))) •
          coherentProj k θ ≤
        bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ) * bandMetric n t k (D.new h c g) *
          bandMetric n t k (D.old h g) ^ (-(1 / 2) : ℝ)) :
    (b * Real.exp ((k : ℝ) * (2 * t) * (∑ c, (D.choiceTree h).weight c *
        moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ) - Err))) •
          coherentProj k θ ≤ D.bandRelRatio n t k h g := by
  sorry

/-- **Entropy-gain lower bound** (area-law paper, Proposition 7.4, display
`transport:entropy-gain`, `06-transport.tex` lines 409--416 and 495--583). The constants
`c₀`, `C`, `e` are universal; `β_k = O(log(k+1))` depends only on the fixed data. -/
theorem exists_entropyGain_le_exactDerivative :
    ∃ c₀ Cent eent : ℝ, 0 < c₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C),
        D.IsAdmissible → ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ →
        (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ h c g, logDim n (D.move h c g).subsystem ≤ ℓ) →
        ∃ β : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
              (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k ≤
                D.exactDerivative n (a / 2) k pre p := by
  sorry

end TransportData

end TensorPower.ReplicaTransport
