/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.EnergyBlock
import QICLean.Representation.ReplicaTransport.Prerequisites
import QICLean.Representation.ReplicaTransport.States

/-!
# The energy estimate of the transport proposition

Area-law paper, Proposition 7.4, display `transport:energy` (`06-transport.tex`
lines 417--426, proof lines 588--766): if `H̄ pre = E₀ pre`, then
$$\langle v,\bar Hv\rangle\le 2E_0+Ca^2\ell^C\sum_iW_i(p)\sum_{j\in\mathcal J_i}\pi_j
  \int m_{1/4}(u)\int\eta_{i,j}^{1/8}\,d\mu_{\sigma_{j,u}}\,du+o_k(1).$$

Proof outline:

* `commute_input_copyMean_of_not_mem_splitLeaves` — an unsplit leaf metric commutes with
  `h̄_i` (lines 359--364);
* `skewSquare_input_eq_bandMetric` — at a split leaf only the exceptional band fails to
  commute, and the other factors cancel in `O_{i,j}` (lines 732--735);
* `splitEta_eq_splitBandEta` — `η_{i,j}` is the split entropy of the exceptional band;
* `trace_state_skewSquare_le` — Lemma 6.5 at every split term--leaf pair, with one common
  remainder (display `transport:symbol-cost`, lines 736--748);
* `Matrix.Transport.re_star_dotProduct_mulVec_le_energy` (generic block argument) per
  term, then summation over `i` using `M^s v = pre / N` and `H̄ pre = E₀ pre`
  (lines 750--766).

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

/-- A band metric commutes with the copy mean of an operator supported in one of its
parts (`05-replicas.tex` lines 470--473; `06-transport.tex` lines 359--364). -/
theorem commute_bandMetric_copyMean_of_contains {π : PYF V} (hπ : π.IsPartition) {t : ℝ}
    (k : ℕ) {D : Finset V} {h : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hh : IsSupportedOn h D) (hD : π.Contains D) :
    Commute (bandMetric n t k π) (copyMean n k h) := by
  sorry

namespace TransportData

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
  {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι)

/-- **Unsplit leaves commute with the term** (`06-transport.tex` lines 359--364). -/
theorem commute_input_copyMean_of_not_mem_splitLeaves (hD : D.IsAdmissible) {t : ℝ}
    (k : ℕ) (hEsupp : ∀ i, IsSupportedOn (E.term i) (E.support i)) {i : ι}
    {j : Σ h, Option (C h)} (hj : j ∉ D.splitLeaves E i) :
    Commute (D.input n t k j) (copyMean n k (E.term i)) := by
  sorry

/-- **Single-band reduction at a split leaf** (`06-transport.tex` lines 732--735): if `g`
is the exceptional band of `D_i` at `j`, the other band factors cancel in
`O_{i,j} = A_j^{-1/2} h̄_i A_j^{1/2}`, so the skew square is that of the band metric. -/
theorem skewSquare_input_eq_bandMetric (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) (hEsupp : ∀ i, IsSupportedOn (E.term i) (E.support i))
    (hcompat : D.SupportCompatible E) {i : ι} {j : Σ h, Option (C h)} {g : Fin K}
    (hg : ¬ (D.leafPart j g).Contains (E.support i)) :
    Transport.skewSquare (D.input n t k j) (copyMean n k (E.term i)) =
      Transport.skewSquare (bandMetric n t k (D.leafPart j g)) (copyMean n k (E.term i)) := by
  sorry

/-- `η_{i,j}` is the split entropy of the unique exceptional band. -/
theorem splitEta_eq_splitBandEta (hcompat : D.SupportCompatible E) {i : ι}
    {j : Σ h, Option (C h)} {g : Fin K} (hg : ¬ (D.leafPart j g).Contains (E.support i))
    (θ : EuclideanSpace ℂ (SiteConfig n)) :
    D.splitEta E i j θ = splitBandEta n (D.leafPart j g) (E.support i) θ := by
  sorry

/-- **Symbol cost at the split leaves** (`06-transport.tex`, display
`transport:symbol-cost`, lines 736--748): one remainder `r_k → 0` serves all split
term--leaf pairs, uniformly over density matrices on `𝒮_k`. -/
theorem exists_trace_skewSquare_le :
    ∃ c₀ Csym esym : ℝ, 0 < c₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
        {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
        D.IsAdmissible → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
        (∀ i, IsSupportedOn (E.term i) (E.support i)) → D.SupportCompatible E →
        ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
        ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ k, 0 ≤ r k) ∧
          ∀ (k : ℕ) (i : ι), ∀ j ∈ D.splitLeaves E i,
            ∀ ρ : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ,
            ρ.PosSemidef → ρ.trace = 1 → symProj (copyPerm (SiteConfig n) k) * ρ = ρ →
            (ρ * Transport.skewSquare (D.input n (a / 2) k j)
                (copyMean n k (E.term i))).trace.re ≤
              Csym * a ^ 2 * ℓ ^ esym * coherentIntegral k (base n) ρ (fun θ =>
                D.splitEta E i j ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ)) + r k := by
  sorry

/-- **Energy estimate** (area-law paper, Proposition 7.4, display `transport:energy`,
`06-transport.tex` lines 417--426 and 588--766). The split weight `W_i(p)` enters twice;
the remainder is uniform in `p`, in `pre` and in the replica state; support dimensions
enter the coefficient only through `ℓ`. -/
theorem exists_energy_le :
    ∃ c₀ Cen een : ℝ, 0 < c₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
        {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
        D.IsAdmissible → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
        (∀ i, IsSupportedOn (E.term i) (E.support i)) → D.SupportCompatible E →
        ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
        ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
            ∀ E₀ : ℝ, E.replicaEnergy k *ᵥ pre = (E₀ : ℂ) • pre →
              let v := Transport.filteredVector (D.rootPath n (a / 2) k p) pre
              (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re ≤
                2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) k pre p + r k := by
  sorry

end TransportData

end TensorPower.ReplicaTransport
