/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.SplitSkewBound
import QICLean.Representation.ReplicaTransport.IntegratedEntropy
import QICLean.Representation.ReplicaTransport.Integrated

/-!
# Entropy and energy transport

Area-law paper (*A two-dimensional area law from a global spectral gap*, September 24,
2026), Proposition 7.4 (`prop:transport`), `06-transport.tex` lines 377--434, with the
hypotheses of the source only: the relative coherent pin and the skew bound of the replica
section enter through `relativePinBound` and `splitSkewBound`, cross-band commutation is
commutation on `𝒮_k`, and the integrated entropy estimate uses the integrability of the
entropy gain in the interpolation parameter (`intervalIntegrable_entropyGain`).

The universal constants are named: `transportThreshold`, `transportEntropyConst`,
`transportEntropyExponent`, `transportEnergyConst` and `transportEnergyExponent`, with values
`1/8`, `200000`, `2`, `3 skewConst` and `4`, and `transport_explicit` states the proposition
at them.

The proof is written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

universe u

namespace TensorPower.ReplicaTransport

/-- The universal threshold `c₀` of Proposition 7.4 (`06-transport.tex` lines 377--434):
the transport estimate `transport_explicit` holds for `a ℓ ≤ c₀`. It is the smaller of the
thresholds of the entropy and energy estimates, each capped at `1/4`; its value is `1/8`
(`transportThreshold_eq`). -/
noncomputable def transportThreshold : ℝ :=
  min (min conditionalMovementThreshold (1 / 4)) (min (1 / 8) (1 / 4))

/-- The universal constant of the entropy error `C k a K a^{1/4} ℓ^e` of Proposition 7.4
(`06-transport.tex` lines 409--416): half the absolute value of the constant of Lemma 6.3.
Its value is `200000` (`transportEntropyConst_eq`). -/
noncomputable def transportEntropyConst : ℝ := |relativePinConst| / 2

/-- The universal exponent of `ℓ` in the entropy error of Proposition 7.4
(`06-transport.tex` lines 409--416): the exponent `2` of Lemma 6.3, made nonnegative. -/
noncomputable def transportEntropyExponent : ℝ := max 2 0

/-- The universal constant of the energy error `C a² ℓ^e` of Proposition 7.4
(`06-transport.tex` lines 417--426): `3/2` times the nonnegative part of the constant of
Lemma 6.4 at a split leaf. Its value is `3 skewConst` (`transportEnergyConst_eq`). -/
noncomputable def transportEnergyConst : ℝ := 3 / 2 * max splitSkewConst 0

/-- The universal exponent of `ℓ` in the energy error of Proposition 7.4
(`06-transport.tex` lines 417--426): the exponent `4` of Lemma 6.4, made nonnegative. -/
noncomputable def transportEnergyExponent : ℝ := max 4 0

/-- The transport threshold is `1/8`. -/
theorem transportThreshold_eq : transportThreshold = 1 / 8 := by
  norm_num [transportThreshold, conditionalMovementThreshold]

/-- The transport threshold is positive. -/
theorem transportThreshold_pos : 0 < transportThreshold := by
  rw [transportThreshold_eq]; norm_num

/-- The entropy constant of the transport estimate is `200000`. -/
theorem transportEntropyConst_eq : transportEntropyConst = 200000 := by
  norm_num [transportEntropyConst, relativePinConst, conditionalMovementConst]

/-- The entropy exponent of the transport estimate is `2`. -/
theorem transportEntropyExponent_eq : transportEntropyExponent = 2 := by
  norm_num [transportEntropyExponent]

/-- The energy constant of the transport estimate is `3 skewConst`. -/
theorem transportEnergyConst_eq :
    transportEnergyConst = 3 * Entropy.ConditionalSkew.skewConst := by
  rw [transportEnergyConst, splitSkewConst, max_eq_left (by linarith [skewConst_nonneg])]
  ring

/-- The energy exponent of the transport estimate is `4`. -/
theorem transportEnergyExponent_eq : transportEnergyExponent = 4 := by
  norm_num [transportEnergyExponent]

/-- **Proposition 7.4 at the named universal constants** (area-law paper, `prop:transport`,
`06-transport.tex` lines 377--434): the conclusion of `transport` with threshold
`transportThreshold`, entropy constant and exponent `transportEntropyConst`,
`transportEntropyExponent`, and energy constant and exponent `transportEnergyConst`,
`transportEnergyExponent`. -/
theorem transport_explicit :
    ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
      {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
      [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
      {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
      D.IsAdmissible → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
      (∀ i, IsSupportedOn (E.term i) (E.support i)) → D.SupportCompatible E →
      ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ transportThreshold →
      (∀ k, D.CrossBandCommute n (a / 2) k) →
      (∀ h c g, logDim n (D.move h c g).subsystem ≤ ℓ) →
      (∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
      ∃ β r : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧
        Tendsto r atTop (𝓝 0) ∧
        ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
          pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
          (∀ p ∈ Ioo (0 : ℝ) 1,
            HasDerivAt
              (fun q => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k q) pre))
              (D.exactDerivative n (a / 2) k pre p) p ∧
            (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                transportEntropyConst * k * a * K * a ^ (1 / 4 : ℝ) *
                  ℓ ^ transportEntropyExponent - β k ≤
              D.exactDerivative n (a / 2) k pre p ∧
            ∀ E₀ : ℝ, E.replicaEnergy k *ᵥ pre = (E₀ : ℂ) • pre →
              let v := Transport.filteredVector (D.rootPath n (a / 2) k p) pre
              (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re ≤
                2 * E₀ + transportEnergyConst * a ^ 2 * ℓ ^ transportEnergyExponent *
                  D.energyError E (a / 2) k pre p + r k) ∧
          ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
            ∫ p in p₀..p₁, ((k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                transportEntropyConst * k * a * K * a ^ (1 / 4 : ℝ) *
                  ℓ ^ transportEntropyExponent - β k) ≤
              Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k p₀) pre) -
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k p₁) pre) := by
  intro V _ _ n _ K H' _ _ C _ _ D ι _ E hD hE0 hE1 hEs hcompat a ℓ ha hℓ haℓ hcomm hℓm hℓs
  obtain ⟨β, r, hβ, hr, hpt⟩ := transport_of_splitSkewBoundAt splitSkewBoundAt n D E hD hE0 hE1 hEs
    hcompat ha hℓ haℓ hcomm hℓm hℓs
  refine ⟨β, r, hβ, hr, fun k pre hpre hne => ⟨hpt k pre hpre hne, ?_⟩⟩
  intro p₀ p₁ h0 h01 h1
  have ht : (0 : ℝ) ≤ a / 2 := by positivity
  have hL : IntervalIntegrable (fun p => (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
      transportEntropyConst * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ transportEntropyExponent -
        β k) volume 0 1 :=
    (((D.intervalIntegrable_entropyGain hD ht (hcomm k) hne).const_mul _).sub
      intervalIntegrable_const).sub intervalIntegrable_const
  exact D.integral_le_log_filteredNormSq_sub hD ht (hcomm k) hne hL
    (fun p hp => (hpt k pre hpre hne p hp).2.1) h0 h01 h1

/-- **Proposition 7.4, entropy and energy transport** (area-law paper, `prop:transport`,
`06-transport.tex` lines 377--434). Fix a finite one-copy space, history and conditional
choice trees, partitions with cross-band commutation on `𝒮_k`, a positive parameter
`a = 2t`, and positive contractions with designated supports compatible with the terminal
partitions. Let `ℓ ≥ 1` bound `log(e dim x)` for every transferred subsystem and
`log(e dim D_i)` for every term split at some terminal leaf, with `a ℓ` below a universal
threshold. Then for every `k` and every nonzero `pre ∈ 𝒮_k`:

* for `0 < p < 1`, `-∂_p log N(p)² = ∑_h w_h ∫ m_{1/4}(u) Tr(σ_{h,u} log C_h) du`;
* for `0 < p < 1`, the entropy-gain lower bound with error `C k a K a^{1/4} ℓ^C + β_k`,
  `β_k = O(log(k+1))` independent of `p` and `pre`;
* for `0 < p < 1`, if `Hbar pre = E₀ pre`, the energy bound
  `⟨v, Hbar v⟩ ≤ 2E₀ + C a² ℓ^C ∑_i W_i(p) ∑_{j∈𝒥_i} π_j ∫ m_{1/4} ∫ η_{i,j}^{1/8} dμ_{σ_{j,u}}
  du + o_k(1)`, with the remainder uniform in `p`, `pre` and the replica state;
* the entropy estimate integrates over every closed subinterval `[p₀, p₁] ⊆ [0, 1]`, with
  the endpoint values of `N` (lines 427--429).

The constants and exponents are universal (separate ones for the two estimates); only `β_k`
and the rate of `o_k(1)` depend on the fixed data. -/
theorem transport :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
        {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
        D.IsAdmissible → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
        (∀ i, IsSupportedOn (E.term i) (E.support i)) → D.SupportCompatible E →
        ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ h c g, logDim n (D.move h c g).subsystem ≤ ℓ) →
        (∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
        ∃ β r : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧
          Tendsto r atTop (𝓝 0) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
            (∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun q => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k q) pre))
                (D.exactDerivative n (a / 2) k pre p) p ∧
              (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k ≤
                D.exactDerivative n (a / 2) k pre p ∧
              ∀ E₀ : ℝ, E.replicaEnergy k *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector (D.rootPath n (a / 2) k p) pre
                (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) k pre p + r k) ∧
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              ∫ p in p₀..p₁, ((k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k) ≤
                Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k p₀) pre) -
                  Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k p₁) pre) :=
  ⟨_, _, _, _, _, transportThreshold_pos, transport_explicit⟩

end TensorPower.ReplicaTransport
