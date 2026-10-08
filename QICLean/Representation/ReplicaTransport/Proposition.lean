/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.EntropyGain
import QICLean.Representation.ReplicaTransport.Energy

/-!
# Entropy and energy transport

Area-law paper (*A two-dimensional area law from a global spectral gap*, September 24,
2026), Proposition 7.4 (`prop:transport`), `06-transport.tex` lines 377--434.

Fix a finite one-copy space, history and conditional choice trees, partitions, cross-band
commutation, a positive parameter `a = 2t`, and positive contractions with designated
supports. Let `ℓ ≥ 1` bound `log(e dim x)` for every transferred subsystem and
`log(e dim D_i)` for every term split at some terminal leaf, with `a ℓ` below a universal
threshold. For every `k`, every nonzero `pre ∈ 𝒮_k` and every `0 < p < 1`:

* the exact derivative `-∂_p log N(p)² = ∑_h w_h ∫ m_{1/4}(u) Tr(σ_{h,u} log C_h) du`;
* the entropy-gain lower bound with error `C k a K a^{1/4} ℓ^C + β_k`,
  `β_k = O(log(k+1))` independent of `p` and `pre`;
* if `H̄ pre = E₀ pre`, the energy bound
  `⟨v, H̄ v⟩ ≤ 2E₀ + C a² ℓ^C ∑_i W_i(p) ∑_{j∈𝒥_i} π_j ∫ m_{1/4} ∫ η_{i,j}^{1/8} dμ_{σ_{j,u}} du
  + o_k(1)`, with the remainder uniform in `p`, `pre` and the replica state.

The constants and exponents are universal (separate ones for the two estimates, as the
source's `C` denotes possibly different universal constants); only `β_k` and the rate of
`o_k(1)` depend on the fixed data. The entropy estimate is evaluated against the same
states `σ_{h,u}` as the energy estimate. The one-dimensional coherent integral uses the
image of Haar measure on the unitary group under `U ↦ U e`, which is the invariant
probability measure on the unit sphere of the source.

The proof is written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology PermutationRepresentation Entropy

noncomputable section

universe u

namespace TensorPower.ReplicaTransport

/-- **Proposition 7.4, entropy and energy transport** (area-law paper, `prop:transport`,
`06-transport.tex` lines 377--434), assuming the relative coherent pin of Lemma 6.4 and the
split-leaf skew bound of Lemma 6.5 in the forms `RelativePinBound` and `SplitSkewBound`.
The source proves those lemmas in its replica section; here they are hypotheses until the
replica-metric formalization supplies them. -/
theorem transport_of_relativePin_of_splitSkewBound (hpin : RelativePinBound.{u})
    (hskew : SplitSkewBound.{u}) :
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
        ∃ β r : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧ Tendsto r atTop (𝓝 0) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun q => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k q) pre))
                (D.exactDerivative n (a / 2) k pre p) p ∧
              (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k ≤
                D.exactDerivative n (a / 2) k pre p ∧
              ∀ E₀ : ℝ, E.replicaEnergy k *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector (D.rootPath n (a / 2) k p) pre
                (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) k pre p + r k := by
  obtain ⟨c₁, Cent, eent, hc₁, hG2⟩ :=
    TransportData.exists_entropyGain_le_exactDerivative_of_relativePin hpin
  obtain ⟨c₂, Cen, een, hc₂, hG4⟩ := TransportData.exists_energy_le_of_splitSkewBound hskew
  refine ⟨min c₁ c₂, Cent, eent, Cen, een, lt_min hc₁ hc₂, ?_⟩
  intro V _ _ n _ K H _ _ C _ _ D ι _ E hD hE0 hE1 hEs hcompat a ℓ ha hℓ haℓ hcomm hℓm hℓs
  obtain ⟨β, hβ, hent⟩ := hG2 n D hD ha hℓ (haℓ.trans (min_le_left _ _)) hcomm hℓm
  obtain ⟨r, hr, hen⟩ := hG4 n D E hD hE0 hE1 hEs hcompat ha hℓ (haℓ.trans (min_le_right _ _))
    hcomm hℓs
  refine ⟨β, r, hβ, hr, fun k pre hpre hne p hp => ⟨?_, hent k pre hpre hne p hp,
    fun E₀ hE => hen k pre hpre hne p hp E₀ hE⟩⟩
  exact D.hasDerivAt_exactDerivative hD (by positivity) (hcomm k) hne hp

end TensorPower.ReplicaTransport
