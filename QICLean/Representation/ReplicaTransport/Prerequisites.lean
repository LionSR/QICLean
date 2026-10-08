/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Setup

/-!
# Replica-metric inputs of the transport estimate

The transport estimate consumes two results of the replica section of the area-law paper:

* Lemma 6.4 (`lem:relative-pin`, `05-replicas.tex` lines 480--500), the relative coherent
  pin for one move;
* the skew bound of Lemma 6.5 (`lem:symbol`, display `replicas:skew-bound`,
  `05-replicas.tex` lines 615--660), in the form used at a split leaf.

Both lemmas belong to the replica section of the source and are not formalized yet. They
are recorded here as propositions on the band metric of `ReplicaTransport.Setup`, and the
transport estimate is proved assuming them; once the replica-metric lemmas are formalized,
both propositions are discharged by applying them.

`SplitSkewBound` is the case of Lemma 6.5 used at a split leaf: the
designated support meets `Y` and exactly one outer part. The source lemma requires only
that `h` be supported on `P ∪ Y`; the split case is the specialization consumed by
Proposition 7.4 (`06-transport.tex` lines 735--748).
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Filter Topology PermutationRepresentation Entropy

noncomputable section

universe u

namespace TensorPower.ReplicaTransport

/-- **Lemma 6.4, relative coherent pin** (`05-replicas.tex`, display
`replicas:relative-pin`, lines 480--500): for a valid move of `x ⊆ Y` with
`0 < t < 1/4`, `a = 2t` and `a log(e dim x) ≤ c`, there are `b_k > 0` with
`-log b_k = O(log(k+1))`, uniform in `θ`, such that
`A^{-1/2} B A^{-1/2} ≥ b_k exp(k a [η_θ - C a^{1/4} log^C(e dim x)]) P_{θ,k}`.
A choice making no move has relative metric `I` and gain zero. -/
def RelativePinBound : Prop :=
    ∃ c Cpin epin : ℝ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        (π : PYF V), π.IsPartition → ∀ (m : Move V), m.IsValid π →
        ∀ {t : ℝ}, 0 < t → t < 1 / 4 → 2 * t * logDim n m.subsystem ≤ c →
        ∃ b : ℕ → ℝ, (∀ k, 0 < b k) ∧
          ((fun k : ℕ => -Real.log (b k)) =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧
          ∀ (k : ℕ) (θ : SiteConfig n → ℂ), star θ ⬝ᵥ θ = 1 →
            (b k * Real.exp ((k : ℝ) * (2 * t) *
                (moveEta n π m ((EuclideanSpace.equiv _ ℂ).symm θ) -
                  Cpin * (2 * t) ^ (1 / 4 : ℝ) * logDim n m.subsystem ^ epin))) •
                coherentProj k θ ≤
              bandMetric n t k π ^ (-(1 / 2) : ℝ) * bandMetric n t k (m.apply π) *
                bandMetric n t k π ^ (-(1 / 2) : ℝ)

/-- **Lemma 6.5, skew bound at a split** (`05-replicas.tex`, display
`replicas:skew-bound`, lines 645--660): for `0 ≤ h ≤ 1` with designated support `D`
meeting `Y` and exactly one outer part, `0 < t < 1/4`, `a = 2t` and `a log(e dim D) ≤ c`,
uniformly over density matrices `ρ` on `𝒮_k`,
`Tr(ρ 𝒟_k) ≤ C a² log^C(e dim D) ∫ η^{1/8} dμ_ρ + o_k(1)`. -/
def SplitSkewBound : Prop :=
    ∃ c Csym esym : ℝ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        (π : PYF V), π.IsPartition → ∀ (D : Finset V) (h : Matrix (SiteConfig n) (SiteConfig n) ℂ),
        0 ≤ h → h ≤ 1 → IsSupportedOn h D → (π.SplitsToP D ∨ π.SplitsToF D) →
        ∀ {t : ℝ}, 0 < t → t < 1 / 4 → 2 * t * logDim n D ≤ c →
        ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧
          ∀ (k : ℕ) (ρ : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ),
            ρ.PosSemidef → ρ.trace = 1 → symProj (copyPerm (SiteConfig n) k) * ρ = ρ →
            (ρ * Matrix.Transport.skewSquare (bandMetric n t k π) (copyMean n k h)).trace.re ≤
              Csym * (2 * t) ^ 2 * logDim n D ^ esym *
                  coherentIntegral k (TransportData.base n) ρ (fun θ =>
                    splitBandEta n π D ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ)) +
                r k

end TensorPower.ReplicaTransport
