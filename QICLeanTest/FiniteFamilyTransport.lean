/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.FiniteFamily

/-! Dependent round families, signed errors, empty families and the zero-copy index. -/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy TensorPower
open TensorPower.ReplicaTransport

noncomputable section

universe u

namespace FiniteFamilyTransportTest

-- A signed error can be nonzero at zero despite an eventual bound by log(k+1).
example : ∃ C : ℝ, 0 ≤ C ∧ 7 ≤ C * Real.log 2 := by
  have hf : (fun k : ℕ => if k = 0 then (-7 : ℝ) else 0) =O[atTop]
      fun k : ℕ => Real.log (k + 1) := by
    refine Asymptotics.IsBigO.of_bound 0 (eventually_atTop.2 ⟨1, ?_⟩)
    intro k hk
    have hk0 : k ≠ 0 := by omega
    simp [hk0]
  obtain ⟨C, hC, hbound⟩ := hf.exists_nonneg_abs_le_mul_log_add_two
  refine ⟨C, hC, ?_⟩
  simpa using hbound 0

-- Both history and choice types vary across the two rounds. One pair of errors
-- precedes every round, count, supplied vector, parameter and eigenvalue.
example :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ}
        (D : (j : Fin 2) → TransportData V K (Fin (j.val + 1))
          (fun h => Fin (h.val + 1)))
        {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
        (∀ j, (D j).IsAdmissible) → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
        (∀ i, IsSupportedOn (E.term i) (E.support i)) →
        (∀ j, (D j).SupportCompatible E) →
        ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ →
        (∀ j k, (D j).CrossBandCommute n (a / 2) k) →
        (∀ j h c g, logDim n ((D j).move h c g).subsystem ≤ ℓ) →
        (∀ j i, ((D j).splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
        ∃ (β r : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧
          (∀ k, 0 ≤ β k) ∧ (∀ k, 0 ≤ r k) ∧
          (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧ Tendsto r atTop (𝓝 0) ∧
          ∀ (j : Fin 2) (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 →
            (∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun q => -Real.log
                  (Transport.filteredNormSq ((D j).rootPath n (a / 2) k q) pre))
                ((D j).exactDerivative n (a / 2) k pre p) p ∧
              (k : ℝ) * a * (D j).entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k ≤
                (D j).exactDerivative n (a / 2) k pre p ∧
              ∀ E₀ : ℝ, E.replicaEnergy k *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector ((D j).rootPath n (a / 2) k p) pre
                (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een *
                    (D j).energyError E (a / 2) k pre p + r k) ∧
            ∀ p₀ p₁ : ℝ, 0 ≤ p₀ → p₀ ≤ p₁ → p₁ ≤ 1 →
              ∫ p in p₀..p₁, ((k : ℝ) * a * (D j).entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k) ≤
                Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k p₀) pre) -
                  Real.log (Transport.filteredNormSq ((D j).rootPath n (a / 2) k p₁) pre) := by
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, h⟩ := transport_finite_family
  refine ⟨c₀, Cent, eent, Cen, een, hc₀, ?_⟩
  intro V _ _ n _ K D ι _ E hD hE0 hE1 hEs hcompat a ℓ ha hℓ haℓ hcomm hℓm hℓs
  exact h n D E hD hE0 hE1 hEs hcompat ha hℓ haℓ hcomm hℓm hℓs

-- There is no inhabited-round premise. The hypotheses indexed by rounds or
-- energy terms can all be vacuous while the common sequences are still supplied.
example : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ →
      ∃ (β r : ℕ → ℝ) (Cβ : ℝ), 0 ≤ Cβ ∧
        (∀ k, 0 ≤ β k) ∧ (∀ k, 0 ≤ r k) ∧
        (∀ k, β k ≤ Cβ * Real.log (k + 2)) ∧ Tendsto r atTop (𝓝 0) := by
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, h⟩ := transport_finite_family
  refine ⟨c₀, hc₀, ?_⟩
  intro a ℓ ha hℓ haℓ
  let n : Unit → ℕ := fun _ => 1
  let E : EnergyTerms Unit n Empty :=
    { term := Empty.elim, support := Empty.elim }
  let D : (j : Empty) → TransportData Unit 0 Empty (fun _ => Empty) := fun j => nomatch j
  obtain ⟨β, r, Cβ, hCβ, hβ0, hr0, hβ, hr, _⟩ := h n D E
    (fun j => nomatch j) (fun i => nomatch i) (fun i => nomatch i)
    (fun i => nomatch i) (fun j => nomatch j) ha hℓ haℓ
    (fun j => nomatch j) (fun j => nomatch j) (fun j => nomatch j)
  exact ⟨β, r, Cβ, hCβ, hβ0, hr0, hβ, hr⟩

end FiniteFamilyTransportTest
