/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LogarithmicEnvelope
import QICLean.Representation.ReplicaTransport.Transport

/-!
# Simultaneous transport for a finite family

A finite-family consequence of Proposition 7.4 of the area-law paper (*A two-dimensional
area law from a global spectral gap*, September 24, 2026; `06-transport.tex` lines 377--434).
The universal transport constants are chosen once. For fixed admissible data in a finite
family, absolute sums of the individual errors give nonnegative errors shared by all rounds,
replica counts, supplied vectors and interpolation parameters. The entropy error has an
all-count bound by a multiple of `log(k+2)`, including `k = 0`.

This result retains the dimension bound `ℓ` and the actual replica-energy eigenvector premise.
It does not construct a physical prevector or identify its eigenvalue with a physical energy.
The proof is written from the finite-family argument; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set Filter Topology MeasureTheory PermutationRepresentation Entropy

noncomputable section

universe u

namespace TensorPower.ReplicaTransport

/-- Simultaneous finite-family form of the area-law paper's Proposition 7.4
(`06-transport.tex` lines 377--434). The same universal constants work for every finite
family, whose history and choice types may vary with the round. The common nonnegative
errors and their logarithmic coefficient are chosen before the round, replica count,
nonzero symmetric vector, interpolation parameter and energy eigenvalue. Empty families
are allowed. The integrated entropy estimate includes both endpoints. -/
theorem transport_finite_family :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {J : Type*} [Fintype J] {H : J → Type*}
        [∀ j, Fintype (H j)] [∀ j, DecidableEq (H j)] {C : (j : J) → H j → Type*}
        [∀ j h, Fintype (C j h)] [∀ j h, DecidableEq (C j h)]
        (D : ∀ j, TransportData V K (H j) (C j))
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
          ∀ (j : J) (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
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
  classical
  obtain ⟨c₀, Cent, eent, Cen, een, hc₀, htransport⟩ := transport
  refine ⟨c₀, Cent, eent, Cen, een, hc₀, ?_⟩
  intro V _ _ n _ K J _ H _ _ C _ _ D ι _ E hD hE0 hE1 hEs hcompat a ℓ ha hℓ haℓ
    hcomm hℓm hℓs
  have hround := fun j => htransport n (D j) E (hD j) hE0 hE1 hEs (hcompat j)
    ha hℓ haℓ (hcomm j) (hℓm j) (hℓs j)
  choose β r hβ hr hpt using hround
  let B : ℕ → ℝ := fun k => ∑ j, |β j k|
  let R : ℕ → ℝ := fun k => ∑ j, |r j k|
  have hB0 : ∀ k, 0 ≤ B k := fun k => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hR0 : ∀ k, 0 ≤ R k := fun k => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hβB : ∀ j k, β j k ≤ B k := fun j k =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |β j k|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j))
  have hrR : ∀ j k, r j k ≤ R k := fun j k =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |r j k|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ j))
  have hBO : B =O[atTop] fun k : ℕ => Real.log (k + 1) :=
    Asymptotics.IsBigO.fun_sum fun j _ => (hβ j).abs_left
  obtain ⟨Cβ, hCβ, hB⟩ := hBO.exists_nonneg_abs_le_mul_log_add_two
  have hR : Tendsto R atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun j _ => (hr j).abs
  refine ⟨B, R, Cβ, hCβ, hB0, hR0,
    fun k => (le_abs_self _).trans (hB k), hR, ?_⟩
  intro j k pre hpre hne
  have hent : ∀ p ∈ Ioo (0 : ℝ) 1,
      (k : ℝ) * a * (D j).entropyGain n (a / 2) k pre p -
          Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - B k ≤
        (D j).exactDerivative n (a / 2) k pre p := fun p hp =>
    (sub_le_sub_left (hβB j k) _).trans ((hpt j k pre hpre hne).1 p hp).2.1
  refine ⟨fun p hp => ⟨((hpt j k pre hpre hne).1 p hp).1, hent p hp,
    fun E₀ hE₀ => ?_⟩, ?_⟩
  · exact (((hpt j k pre hpre hne).1 p hp).2.2 E₀ hE₀).trans
      (add_le_add_left (hrR j k) _)
  · intro p₀ p₁ h0 h01 h1
    have ht : (0 : ℝ) ≤ a / 2 := by positivity
    have hL : IntervalIntegrable
        (fun p => (k : ℝ) * a * (D j).entropyGain n (a / 2) k pre p -
          Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - B k) volume 0 1 :=
      ((((D j).intervalIntegrable_entropyGain (hD j) ht (hcomm j k) hne).const_mul _).sub
        intervalIntegrable_const).sub intervalIntegrable_const
    exact (D j).integral_le_log_filteredNormSq_sub (hD j) ht (hcomm j k) hne hL hent
      h0 h01 h1

end TensorPower.ReplicaTransport
