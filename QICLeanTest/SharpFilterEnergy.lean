/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterChainEnergy

/-! The one-endpoint constant is derived from support, not supplied as a decomposition. -/

open Entropy Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

example {B S : Finset V} {v : V} (hinside : S ∩ B = {v}) :
    Fintype.card (InnerConfig n B S) = n v := by
  rw [card_innerConfig, hinside, Finset.prod_singleton]

-- Arbitrary spectator dimensions do not enter the one-crossing coefficient.
example {B S : Finset V} {v : V} (hinside : S ∩ B = {v})
    {L W : Matrix (RegionConfig n B) (RegionConfig n B) ℂ} {l p : RegionConfig n B → ℝ}
    {φ : EuclideanSpace ℂ (SiteConfig n)} (hφ : ‖φ‖ = 1) (hW : Wᴴ * W = 1)
    (hl : ∀ i, 0 < l i) (hL : L = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ)
    (hρ : regionState B φ = W * diagonal (fun i ↦ (p i : ℂ)) * Wᴴ)
    {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hX : IsSupportedOn X S) (hXh : X.IsHermitian)
    (σ₀ : SiteConfig n) {J a : ℝ} (hJ : ‖X‖ ≤ J) (ha : a ≤ 1)
    (hclip : ∀ i k, 0 < p i → 0 < p k →
      |Real.log (l i) - Real.log (l k)| ≤ a / 2 * |Real.log (p i) - Real.log (p k)|) :
    |(⟪φ, toEuclideanLin X φ⟫_ℂ -
      ⟪φ, toEuclideanLin (localLift B L * X * localLift B L⁻¹) φ⟫_ℂ).re| ≤
      (n v : ℝ) ^ 2 * J * a ^ 2 := by
  have h := abs_re_inner_sub_conj_localLift_le_sharp hφ hW hl hL hρ hX hXh σ₀ hJ ha hclip
  rw [card_innerConfig, hinside, Finset.prod_singleton] at h
  nlinarith only [h]

-- The energy sum retains each interaction’s actual inside-support cardinality.
example {m : ℕ} (D : ℕ → Finset V) (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (K : (i : Fin m) → Matrix (RegionConfig n (D i)) (RegionConfig n (D i)) ℂ)
    (hunit : ∀ i, IsUnit (K i).det) {φ : EuclideanSpace ℂ (SiteConfig n)} (hφ : ‖φ‖ = 1)
    (a : Fin m → ℝ) (ha : ∀ j, a j ≤ 1)
    (hcl : ∀ j, K j * regionState (D j) φ = regionState (D j) φ * K j ∧
      ∃ (W : Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ)
        (l q : RegionConfig n (D j) → ℝ),
        Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧ K j = W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
        regionState (D j) φ = W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ ∧
        ∀ i k, 0 < q i → 0 < q k →
          |Real.log (l i) - Real.log (l k)| ≤ a j / 2 * |Real.log (q i) - Real.log (q k)|)
    {ι : Type*} [Fintype ι] (h : ι → Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (S : ι → Finset V) (hsupp : ∀ i, IsSupportedOn (h i) (S i)) (hherm : ∀ i, (h i).IsHermitian)
    (σ₀ : SiteConfig n) {c₀ : ℝ} (hnorm : ∀ i, ‖h i‖ ≤ c₀)
    (hsingle : ∀ i, ∀ j ∈ splitIndices (S i) D m, ∀ j' ∈ splitIndices (S i) D m, j = j')
    {E₀ : ℝ}
    (heig : toEuclideanLin (liftProd (chainList D K fun _ ↦ True) * (∑ i, h i) *
      liftProdInv (chainList D K fun _ ↦ True)) φ = (E₀ : ℂ) • φ) :
    (⟪φ, toEuclideanLin (∑ i, h i) φ⟫_ℂ).re - E₀ ≤
      ∑ j : Fin m, a j ^ 2 *
        ∑ i ∈ crossingTerms S (D j), Fintype.card (InnerConfig n (D j) (S i)) ^ 2 * c₀ := by
  exact re_inner_sub_le_of_chain_sharp D hD K hunit hφ a ha hcl h S hsupp hherm σ₀
    hnorm hsingle heig
