/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterZeroFloorEnergy

/-!
# Zero-floor energy specializations

The tests keep empty chains and empty interaction families admissible, and apply the
full-system gap to the same chosen normalized output. No invertibility assumption is
made about the zero-floor maximizing filters.
-/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {m : ℕ}

example (D : ℕ → Finset V) {Ω : EuclideanSpace ℂ (SiteConfig n)} (hΩ : Ω ≠ 0) :
    ∃ K : (j : Fin 0) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      0 < ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖ := by
  have heig : toEuclideanLin (∑ _i : Empty, (0 : Matrix (SiteConfig n) (SiteConfig n) ℂ)) Ω =
      ((0 : ℝ) : ℂ) • Ω := by simp
  obtain ⟨K, _, _, hpos, _⟩ := exists_max_feasible_chain_zero_floor_energy
    (n := n) (m := 0) D (by intro i; exact i.elim0)
    (fun i ↦ i.elim0) (by intro i; exact i.elim0) (by intro i; exact i.elim0)
    hΩ (fun _i : Empty ↦ (0 : Matrix (SiteConfig n) (SiteConfig n) ℂ))
    (fun _i : Empty ↦ (∅ : Finset V)) (by intro i; exact i.elim)
    (by intro i; exact i.elim) (c₀ := 0) (by intro i; exact i.elim)
    (by intro i; exact i.elim) heig
  exact ⟨K, hpos⟩

example (D : ℕ → Finset V) (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha2 : ∀ j, a j ≤ 1 / 2)
    {Ω : EuclideanSpace ℂ (SiteConfig n)} (hΩ : Ω ≠ 0) :
    ∃ K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      (∀ j, IsFeasibleFilter 0 (a j) (K j)) ∧
      0 < ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖ := by
  have heig : toEuclideanLin (∑ _i : Empty, (0 : Matrix (SiteConfig n) (SiteConfig n) ℂ)) Ω =
      ((0 : ℝ) : ℂ) • Ω := by simp
  obtain ⟨K, hK, _, hpos, _⟩ := exists_max_feasible_chain_zero_floor_energy
    D hD a ha ha2 hΩ
    (fun _i : Empty ↦ (0 : Matrix (SiteConfig n) (SiteConfig n) ℂ))
    (fun _i : Empty ↦ (∅ : Finset V)) (by intro i; exact i.elim)
    (by intro i; exact i.elim) (c₀ := 0) (by intro i; exact i.elim)
    (by intro i; exact i.elim) heig
  exact ⟨K, hK, hpos⟩

example (D : ℕ → Finset V) (hD : ∀ i j : Fin m, i ≤ j → D i ⊆ D j)
    (a : Fin m → ℝ) (ha : ∀ j, 0 < a j) (ha2 : ∀ j, a j ≤ 1 / 2)
    {Ω : EuclideanSpace ℂ (SiteConfig n)} (hΩ : ‖Ω‖ = 1)
    {ι : Type*} [Fintype ι] (h : ι → Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (S : ι → Finset V) (hsupp : ∀ i, IsSupportedOn (h i) (S i))
    (hherm : ∀ i, (h i).IsHermitian) {c₀ : ℝ} (hnorm : ∀ i, ‖h i‖ ≤ c₀)
    (hsingle : ∀ i, ∀ j ∈ splitIndices (S i) D m,
      ∀ j' ∈ splitIndices (S i) D m, j = j')
    {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    (heig : toEuclideanLin (∑ i, h i) Ω = (E₀ : ℂ) • Ω)
    (hgap : ((∑ i, h i) - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec Ω.ofLp (star Ω.ofLp))).PosSemidef) :
    ∃ K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      (∀ j, IsFeasibleFilter 0 (a j) (K j)) ∧
      (∀ K' : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
        (∀ j, IsFeasibleFilter 0 (a j) (K' j)) →
        ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
          ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) ∧
      let ψ := toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω
      let φ := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
      0 < ‖ψ‖ ∧ ‖φ‖ = 1 ∧
        (⟪φ, toEuclideanLin (∑ i, h i) φ⟫_ℂ).re - E₀ ≤
          ∑ j : Fin m, 4 * a j ^ 2 *
            ∑ i ∈ crossingTerms S (D j), supportDim n (S i) ^ 2 * c₀ ∧
        1 - (∑ j : Fin m, 4 * a j ^ 2 *
          ∑ i ∈ crossingTerms S (D j), supportDim n (S i) ^ 2 * c₀) / Δ ≤
            ‖⟪Ω, φ⟫_ℂ‖ ^ 2 := by
  have hΩ0 : Ω ≠ 0 := fun h0 ↦ by simp [h0] at hΩ
  obtain ⟨K, hK, hmax, hpos, hunit, henergy⟩ :=
    exists_max_feasible_chain_zero_floor_normalized_energy
      D hD a ha ha2 hΩ0 h S hsupp hherm hnorm hsingle heig
  exact ⟨K, hK, hmax, hpos, hunit, henergy,
    sq_norm_inner_ge_of_gap hΔ hgap hunit henergy⟩

end Entropy
