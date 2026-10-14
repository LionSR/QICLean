/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.PatchStationarity

/-!
# First-order trace inequalities for normalized patch outputs

For each factor of an ordered patch minimizer, every commuting density matrix
satisfies the first-order trace inequality against the regional state of the
normalized output. The inequality remains valid when the output is zero.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `03-patches.tex`, lines 170–178,
`eq:patch-simplex-derivative`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- Let `ρ` be the regional state of the normalized output of an ordered patch
minimizer. For each factor with density `x`, every density matrix `y` commuting
with `x` satisfies `Re Tr (ρ (x + b 1)⁻¹ y) ≤ Re Tr (ρ (x + b 1)⁻¹ x)`.
If the output vanishes, then `ρ = 0` and both sides vanish.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–178,
`eq:patch-simplex-derivative`. -/
theorem re_trace_variation_le_of_isPatchMinimizer {b : ℝ} (hb : 0 < b)
    {l : List (PatchFactor n)} {Ω : EuclideanSpace ℂ (SiteConfig n)}
    (hexp : ∀ f ∈ l, 0 < f.exponent)
    (hden : ∀ f ∈ l, f.density.PosSemidef ∧ f.density.trace = 1)
    (hnest : l.Pairwise fun g g' ↦ g'.region ⊆ g.region)
    (hmin : IsPatchMinimizer b l Ω) :
    ∀ f ∈ l, ∀ y : Matrix (RegionConfig n f.region) (RegionConfig n f.region) ℂ,
      y.PosSemidef → y.trace = 1 → Commute f.density y →
      (regionState f.region (patchState b l Ω) *
          (f.density + b • 1) ^ (-1 : ℝ) * y).trace.re ≤
        (regionState f.region (patchState b l Ω) *
          (f.density + b • 1) ^ (-1 : ℝ) * f.density).trace.re := by
  intro f hf y hy hyt hxy
  by_cases hne : Nonempty (SiteConfig n)
  · obtain ⟨σ₀⟩ := hne
    obtain ⟨pre, post, hl⟩ := List.append_of_mem hf
    have hchain := isDescendingChain_of_patch_min hb σ₀ hexp hden hnest hmin
      pre (f :: post) hl
    subst hl
    have hsub : ∀ p ∈ pre.map (PatchFactor.filter b), f.region ⊆ p.1 :=
      List.forall_mem_map.mpr fun q hq ↦
        (List.pairwise_append.mp hnest).2.2 q hq f (by simp)
    have hmin' := hmin.coord hden
    simp only [patchOutput_append_cons] at hmin' hchain
    have hvar := re_trace_variation_le_of_patch_min (hden f hf).1 (hden f hf).2
      (hexp f hf) hb (liftProd (post.map (PatchFactor.filter b))) Ω σ₀
      hmin' hchain hsub y hy hyt hxy
    have hst : regionState f.region (patchState b (pre ++ f :: post) Ω) =
        (‖patchOutput b (pre ++ f :: post) Ω‖⁻¹ ^ 2) •
          regionState f.region (patchOutput b (pre ++ f :: post) Ω) := by
      rw [patchState, regionState_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), Complex.coe_smul]
    simpa only [hst, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul,
      patchOutput_append_cons] using
      mul_le_mul_of_nonneg_left hvar (sq_nonneg ‖patchOutput b (pre ++ f :: post) Ω‖⁻¹)
  · have : IsEmpty (SiteConfig n) := not_nonempty_iff.mp hne
    have h0 : regionState f.region (patchState b l Ω) = 0 := by
      rw [Subsingleton.elim (patchState b l Ω) ((0 : ℂ) • patchState b l Ω),
        regionState_smul]
      simp
    simp [h0]

end Entropy
