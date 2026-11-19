/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.KroneckerSum
import QICLean.ManyBody.Sites.Placement

/-!
# Gapped ground vectors of a sum of single-site Hamiltonians

Let `H = ∑ᵥ Hᵥ ⊗ 1`, where each Hermitian `Hᵥ` acts on the single site `v` of a nonempty finite
set of sites. If `H` is gapped at `E₀` with gap `Δ > 0` and its ground space is the line through
a unit vector `Ω`, then `Ω = ⨂ᵥ ωᵥ` for unit vectors `ωᵥ`, `E₀ = ∑ᵥ aᵥ`, and each `Hᵥ` is
gapped at `aᵥ` with the same gap `Δ` and ground space the line through `ωᵥ`.

At each site `v`, the cut of the system into `v` and the other sites writes `H` as the Kronecker
sum `Hᵥ ⊗ 1 + 1 ⊗ H'`, and `ManyBody.exists_isGapped_factors_of_kronecker_sum` gives the gap of
`Hᵥ`, a unit vector `uᵥ` spanning its ground space at `aᵥ`, and `(Hᵥ ⊗ 1) Ω = aᵥ Ω`. Summing over
`v` gives `E₀ = ∑ᵥ aᵥ`. The unit product `⨂ᵥ uᵥ` has energy `∑ᵥ aᵥ`, so it lies on the line
through `Ω`; the phase between them is absorbed into one factor.

Moved from TNLean, `TNLean/Lattice/ProductGroundState.lean` at commit `e41c3b63`, where the
factors were indexed by `Fin (n + 1)` and the summands were written with a separate definition
`factorOperator`; here they are the placements `place {v} Hᵥ` on a system of sites.

## Main results

* `ManyBody.exists_isGapped_factors_of_sum_place` — the factorization of the ground vector.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, Lemma reductions (`lem:reductions`), `part1_arealaw.tex`, lines 64–89.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]

/-- Configurations of the system are families of configurations of the single sites. -/
private def siteConfigEquiv : Config X ≃ ∀ v, RegionConfig X {v} :=
  Equiv.piCongrRight fun v ↦ (Equiv.piUnique fun w : ({v} : Finset V) ↦ X w.1).symm

private theorem siteConfigEquiv_apply (x : Config X) (v : V) :
    siteConfigEquiv x v = fun w : ({v} : Finset V) ↦ x w := by
  funext w
  obtain ⟨w, hw⟩ := w
  obtain rfl := Finset.mem_singleton.mp hw
  rfl

/-- The product vector `x ↦ ∏ᵥ uᵥ(x_v)`. -/
private noncomputable def siteProduct (u : ∀ v, EuclideanSpace ℂ (RegionConfig X {v})) :
    Config X → ℂ :=
  fun x ↦ ∏ v, u v (fun w : ({v} : Finset V) ↦ x w)

private theorem star_siteProduct_dotProduct (u : ∀ v, EuclideanSpace ℂ (RegionConfig X {v})) :
    star (siteProduct u) ⬝ᵥ siteProduct u = ∏ v, star (WithLp.ofLp (u v)) ⬝ᵥ WithLp.ofLp (u v) := by
  simp only [dotProduct, Fintype.prod_sum]
  rw [← siteConfigEquiv.sum_comp]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  simp only [siteProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib,
    siteConfigEquiv_apply]

variable [∀ v, DecidableEq (X v)]

/-- A single-site Hamiltonian acts on a product vector through its own factor. -/
private theorem place_mulVec_siteProduct (u : ∀ v, EuclideanSpace ℂ (RegionConfig X {v})) (v : V)
    (K : Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ) {a : ℝ}
    (hK : K *ᵥ WithLp.ofLp (u v) = (a : ℂ) • WithLp.ofLp (u v)) :
    place {v} K *ᵥ siteProduct u = (a : ℂ) • siteProduct u := by
  funext σ
  rw [place_mulVec_apply]
  have hglue (r : RegionConfig X {v}) :
      siteProduct u ((cutEquiv X {v}).symm (r, (cutEquiv X {v} σ).2)) =
        u v r * ∏ w ∈ Finset.univ.erase v, u w (fun z : ({w} : Finset V) ↦ σ z) := by
    rw [siteProduct, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
    congr 1
    · refine congrArg (WithLp.ofLp (u v)) (funext fun z ↦ ?_)
      obtain ⟨z, hz⟩ := z
      exact cutEquiv_symm_apply_mem _ _ hz
    · refine Finset.prod_congr rfl fun w hw ↦ congrArg (WithLp.ofLp (u w)) (funext fun z ↦ ?_)
      obtain ⟨z, hz⟩ := z
      obtain rfl := Finset.mem_singleton.mp hz
      exact cutEquiv_symm_apply_not_mem _ _
        (by simpa using (Finset.ne_of_mem_erase hw))
  simp only [hglue, ← mul_assoc, ← Finset.sum_mul]
  have hv := congrFun hK (fun w : ({v} : Finset V) ↦ σ w)
  simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hv
  rw [hv, Pi.smul_apply, smul_eq_mul, siteProduct, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    mul_assoc]

/-- At one site, the Kronecker-sum factorization gives the gap and the ground line of the
single-site Hamiltonian, and its eigenvalue on the ground vector. -/
private theorem exists_site_factor {H : ∀ v, Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ}
    (hH : ∀ v, (H v).IsHermitian) {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Config X)} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgs : IsGapped (∑ v, place {v} (H v)) E₀ Δ)
    (hspan : groundSpace (∑ v, place {v} (H v)) E₀ = Submodule.span ℂ {Ω}) (v : V) :
    ∃ (a : ℝ) (u : EuclideanSpace ℂ (RegionConfig X {v})), ‖u‖ = 1 ∧ IsGapped (H v) a Δ ∧
      groundSpace (H v) a = Submodule.span ℂ {u} ∧
      place {v} (H v) *ᵥ WithLp.ofLp Ω = (a : ℂ) • WithLp.ofLp Ω := by
  classical
  set c := cutEquiv X {v}
  have hne : Nonempty (Config X) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Ω = 0 := by
      apply WithLp.ofLp_injective 2
      funext x
      exact isEmptyElim x
    simp [this] at hΩ
  obtain ⟨x₀⟩ := hne
  let r₀ : RegionConfig X {v} := (c x₀).1
  let B := ∑ w ∈ Finset.univ.erase v, place {w} (H w)
  have hsplit : ∑ w, place {w} (H w) = place {v} (H v) + B :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have hB : B ∈ supportedOperators X ({v}ᶜ) := by
    refine sum_mem fun w hw ↦ supportedOperators_mono ?_ (place_mem_supportedOperators _)
    simpa [eq_comm] using Finset.ne_of_mem_erase hw
  obtain ⟨B₂, hB₂⟩ := exists_eq_one_kronecker_of_mem_supportedOperators
    (D := {v}) disjoint_compl_left hB
  have hBherm : B.IsHermitian :=
    (isSelfAdjoint_sum _ fun w _ ↦ (isHermitian_place (hH w)).isSelfAdjoint).isHermitian
  have hA : place {v} (H v) =
      ((H v) ⊗ₖ (1 : Matrix (ComplConfig X {v}) (ComplConfig X {v}) ℂ)).submatrix c c := by
    simp [place, reindex_apply, c]
  have hcut : (∑ w, place {w} (H w)).submatrix c.symm c.symm =
      H v ⊗ₖ (1 : Matrix (ComplConfig X {v}) (ComplConfig X {v}) ℂ) +
        (1 : Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ) ⊗ₖ B₂ := by
    rw [hsplit, hA, hB₂]
    ext i j
    simp [c]
  have hB₂herm : B₂.IsHermitian := by
    have hK : ((1 : Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ) ⊗ₖ B₂).IsHermitian := by
      have := hBherm.submatrix c.symm
      rwa [hB₂, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at this
    refine IsHermitian.ext fun i j ↦ ?_
    simpa only [kroneckerMap_apply, one_apply_eq, one_mul] using hK.apply (r₀, i) (r₀, j)
  have hgs' := (isGapped_submatrix_iff c.symm).mpr hgs
  have hspan' := groundSpace_submatrix_eq_span c.symm hspan
  rw [hcut] at hgs' hspan'
  have hn' : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ c.symm.symm Ω‖ = 1 :=
    (LinearIsometryEquiv.norm_map _ _).trans hΩ
  obtain ⟨a, b, u, w, -, hprod, hu, -⟩ :=
    exists_isGapped_factors_of_kronecker_sum (hH v) hB₂herm hΔ hn' hgs' hspan'
  refine ⟨a, u, hu.1, hu.2.1, hu.2.2, ?_⟩
  have hΩc : WithLp.ofLp Ω ∘ c.symm = fun p ↦ u p.1 * w p.2 := by
    funext p
    simpa [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using hprod p
  have hu' := mulVec_eq_of_groundSpace_eq_span hu.2.2
  rw [hA, submatrix_mulVec_equiv, hΩc, kronecker_mulVec_mul, one_mulVec, hu']
  funext σ
  have hσ := congrFun hΩc (c σ)
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at hσ
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, hσ, mul_assoc]

/-- **A gapped unique ground vector of a sum of single-site Hamiltonians is a product.** Let
`Hᵥ` be Hermitian on the site `v` of a nonempty finite set of sites, and let
`H = ∑ᵥ place {v} Hᵥ` be gapped at `E₀` with gap `Δ > 0` and ground space the line through the
unit vector `Ω`. Then `Ω(x) = ∏ᵥ ωᵥ(x_v)` for unit vectors `ωᵥ`, `E₀ = ∑ᵥ aᵥ`, and each `Hᵥ`
is gapped at `aᵥ` with the same gap `Δ` and ground space the line through `ωᵥ`.
TNLean one-dimensional note, Lemma reductions (`lem:reductions`), `part1_arealaw.tex`,
lines 64–89: each component Hamiltonian inherits the gap inequality with the same gap. -/
theorem exists_isGapped_factors_of_sum_place [Nonempty V]
    {H : ∀ v, Matrix (RegionConfig X {v}) (RegionConfig X {v}) ℂ} (hH : ∀ v, (H v).IsHermitian)
    {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Config X)} (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1)
    (hgs : IsGapped (∑ v, place {v} (H v)) E₀ Δ)
    (hspan : groundSpace (∑ v, place {v} (H v)) E₀ = Submodule.span ℂ {Ω}) :
    ∃ (a : V → ℝ) (ω : ∀ v, EuclideanSpace ℂ (RegionConfig X {v})), E₀ = ∑ v, a v ∧
      (∀ x, Ω x = ∏ v, ω v (fun w : ({v} : Finset V) ↦ x w)) ∧
      ∀ v, ‖ω v‖ = 1 ∧ IsGapped (H v) (a v) Δ ∧ groundSpace (H v) (a v) = Submodule.span ℂ {ω v} := by
  classical
  choose a u hu1 hgap hsp hev using exists_site_factor hH hΔ hΩ hgs hspan
  have hΩne : WithLp.ofLp Ω ≠ 0 := by
    intro h
    have : Ω = 0 := WithLp.ofLp_injective 2 h
    simp [this] at hΩ
  -- The energy is additive.
  have hE : E₀ = ∑ v, a v := by
    have hsum : (∑ v, place {v} (H v)) *ᵥ WithLp.ofLp Ω = ((∑ v, a v : ℝ) : ℂ) • WithLp.ofLp Ω := by
      rw [sum_mulVec]
      simp only [hev, ← Finset.sum_smul, Complex.ofReal_sum]
    rw [mulVec_eq_of_groundSpace_eq_span hspan] at hsum
    exact_mod_cast smul_left_injective ℂ hΩne hsum
  -- The product of the factor ground vectors is a unit ground vector.
  have hu1' (v : V) : star (WithLp.ofLp (u v)) ⬝ᵥ WithLp.ofLp (u v) = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      inner_self_eq_one_of_norm_eq_one (𝕜 := ℂ) (hu1 v)
  have hψ1 : star (siteProduct u) ⬝ᵥ siteProduct u = 1 := by
    rw [star_siteProduct_dotProduct]
    simp [hu1']
  have hψ : WithLp.toLp 2 (siteProduct u) ∈ groundSpace (∑ v, place {v} (H v)) E₀ := by
    rw [mem_groundSpace_iff_mulVec, WithLp.ofLp_toLp, sum_mulVec, hE]
    simp only [fun v ↦ place_mulVec_siteProduct u v (H v) (mulVec_eq_of_groundSpace_eq_span (hsp v)),
      ← Finset.sum_smul, Complex.ofReal_sum]
  rw [hspan] at hψ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hψ
  have hc' : siteProduct u = c • WithLp.ofLp Ω := by
    simpa using (congrArg WithLp.ofLp hc).symm
  have hΩ1 : star (WithLp.ofLp Ω) ⬝ᵥ WithLp.ofLp Ω = 1 := by
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
      inner_self_eq_one_of_norm_eq_one (𝕜 := ℂ) hΩ
  have hcc : star c * c = 1 := by
    rw [hc', star_smul, smul_dotProduct, dotProduct_smul, hΩ1] at hψ1
    simpa [mul_comm] using hψ1
  -- Absorb the phase into one factor.
  obtain ⟨v₀⟩ := ‹Nonempty V›
  let ω : ∀ v, EuclideanSpace ℂ (RegionConfig X {v}) := Function.update u v₀ (star c • u v₀)
  have hω₀ : ω v₀ = star c • u v₀ := Function.update_self _ _ _
  have hω (v : V) (hv : v ≠ v₀) : ω v = u v := Function.update_of_ne hv _ _
  have hcne : star c ≠ 0 := by
    intro h
    simp [h] at hcc
  refine ⟨a, ω, hE, fun x ↦ ?_, fun v ↦ ?_⟩
  · have hx := congrFun hc' x
    rw [Pi.smul_apply, smul_eq_mul] at hx
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v₀), hω₀,
      Finset.prod_congr rfl fun v hv ↦ by rw [hω v (Finset.ne_of_mem_erase hv)]]
    have hprod : siteProduct u x =
        u v₀ (fun w : ({v₀} : Finset V) ↦ x w) *
          ∏ v ∈ Finset.univ.erase v₀, u v (fun w : ({v} : Finset V) ↦ x w) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ v₀)).symm
    rw [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← hprod, hx, ← mul_assoc, hcc, one_mul]
  · by_cases hv : v = v₀
    · subst hv
      rw [hω₀]
      refine ⟨?_, hgap v, ?_⟩
      · rw [norm_smul, hu1, mul_one]
        have h2 : ((Complex.normSq c : ℝ) : ℂ) = 1 := by
          rw [← Complex.mul_conj, mul_comm]
          exact hcc
        have h3 : ‖c‖ ^ 2 = 1 := by
          rw [← Complex.normSq_eq_norm_sq]
          exact_mod_cast h2
        rw [norm_star]
        nlinarith [norm_nonneg c]
      · rw [hsp, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hcne)]
    · rw [hω v hv]
      exact ⟨hu1 v, hgap v, hsp v⟩

end ManyBody
