/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcConjugation
import QICLean.Analysis.CommutingHermitian
import QICLean.Analysis.PatchRegulator
import QICLean.Analysis.PosSemidefCommute
import QICLean.Analysis.ShiftedDensityCommutation
import QICLean.Entropy.FilterChainEnergy
import QICLean.Entropy.FilterOptimizer
import QICLean.Entropy.RegionEntropy

/-!
# Stationarity of the ordered patch objective

Let `x_1, …, x_m` be density matrices on nested regions `X_1 ⊆ ⋯ ⊆ X_m`, let `a_j > 0` and
`b > 0`, and put `L_j = (x_j + b 1)^{-a_j/2}`. At every minimizer of the ordered patch objective
`‖L_m ⋯ L_1 Ω‖` over the densities, the regional states `ρ_j` of the normalized output
`φ = L_m ⋯ L_1 Ω / ‖L_m ⋯ L_1 Ω‖` satisfy

* `[x_j, ρ_j] = 0` (and `[L_j, ρ_j] = 0`), and
* `ρ_j ≤ x_j + b 1`.

These are the hypotheses of `Matrix.PosSemidef.shiftedRegulator_bounds`.

The commutation is proved in decreasing order of `j`, as in the source: the unitary variation
`x_j ↦ U x_j U*` keeps a density matrix, conjugates `L_j`, and the descending trace argument
removes the outer filters (`Entropy.commute_regionState_of_unitary_min`). For the order, vary
`x_j` along the segment toward a density matrix `y` commuting with `x_j`. The derivative of
`(x + s (y - x) + b 1)^r` at `s = 0` is computed in a common eigenbasis, and the descending trace
argument turns the one-sided first-order condition into
`Re Tr (G y) ≤ Re Tr (G x)` with `G = ρ (x + b 1)^{-1}`. Testing against the rank-one
projections onto a common eigenbasis of `G` and `x` gives `G ≤ λ 1` with
`λ = Re Tr (G x) ≤ Tr ρ`, hence `ρ = G (x + b 1) ≤ (Tr ρ) (x + b 1)`. This replaces the
coordinate form of the source's eigenvalue conditions `eq:patch-simplex-derivative`,
`eq:patch-kkt` and `eq:patch-clipped-eigenvalues` by an equivalent operator form.

## Main results

* `Matrix.PosSemidef.hasDerivAt_add_smul_add_smul_one_rpow_of_commute`: the derivative of a
  shifted power along a commuting direction.
* `Matrix.PosSemidef.le_trace_smul_add_smul_one_of_forall_density`: the density order from the
  first-order conditions along commuting densities.
* `Entropy.patchFilter_commute_regionState`, `Entropy.re_trace_variation_le_of_patch_min`:
  stationarity of one factor of the ordered product.
* `Entropy.patch_stationarity`: commutation and density order at every minimizer.
* `Entropy.patch_shiftedRegulator_bounds`: the regulator bounds at every minimizer.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
2026, `03-patches.tex`, lines 130–205: `eq:patch-stationarity-commutation`,
`eq:patch-trace-stripping`, `eq:patch-simplex-derivative`, `eq:patch-kkt`,
`eq:patch-clipped-eigenvalues`; source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This closes the continuation recorded in
`docs/paper-gaps/oai26_peps_patch_stationarity_gap.tex`.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Filter Topology

namespace Matrix

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- Real powers of a unitarily diagonalized matrix with nonnegative eigenvalues act on the
eigenvalues. -/
theorem rpow_unitary_mul_diagonal_mul {U : Matrix k k ℂ} (hU : Uᴴ * U = 1) (hU' : U * Uᴴ = 1)
    {d : k → ℝ} (hd : ∀ i, 0 ≤ d i) (r : ℝ) :
    (U * diagonal (fun i ↦ (d i : ℂ)) * Uᴴ) ^ r =
      U * diagonal (fun i ↦ ((d i ^ r : ℝ) : ℂ)) * Uᴴ := by
  have hUu : U ∈ unitary (Matrix k k ℂ) := Unitary.mem_iff.mpr
    ⟨by simpa [star_eq_conjTranspose] using hU, by simpa [star_eq_conjTranspose] using hU'⟩
  have hD : (diagonal (fun i ↦ (d i : ℂ))).PosSemidef :=
    posSemidef_diagonal_iff.mpr fun i ↦ Complex.zero_le_real.mpr (hd i)
  have h := rpow_conj_unitary hD r ⟨U, hUu⟩
  simp only [star_eq_conjTranspose] at h
  rw [h, CFC.rpow_eq_cfc_real hD.nonneg,
    cfc_diagonal d (fun t : ℝ ↦ t ^ r) ((Set.finite_range d).continuousOn _)]

/-- **Derivative of a shifted power along a commuting direction.** For a positive semidefinite
`x`, a Hermitian `h` commuting with `x`, and `b > 0`,
`d/ds (x + s h + b 1)^r |_{s=0} = r (x + b 1)^{r-1} h`.
PEPS manuscript, `03-patches.tex`, lines 170–178: the diagonal variation commutes with
`x_j + b 1`. -/
theorem PosSemidef.hasDerivAt_add_smul_add_smul_one_rpow_of_commute {x h : Matrix k k ℂ}
    (hx : x.PosSemidef) (hh : h.IsHermitian) (hxh : x * h = h * x) {b : ℝ} (hb : 0 < b)
    (r : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (x + s • h + b • (1 : Matrix k k ℂ)) ^ r)
      (r • ((x + b • (1 : Matrix k k ℂ)) ^ (r - 1) * h)) 0 := by
  obtain ⟨U, a, c, hU, hU', hxU, hhU⟩ :=
    exists_unitary_diagonal_of_commute hx.isHermitian hh hxh
  have ha : ∀ i, 0 ≤ a i := by
    have hD := hx.conjTranspose_mul_mul_same U
    have he : Uᴴ * (U * diagonal (fun i ↦ (a i : ℂ)) * Uᴴ) * U =
        diagonal (fun i ↦ (a i : ℂ)) := by
      simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
      rw [Matrix.mul_assoc, hU, Matrix.mul_one]
    rw [hxU, he] at hD
    exact fun i ↦ Complex.zero_le_real.mp (posSemidef_diagonal_iff.mp hD i)
  have hdec : ∀ s : ℝ, x + s • h + b • (1 : Matrix k k ℂ) =
      U * diagonal (fun i ↦ ((a i + s * c i + b : ℝ) : ℂ)) * Uᴴ := by
    intro s
    have hdiag : diagonal (fun i ↦ ((a i + s * c i + b : ℝ) : ℂ)) =
        diagonal (fun i ↦ (a i : ℂ)) + s • diagonal (fun i ↦ (c i : ℂ)) +
          b • (1 : Matrix k k ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hdiag, hxU, hhU]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hU']
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, 0 < a i + s * c i + b := by
    refine Filter.eventually_all.mpr fun i ↦ ?_
    have hc : ContinuousAt (fun s : ℝ ↦ a i + s * c i + b) 0 := by fun_prop
    exact continuousAt_const.eventually_lt hc (by simp only [zero_mul, add_zero]; linarith [ha i])
  let d : ℝ → k → ℂ := fun s i ↦ (((a i + s * c i + b) ^ r : ℝ) : ℂ)
  let d' : k → ℂ := fun i ↦ ((r * (a i + b) ^ (r - 1) * c i : ℝ) : ℂ)
  have hd : HasDerivAt d d' 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have hpos0 : a i + 0 * c i + b ≠ 0 := by
      simp only [zero_mul, add_zero]; linarith [ha i]
    have h1 : HasDerivAt (fun s : ℝ ↦ a i + s * c i + b) (c i) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (c i)).const_add (a i)).add_const b
    have h2 := (h1.rpow_const (p := r) (Or.inl hpos0)).ofReal_comp
    convert h2 using 1
    simp only [d', zero_mul, add_zero]
    push_cast
    ring
  let L : (k → ℂ) →L[ℝ] Matrix k k ℂ := (diagonalLinearMap k ℝ ℂ).toContinuousLinearMap
  have hD := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have hUD := (hD.const_mul U).mul_const Uᴴ
  have heq : (fun s ↦ U * (L ∘ d) s * Uᴴ) =ᶠ[𝓝 0]
      (fun s : ℝ ↦ (x + s • h + b • (1 : Matrix k k ℂ)) ^ r) := by
    filter_upwards [hpos] with s hs
    rw [hdec s, rpow_unitary_mul_diagonal_mul hU hU' (fun i ↦ (hs i).le) r]
    rfl
  have hderiv : U * L d' * Uᴴ = r • ((x + b • (1 : Matrix k k ℂ)) ^ (r - 1) * h) := by
    have h0 := hdec 0
    simp only [zero_mul, add_zero, zero_smul] at h0
    rw [h0, rpow_unitary_mul_diagonal_mul hU hU' (fun i ↦ by linarith [ha i]) (r - 1), hhU]
    have e : U * diagonal (fun i ↦ (((a i + b) ^ (r - 1) : ℝ) : ℂ)) * Uᴴ *
        (U * diagonal (fun i ↦ (c i : ℂ)) * Uᴴ) =
        U * (diagonal (fun i ↦ (((a i + b) ^ (r - 1) : ℝ) : ℂ)) * (Uᴴ * U) *
          diagonal (fun i ↦ (c i : ℂ))) * Uᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, hU, Matrix.mul_one, diagonal_mul_diagonal]
    have hd' : L d' = r • diagonal (fun i ↦ (((a i + b) ^ (r - 1) : ℝ) : ℂ) * (c i : ℂ)) := by
      change diagonal d' = _
      rw [← diagonal_smul]
      congr 1
      funext i
      simp only [d', Pi.smul_apply, Complex.real_smul]
      push_cast
      ring
    rw [hd', Matrix.mul_smul, Matrix.smul_mul]
  exact hderiv ▸ hUD.congr_of_eventuallyEq heq.symm

/-- **Density order from commuting first-order conditions.** Let `x, ρ ≥ 0` commute and
`b > 0`, and put `G = ρ (x + b 1)^{-1}`. If `Re Tr (G y) ≤ Re Tr (G x)` for every density
matrix `y` commuting with `x`, then `ρ ≤ (Re Tr ρ) (x + b 1)`.
PEPS manuscript, `03-patches.tex`, lines 170–200, the operator form of `eq:patch-kkt` and
`eq:patch-clipped-eigenvalues`. -/
theorem PosSemidef.le_trace_smul_add_smul_one_of_forall_density {x ρ : Matrix k k ℂ}
    (hx : x.PosSemidef) (hρ : ρ.PosSemidef) (hxρ : Commute x ρ) {b : ℝ} (hb : 0 < b)
    (hvar : ∀ y : Matrix k k ℂ, y.PosSemidef → y.trace = 1 → Commute x y →
      (ρ * (x + b • (1 : Matrix k k ℂ)) ^ (-1 : ℝ) * y).trace.re ≤
        (ρ * (x + b • (1 : Matrix k k ℂ)) ^ (-1 : ℝ) * x).trace.re) :
    ρ ≤ ρ.trace.re • (x + b • (1 : Matrix k k ℂ)) := by
  set K := x + b • (1 : Matrix k k ℂ) with hKdef
  have hK : K.PosDef := hx.add_smul_one_posDef hb
  set Ki := K ^ (-1 : ℝ) with hKidef
  have hKiK : Ki * K = 1 := by
    have h := CFC.rpow_neg_mul_rpow (1 : ℝ) (a := K) hK.isStrictlyPositive
    rwa [CFC.rpow_one K hK.posSemidef.nonneg] at h
  have hKi : Ki.PosSemidef := nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hKix : Commute Ki x :=
    (hx.commute_add_smul_one_rpow_iff hb (by norm_num)).mpr (Commute.refl x)
  have hKiρ : Commute Ki ρ := (hx.commute_add_smul_one_rpow_iff hb (by norm_num)).mpr hxρ
  set G := ρ * Ki with hGdef
  have hG : G.PosSemidef := hρ.mul_of_commute hKi hKiρ.symm.eq
  have hGx : Commute G x := hxρ.symm.mul_left hKix
  have hGK : Commute G K :=
    hGx.add_right ((Commute.one_right G).smul_right b)
  obtain ⟨U, g, c, hU, hU', hGU, hxU⟩ :=
    exists_unitary_diagonal_of_commute hG.isHermitian hx.isHermitian hGx.eq
  have hconj : ∀ f₁ f₂ : k → ℂ, U * diagonal f₁ * Uᴴ * (U * diagonal f₂ * Uᴴ) =
      U * diagonal (f₁ * f₂) * Uᴴ := by
    intro f₁ f₂
    rw [show U * diagonal f₁ * Uᴴ * (U * diagonal f₂ * Uᴴ) =
        U * (diagonal f₁ * (Uᴴ * U) * diagonal f₂) * Uᴴ by simp only [Matrix.mul_assoc], hU,
      Matrix.mul_one, diagonal_mul_diagonal]
    rfl
  have htr : ∀ f : k → ℂ, (U * diagonal f * Uᴴ).trace = ∑ i, f i := by
    intro f
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, trace_diagonal]
  have hpsd : ∀ f : k → ℝ, (∀ i, 0 ≤ f i) →
      (U * diagonal (fun i ↦ (f i : ℂ)) * Uᴴ).PosSemidef := fun f hf ↦
    (posSemidef_diagonal_iff.mpr fun i ↦
      Complex.zero_le_real.mpr (hf i)).mul_mul_conjTranspose_same U
  set lam := (G * x).trace.re with hlam
  -- every eigenvalue of `G` is at most `lam`
  have hgle : ∀ i, g i ≤ lam := by
    intro i
    set e : k → ℝ := fun j ↦ if j = i then 1 else 0
    have he : ∀ j, 0 ≤ e j := fun j ↦ by simp only [e]; split_ifs <;> norm_num
    have hy := hvar (U * diagonal (fun j ↦ (e j : ℂ)) * Uᴴ) (hpsd e he)
      (by rw [htr]; simp [e, apply_ite]) (by
        rw [commute_iff_eq, hxU, hconj, hconj]
        congr 3
        exact mul_comm _ _)
    rw [hGU, hconj, htr] at hy
    simpa [e, Pi.mul_apply, ← hGU] using hy
  -- hence `G ≤ lam`
  have hGle : (lam • (1 : Matrix k k ℂ) - G).PosSemidef := by
    have h := hpsd (fun i ↦ lam - g i) fun i ↦ sub_nonneg.mpr (hgle i)
    convert h using 1
    rw [hGU]
    have hdiag : diagonal (fun i ↦ ((lam - g i : ℝ) : ℂ)) =
        lam • (1 : Matrix k k ℂ) - diagonal (fun i ↦ (g i : ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hU']
  -- `ρ = G K`
  have hρGK : G * K = ρ := by rw [hGdef, Matrix.mul_assoc, hKiK, Matrix.mul_one]
  have hlamK : (lam • K - ρ).PosSemidef := by
    have h := hGle.mul_of_commute hK.posSemidef
      (((Commute.one_left K).smul_left lam).sub_left hGK).eq
    rwa [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hρGK] at h
  -- `lam ≤ Re Tr ρ`
  have hlam_le : lam ≤ ρ.trace.re := by
    have hx' : x = K - b • (1 : Matrix k k ℂ) := by rw [hKdef]; abel
    have hGtr : 0 ≤ G.trace.re := (Complex.nonneg_iff.mp hG.trace_nonneg).1
    have : lam = ρ.trace.re - b * G.trace.re := by
      rw [hlam, hx', Matrix.mul_sub, hρGK, Matrix.mul_smul, Matrix.mul_one, trace_sub,
        trace_smul, Complex.sub_re, Complex.smul_re, smul_eq_mul]
    nlinarith
  rw [Matrix.le_iff]
  have h := hlamK.add (hK.posSemidef.smul (sub_nonneg.mpr hlam_le))
  convert h using 1
  module

end Matrix

namespace Entropy

section Calculus

variable {m p : Type*} [Fintype p] [DecidableEq p]

theorem mulApplyCLM_apply [Fintype m] (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix p p ℂ)
    (A : Matrix p p ℂ) (w : EuclideanSpace ℂ p) (X : Matrix m m ℂ) :
    mulApplyCLM Φ A w X = toEuclideanLin (A * Φ X) w := rfl

/-- The derivative of `s ↦ ‖A Φ(g s) w‖²` along a differentiable matrix path `g`. -/
theorem hasDerivAt_norm_sq_mulApply [Finite m] (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix p p ℂ)
    (A : Matrix p p ℂ) (w : EuclideanSpace ℂ p) {g : ℝ → Matrix m m ℂ} {g' : Matrix m m ℂ}
    {t : ℝ} (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s ↦ ‖toEuclideanLin (A * Φ (g s)) w‖ ^ 2)
      (2 * (⟪toEuclideanLin (A * Φ (g t)) w, toEuclideanLin (A * Φ g') w⟫_ℂ).re) t := by
  classical
  have := Fintype.ofFinite m
  have hv : HasDerivAt (fun s ↦ mulApplyCLM Φ A w (g s)) (mulApplyCLM Φ A w g') t :=
    ((mulApplyCLM Φ A w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hg
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hv.inner ℂ hv)
  convert hre using 1
  · funext s
    simp only [Function.comp_apply, Complex.reCLM_apply, mulApplyCLM_apply]
    rw [← RCLike.re_to_complex, ← @norm_sq_eq_re_inner ℂ]
  · simp only [Complex.reCLM_apply, mulApplyCLM_apply, Complex.add_re]
    rw [← inner_conj_symm (toEuclideanLin (A * Φ g') w), Complex.conj_re]
    ring

end Calculus

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- **Descending trace identity for a variation of one filter.** Let `ψ = A (L ⊗ 1) C w`, where
`A` is the product of a descending chain for `ψ` on regions containing `D` and `L` is invertible.
Then `⟪ψ, A (M ⊗ 1) C w⟫ = Tr (ρ_{ψ,D} M L⁻¹)` for every `M` on `D`.
PEPS manuscript, `03-patches.tex`, lines 138–160, `eq:patch-trace-stripping`. -/
theorem inner_mulLocalLift_eq_trace {D : Finset V}
    {L : Matrix (RegionConfig n D) (RegionConfig n D) ℂ} (hL : IsUnit L.det)
    {outer : List (RegionFilter n)} (C : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (w : EuclideanSpace ℂ (SiteConfig n)) (σ₀ : SiteConfig n)
    (hchain : IsDescendingChain (toEuclideanLin (liftProd outer * localLift D L * C) w) outer)
    (hsub : ∀ p ∈ outer, D ⊆ p.1) (M : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    ⟪toEuclideanLin (liftProd outer * localLift D L * C) w,
        toEuclideanLin (liftProd outer * localLift D M * C) w⟫_ℂ =
      (regionState D (toEuclideanLin (liftProd outer * localLift D L * C) w) *
        (M * L⁻¹)).trace := by
  have hM : localLift D M = localLift D (M * L⁻¹) * localLift D L := by
    rw [← localLift_mul, Matrix.mul_assoc, nonsing_inv_mul _ hL, Matrix.mul_one]
  have hvec : toEuclideanLin (liftProd outer * localLift D M * C) w =
      toEuclideanLin (liftProd outer * localLift D (M * L⁻¹) * liftProdInv outer)
        (toEuclideanLin (liftProd outer * localLift D L * C) w) := by
    rw [hM, ← toEuclideanLin_mul_apply', show liftProd outer * localLift D (M * L⁻¹) *
        liftProdInv outer * (liftProd outer * localLift D L * C) =
        liftProd outer * localLift D (M * L⁻¹) * (liftProdInv outer * liftProd outer) *
          localLift D L * C by simp only [Matrix.mul_assoc],
      liftProdInv_mul_liftProd hchain, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  have hY : ∀ p ∈ outer, IsSupportedOn (localLift D (M * L⁻¹)) p.1 := fun p hp ↦
    (isSupportedOn_localLift _).mono (hsub p hp)
  rw [hvec, inner_liftProd_conj σ₀ hchain hY, inner_localLift]

/-- **Commutation for one factor of the patch objective.** If the density `x` minimizes
`‖A ((x + b 1)^{-a/2} ⊗ 1) C w‖` among density matrices on `D`, with `A` a descending chain for
the output on regions containing `D`, then the filter and `x` commute with the regional state of
the output.
PEPS manuscript, `03-patches.tex`, lines 130–168, `eq:patch-stationarity-commutation`. -/
theorem patchFilter_commute_regionState {D : Finset V}
    {x : Matrix (RegionConfig n D) (RegionConfig n D) ℂ} (hx : x.PosSemidef) (hxt : x.trace = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {outer : List (RegionFilter n)} (C : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (w : EuclideanSpace ℂ (SiteConfig n)) (σ₀ : SiteConfig n)
    (hmin : ∀ y : Matrix (RegionConfig n D) (RegionConfig n D) ℂ, y.PosSemidef → y.trace = 1 →
      ‖toEuclideanLin (liftProd outer * localLift D ((x + b • 1) ^ (-a / 2)) * C) w‖ ≤
        ‖toEuclideanLin (liftProd outer * localLift D ((y + b • 1) ^ (-a / 2)) * C) w‖)
    (hchain : IsDescendingChain
      (toEuclideanLin (liftProd outer * localLift D ((x + b • 1) ^ (-a / 2)) * C) w) outer)
    (hsub : ∀ p ∈ outer, D ⊆ p.1) :
    Commute ((x + b • 1) ^ (-a / 2))
        (regionState D (toEuclideanLin (liftProd outer *
          localLift D ((x + b • 1) ^ (-a / 2)) * C) w)) ∧
      Commute x (regionState D (toEuclideanLin (liftProd outer *
          localLift D ((x + b • 1) ^ (-a / 2)) * C) w)) := by
  set K := x + b • (1 : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) with hKdef
  have hK : K.PosDef := hx.add_smul_one_posDef hb
  have hL : (K ^ (-a / 2)).PosDef :=
    Matrix.isStrictlyPositive_iff_posDef.mp
      (IsStrictlyPositive.rpow K (-a / 2) hK.isStrictlyPositive)
  have hc : K ^ (-a / 2) * regionState D (toEuclideanLin (liftProd outer *
      localLift D (K ^ (-a / 2)) * C) w) = regionState D (toEuclideanLin (liftProd outer *
      localLift D (K ^ (-a / 2)) * C) w) * K ^ (-a / 2) := by
    refine commute_regionState_of_unitary_min hL C w σ₀ (fun U hU ↦ ?_) hchain hsub
    have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
    have hUu : U ∈ unitary (Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :=
      Unitary.mem_iff.mpr
        ⟨by simpa [star_eq_conjTranspose] using hU, by simpa [star_eq_conjTranspose] using hU'⟩
    have hconj := rpow_conj_unitary hK.posSemidef (-a / 2) ⟨U, hUu⟩
    simp only [star_eq_conjTranspose] at hconj
    have hUK : U * K * Uᴴ = U * x * Uᴴ + b • (1 : Matrix _ _ ℂ) := by
      rw [hKdef, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hU']
    rw [← hconj, hUK]
    refine hmin _ (hx.mul_mul_conjTranspose_same U) ?_
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, hxt]
  refine ⟨hc, ?_⟩
  exact (hx.commute_of_commute_shifted_inverse_power ha hb hc.symm).symm

/-- **One-sided first-order condition for one factor of the patch objective.** Under the
minimality of `patchFilter_commute_regionState`, every density matrix `y` commuting with `x`
satisfies `Re Tr (G y) ≤ Re Tr (G x)` with `G = ρ (x + b 1)^{-1}`.
PEPS manuscript, `03-patches.tex`, lines 170–178, `eq:patch-simplex-derivative`. -/
theorem re_trace_variation_le_of_patch_min {D : Finset V}
    {x : Matrix (RegionConfig n D) (RegionConfig n D) ℂ} (hx : x.PosSemidef) (hxt : x.trace = 1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {outer : List (RegionFilter n)} (C : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (w : EuclideanSpace ℂ (SiteConfig n)) (σ₀ : SiteConfig n)
    (hmin : ∀ y : Matrix (RegionConfig n D) (RegionConfig n D) ℂ, y.PosSemidef → y.trace = 1 →
      ‖toEuclideanLin (liftProd outer * localLift D ((x + b • 1) ^ (-a / 2)) * C) w‖ ≤
        ‖toEuclideanLin (liftProd outer * localLift D ((y + b • 1) ^ (-a / 2)) * C) w‖)
    (hchain : IsDescendingChain
      (toEuclideanLin (liftProd outer * localLift D ((x + b • 1) ^ (-a / 2)) * C) w) outer)
    (hsub : ∀ p ∈ outer, D ⊆ p.1)
    (y : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) (hy : y.PosSemidef) (hyt : y.trace = 1)
    (hxy : Commute x y) :
    (regionState D (toEuclideanLin (liftProd outer * localLift D ((x + b • 1) ^ (-a / 2)) * C) w) *
        (x + b • 1) ^ (-1 : ℝ) * y).trace.re ≤
      (regionState D (toEuclideanLin (liftProd outer *
          localLift D ((x + b • 1) ^ (-a / 2)) * C) w) * (x + b • 1) ^ (-1 : ℝ) * x).trace.re := by
  set K := x + b • (1 : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) with hKdef
  set r : ℝ := -a / 2 with hr
  have hr0 : r < 0 := by rw [hr]; linarith
  have hK : K.PosDef := hx.add_smul_one_posDef hb
  set ψ := toEuclideanLin (liftProd outer * localLift D (K ^ r) * C) w with hψ
  set ρ := regionState D ψ with hρ
  set h := y - x with hhdef
  have hh : h.IsHermitian := hy.isHermitian.sub hx.isHermitian
  have hxh : x * h = h * x := by rw [hhdef, Matrix.mul_sub, Matrix.sub_mul, hxy.eq]
  have hg := hx.hasDerivAt_add_smul_add_smul_one_rpow_of_commute hh hxh hb r
  set Φ := (LinearMap.mulRight ℂ C) ∘ₗ localLiftₗ (n := n) D
  have hΦ : ∀ M, liftProd outer * Φ M = liftProd outer * localLift D M * C := fun M ↦ by
    simp [Φ, localLiftₗ, Matrix.mul_assoc]
  have hF := hasDerivAt_norm_sq_mulApply Φ (liftProd outer) w hg
  simp only [zero_smul, add_zero, hΦ] at hF
  -- the segment toward `y` stays among density matrices
  have hseg : IsMinOn (fun s : ℝ ↦ ‖toEuclideanLin (liftProd outer *
      Φ ((x + s • h + b • (1 : Matrix _ _ ℂ)) ^ r)) w‖ ^ 2) (Set.Icc 0 1) 0 := by
    refine isMinOn_iff.mpr fun s hs ↦ ?_
    simp only [hΦ, zero_smul, add_zero]
    have hxs : x + s • h = (1 - s) • x + s • y := by
      rw [hhdef, smul_sub, sub_smul, one_smul]; abel
    refine pow_le_pow_left₀ (norm_nonneg _) (hmin _ ?_ ?_) 2
    · rw [hxs]
      exact (hx.smul (sub_nonneg.mpr hs.2)).add (hy.smul hs.1)
    · rw [hxs, trace_add, trace_smul, trace_smul, hxt, hyt]
      simp
  have hseg01 : segment ℝ (0 : ℝ) 1 ⊆ Set.Icc 0 1 :=
    (convex_Icc (0 : ℝ) 1).segment_subset (Set.left_mem_Icc.mpr zero_le_one)
      (Set.right_mem_Icc.mpr zero_le_one)
  have hF' := hF
  rw [show (fun s : ℝ ↦ ‖toEuclideanLin (liftProd outer *
      localLift D ((x + s • h + b • (1 : Matrix _ _ ℂ)) ^ r) * C) w‖ ^ 2) =
      (fun s : ℝ ↦ ‖toEuclideanLin (liftProd outer *
        Φ ((x + s • h + b • (1 : Matrix _ _ ℂ)) ^ r)) w‖ ^ 2) by simp only [hΦ]] at hF'
  have h0 := hseg.isLocalMinOn.hasFDerivWithinAt_nonneg hF'.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset hseg01)
  simp only [sub_zero, ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h0
  -- strip the outer filters
  have hLu : IsUnit (K ^ r).det := (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.isStrictlyPositive_iff_posDef.mp
      (IsStrictlyPositive.rpow K r hK.isStrictlyPositive)).isUnit
  rw [inner_mulLocalLift_eq_trace hLu C w σ₀ hchain hsub] at h0
  have hLinv : (K ^ r)⁻¹ = K ^ (-r) :=
    Matrix.inv_eq_right_inv (CFC.rpow_mul_rpow_neg r hK.isStrictlyPositive)
  have hhK : Commute (K ^ (-r)) h :=
    (hx.commute_add_smul_one_rpow_iff hb (by rw [hr]; linarith : -r ≠ 0)).mpr hxh
  have hexp : K ^ (r - 1) * K ^ (-r) = K ^ (-1 : ℝ) := by
    rw [← CFC.rpow_add hK.isUnit]; congr 1; ring
  have hM : r • (K ^ (r - 1) * h) * (K ^ r)⁻¹ = r • (K ^ (-1 : ℝ) * h) := by
    rw [hLinv, Matrix.smul_mul, Matrix.mul_assoc, ← hhK.eq, ← Matrix.mul_assoc, hexp]
  rw [hM, Matrix.mul_smul, trace_smul, Complex.smul_re, smul_eq_mul, hhdef, Matrix.mul_sub,
    Matrix.mul_sub, trace_sub, Complex.sub_re] at h0
  simp only [← Matrix.mul_assoc] at h0
  nlinarith

/-- `IsDescendingChain` grows by a filter at the inner end. -/
theorem isDescendingChain_append_singleton {φ : EuclideanSpace ℂ (SiteConfig n)}
    {p : RegionFilter n} (hu : IsUnit p.2.det)
    (hc : p.2 * regionState p.1 φ = regionState p.1 φ * p.2) :
    ∀ {l : List (RegionFilter n)}, IsDescendingChain φ l → (∀ q ∈ l, p.1 ⊆ q.1) →
      IsDescendingChain φ (l ++ [p])
  | [], _, _ => ⟨hu, hc, by simp, trivial⟩
  | q :: l, ⟨hqu, hqc, hqs, hl⟩, hsub => by
    refine ⟨hqu, hqc, fun r hr ↦ ?_, isDescendingChain_append_singleton hu hc hl
      fun r hr ↦ hsub r (by simp [hr])⟩
    rcases List.mem_append.mp hr with h | h
    · exact hqs r h
    · rw [List.mem_singleton] at h
      subst h
      exact hsub q (by simp)

/-- A factor of the ordered patch objective: a region, a positive exponent, and a matrix on the
region. PEPS manuscript, `03-patches.tex`, `eq:patch-variational-problem`. -/
structure PatchFactor (n : V → ℕ) where
  /-- The region `X_j`. -/
  region : Finset V
  /-- The exponent `a_j`. -/
  exponent : ℝ
  /-- The variable `x_j`, a density matrix at feasible points. -/
  density : Matrix (RegionConfig n region) (RegionConfig n region) ℂ

/-- The regularized filter `L_j = (x_j + b 1)^{-a_j/2}` of a factor, as a regional filter. -/
noncomputable def PatchFactor.filter (b : ℝ) (f : PatchFactor n) : RegionFilter n :=
  ⟨f.region, (f.density + b • 1) ^ (-f.exponent / 2)⟩

/-- The output `L_m ⋯ L_1 Ω` of an ordered list of factors; the head of the list is applied
last. PEPS manuscript, `03-patches.tex`, `eq:patch-variational-problem`. -/
noncomputable def patchOutput (b : ℝ) (l : List (PatchFactor n))
    (Ω : EuclideanSpace ℂ (SiteConfig n)) : EuclideanSpace ℂ (SiteConfig n) :=
  toEuclideanLin (liftProd (l.map (PatchFactor.filter b))) Ω

/-- The normalized output `φ = L_m ⋯ L_1 Ω / ‖L_m ⋯ L_1 Ω‖` (zero if the output vanishes). -/
noncomputable def patchState (b : ℝ) (l : List (PatchFactor n))
    (Ω : EuclideanSpace ℂ (SiteConfig n)) : EuclideanSpace ℂ (SiteConfig n) :=
  ((‖patchOutput b l Ω‖⁻¹ : ℝ) : ℂ) • patchOutput b l Ω

/-- `l` minimizes the ordered patch objective among lists with the same regions and exponents
whose matrices are density matrices. PEPS manuscript, `03-patches.tex`,
`eq:patch-variational-problem`. -/
def IsPatchMinimizer (b : ℝ) (l : List (PatchFactor n)) (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    Prop :=
  ∀ l' : List (PatchFactor n), l'.map PatchFactor.region = l.map PatchFactor.region →
    l'.map PatchFactor.exponent = l.map PatchFactor.exponent →
    (∀ f ∈ l', f.density.PosSemidef ∧ f.density.trace = 1) →
    ‖patchOutput b l Ω‖ ≤ ‖patchOutput b l' Ω‖

theorem patchOutput_append_cons (b : ℝ) (pre post : List (PatchFactor n)) (f : PatchFactor n)
    (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    patchOutput b (pre ++ f :: post) Ω =
      toEuclideanLin (liftProd (pre.map (PatchFactor.filter b)) *
        localLift f.region ((f.density + b • 1) ^ (-f.exponent / 2)) *
          liftProd (post.map (PatchFactor.filter b))) Ω := by
  rw [patchOutput, List.map_append, List.map_cons, liftProd_append, liftProd_cons,
    Matrix.mul_assoc]
  rfl

/-- Minimality of the whole list gives minimality in each coordinate. -/
theorem IsPatchMinimizer.coord {b : ℝ} {pre post : List (PatchFactor n)} {f : PatchFactor n}
    {Ω : EuclideanSpace ℂ (SiteConfig n)} (hmin : IsPatchMinimizer b (pre ++ f :: post) Ω)
    (hden : ∀ g ∈ pre ++ f :: post, g.density.PosSemidef ∧ g.density.trace = 1)
    (y : Matrix (RegionConfig n f.region) (RegionConfig n f.region) ℂ) (hy : y.PosSemidef)
    (hyt : y.trace = 1) :
    ‖patchOutput b (pre ++ f :: post) Ω‖ ≤
      ‖patchOutput b (pre ++ ⟨f.region, f.exponent, y⟩ :: post) Ω‖ := by
  refine hmin _ (by simp) (by simp) fun g hg ↦ ?_
  rcases List.mem_append.mp hg with h | h
  · exact hden g (List.mem_append_left _ h)
  · rcases List.mem_cons.mp h with h | h
    · subst h; exact ⟨hy, hyt⟩
    · exact hden g (List.mem_append_right _ (List.mem_cons_of_mem _ h))

/-- **Stationarity of one factor of a patch minimizer**, for the unnormalized output `ψ`: if the
outer factors form a descending chain for `ψ`, then the factor's filter and density commute with
`ρ = ρ_{ψ, X}`, and `ρ ≤ ‖ψ‖² (x + b 1)`.
PEPS manuscript, `03-patches.tex`, lines 130–205. -/
theorem patchFactor_stationary {b : ℝ} (hb : 0 < b) {pre post : List (PatchFactor n)}
    {f : PatchFactor n} {Ω : EuclideanSpace ℂ (SiteConfig n)} (σ₀ : SiteConfig n)
    (hexp : 0 < f.exponent)
    (hden : ∀ g ∈ pre ++ f :: post, g.density.PosSemidef ∧ g.density.trace = 1)
    (hnest : (pre ++ f :: post).Pairwise fun g g' ↦ g'.region ⊆ g.region)
    (hmin : IsPatchMinimizer b (pre ++ f :: post) Ω)
    (hchain : IsDescendingChain (patchOutput b (pre ++ f :: post) Ω)
      (pre.map (PatchFactor.filter b))) :
    Commute ((f.density + b • 1) ^ (-f.exponent / 2))
        (regionState f.region (patchOutput b (pre ++ f :: post) Ω)) ∧
      Commute f.density (regionState f.region (patchOutput b (pre ++ f :: post) Ω)) ∧
      regionState f.region (patchOutput b (pre ++ f :: post) Ω) ≤
        (‖patchOutput b (pre ++ f :: post) Ω‖ ^ 2) • (f.density + b • 1) := by
  obtain ⟨hx, hxt⟩ := hden f (by simp)
  have hsub : ∀ p ∈ pre.map (PatchFactor.filter b), f.region ⊆ p.1 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (List.pairwise_append.mp hnest).2.2 q hq f (by simp)
  have hmin' : ∀ y : Matrix (RegionConfig n f.region) (RegionConfig n f.region) ℂ,
      y.PosSemidef → y.trace = 1 →
      ‖toEuclideanLin (liftProd (pre.map (PatchFactor.filter b)) *
          localLift f.region ((f.density + b • 1) ^ (-f.exponent / 2)) *
            liftProd (post.map (PatchFactor.filter b))) Ω‖ ≤
        ‖toEuclideanLin (liftProd (pre.map (PatchFactor.filter b)) *
          localLift f.region ((y + b • 1) ^ (-f.exponent / 2)) *
            liftProd (post.map (PatchFactor.filter b))) Ω‖ := by
    intro y hy hyt
    have h := hmin.coord hden y hy hyt
    rwa [patchOutput_append_cons, patchOutput_append_cons] at h
  rw [patchOutput_append_cons] at hchain ⊢
  obtain ⟨hcL, hcx⟩ := patchFilter_commute_regionState hx hxt hexp hb _ Ω σ₀ hmin' hchain hsub
  refine ⟨hcL, hcx, ?_⟩
  have hvar := re_trace_variation_le_of_patch_min hx hxt hexp hb _ Ω σ₀ hmin' hchain hsub
  have h := hx.le_trace_smul_add_smul_one_of_forall_density (regionState_posSemidef _ _) hcx hb
    fun y hy hyt hxy ↦ hvar y hy hyt hxy
  rwa [trace_regionState, Complex.ofReal_re] at h

/-- Along a patch minimizer with nested regions, every initial segment of the list is a
descending chain for the output. PEPS manuscript, `03-patches.tex`, lines 130–168: the
induction in decreasing order of `j`. -/
theorem isDescendingChain_of_patch_min {b : ℝ} (hb : 0 < b) {l : List (PatchFactor n)}
    {Ω : EuclideanSpace ℂ (SiteConfig n)} (σ₀ : SiteConfig n)
    (hexp : ∀ f ∈ l, 0 < f.exponent)
    (hden : ∀ f ∈ l, f.density.PosSemidef ∧ f.density.trace = 1)
    (hnest : l.Pairwise fun g g' ↦ g'.region ⊆ g.region)
    (hmin : IsPatchMinimizer b l Ω) :
    ∀ pre rest, l = pre ++ rest →
      IsDescendingChain (patchOutput b l Ω) (pre.map (PatchFactor.filter b)) := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil => intro _ _; trivial
  | append_singleton pre f ih =>
    intro rest hl
    have hl' : l = pre ++ f :: rest := by simpa using hl
    have hc := ih (f :: rest) hl'
    subst hl'
    have hst := patchFactor_stationary hb σ₀ (hexp f (by simp)) hden hnest hmin hc
    obtain ⟨hx, -⟩ := hden f (by simp)
    have hL : (f.density + b • 1) ^ (-f.exponent / 2) |>.PosDef :=
      Matrix.isStrictlyPositive_iff_posDef.mp (IsStrictlyPositive.rpow _ _
        (hx.add_smul_one_posDef hb).isStrictlyPositive)
    rw [List.map_append, List.map_singleton]
    refine isDescendingChain_append_singleton ((Matrix.isUnit_iff_isUnit_det _).mp hL.isUnit)
      hst.1.eq hc fun q hq ↦ ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hq
    exact (List.pairwise_append.mp hnest).2.2 g hg f (by simp)

/-- **Stationarity of the ordered patch objective.** Let `l = [f_m, …, f_1]` list factors with
nested regions `X_1 ⊆ ⋯ ⊆ X_m`, positive exponents and density matrices `x_j`, and let `l`
minimize `‖L_m ⋯ L_1 Ω‖` over the densities, `L_j = (x_j + b 1)^{-a_j/2}`. Then the regional
state `ρ_j` of the normalized output on `X_j` satisfies `[x_j, ρ_j] = 0` and
`ρ_j ≤ x_j + b 1` for every `j`.
PEPS manuscript, `03-patches.tex`, lines 130–205, `eq:patch-stationarity-commutation`,
`eq:patch-kkt`, `eq:patch-clipped-eigenvalues`. -/
theorem patch_stationarity {b : ℝ} (hb : 0 < b) {l : List (PatchFactor n)}
    {Ω : EuclideanSpace ℂ (SiteConfig n)}
    (hexp : ∀ f ∈ l, 0 < f.exponent)
    (hden : ∀ f ∈ l, f.density.PosSemidef ∧ f.density.trace = 1)
    (hnest : l.Pairwise fun g g' ↦ g'.region ⊆ g.region)
    (hmin : IsPatchMinimizer b l Ω) :
    ∀ f ∈ l, Commute f.density (regionState f.region (patchState b l Ω)) ∧
      regionState f.region (patchState b l Ω) ≤ f.density + b • 1 := by
  intro f hf
  obtain ⟨hx, -⟩ := hden f hf
  have hK := hx.add_smul_one_posDef hb
  by_cases hne : Nonempty (SiteConfig n)
  swap
  · have : Subsingleton (EuclideanSpace ℂ (SiteConfig n)) := by
      rw [not_nonempty_iff] at hne
      infer_instance
    have h0 : regionState f.region (patchState b l Ω) = 0 := by
      rw [Subsingleton.elim (patchState b l Ω) ((0 : ℂ) • patchState b l Ω), regionState_smul]
      simp
    rw [h0]
    exact ⟨Commute.zero_right _, Matrix.le_iff.mpr (by simpa using hK.posSemidef)⟩
  obtain ⟨σ₀⟩ := hne
  obtain ⟨pre, post, hl⟩ := List.append_of_mem hf
  have hc := isDescendingChain_of_patch_min hb σ₀ hexp hden hnest hmin pre (f :: post) hl
  subst hl
  obtain ⟨-, hcx, hle⟩ := patchFactor_stationary hb σ₀ (hexp f hf) hden hnest hmin hc
  set ψ := patchOutput b (pre ++ f :: post) Ω
  have hst : regionState f.region (patchState b (pre ++ f :: post) Ω) =
      (‖ψ‖⁻¹ ^ 2) • regionState f.region ψ := by
    rw [patchState, regionState_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), Complex.coe_smul]
  rw [hst]
  refine ⟨hcx.smul_right _, ?_⟩
  have hc1 : ‖ψ‖⁻¹ ^ 2 * ‖ψ‖ ^ 2 ≤ 1 := by
    rcases eq_or_ne ‖ψ‖ 0 with h | h
    · simp [h]
    · rw [← mul_pow, inv_mul_cancel₀ h, one_pow]
  rw [Matrix.le_iff] at hle ⊢
  have h := (hle.smul (sq_nonneg ‖ψ‖⁻¹)).add (hK.posSemidef.smul (sub_nonneg.mpr hc1))
  convert h using 1
  module

/-- **The regulator bounds at a patch minimizer.** At every minimizer of the ordered patch
objective, `T_j = b ρ_j (x_j + b 1)^{-1}` satisfies `0 ≤ T_j ≤ b 1` and `T_j ≤ ρ_j`.
PEPS manuscript, `03-patches.tex`, lines 130–205 and 390–400. -/
theorem patch_shiftedRegulator_bounds {b : ℝ} (hb : 0 < b) {l : List (PatchFactor n)}
    {Ω : EuclideanSpace ℂ (SiteConfig n)}
    (hexp : ∀ f ∈ l, 0 < f.exponent)
    (hden : ∀ f ∈ l, f.density.PosSemidef ∧ f.density.trace = 1)
    (hnest : l.Pairwise fun g g' ↦ g'.region ⊆ g.region)
    (hmin : IsPatchMinimizer b l Ω) (f : PatchFactor n) (hf : f ∈ l) :
    (b • (regionState f.region (patchState b l Ω) * (f.density + b • 1)⁻¹)).PosSemidef ∧
      b • (regionState f.region (patchState b l Ω) * (f.density + b • 1)⁻¹) ≤ b • 1 ∧
      b • (regionState f.region (patchState b l Ω) * (f.density + b • 1)⁻¹) ≤
        regionState f.region (patchState b l Ω) := by
  obtain ⟨hc, hle⟩ := patch_stationarity hb hexp hden hnest hmin f hf
  exact (hden f hf).1.shiftedRegulator_bounds (regionState_posSemidef _ _) hb hc.symm hle

end Entropy
