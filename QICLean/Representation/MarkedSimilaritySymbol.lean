/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSimilarity
import QICLean.Representation.RegionPowerSymbol
import QICLean.Representation.StarFunction
import QICLean.Representation.CoherentSymbolLimit
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# The coherent symbol of the similarity transform

Let `V = ⨂_v ℂ^{n_v}`, let `P, Y, F` be disjoint subsystems, `0 < t < 1/2`, and let `h` be a
one-copy operator supported on `P ∪ Y`. Lemma 6.4 of the area-law paper (*A two-dimensional
area law from a global spectral gap*, `05-replicas.tex`, lines 615–638 and 663–836) shows that
`O_k = A_k^{-1/2} hbar A_k^{1/2}` has, on the symmetric subspace, the scalar symbol

`f_θ = ⟨θ, ρ_P^t ρ_Y^{-t} h ρ_P^{-t} ρ_Y^t θ⟩`.

The proof replaces the marked ratios by polynomials in star operators (lines 693–708),
computes the symbols of these polynomial words (lines 776–812), and removes the clipping on the
one-copy side (lines 813–826). This file assembles these steps into
`TensorPower.hasCoherentSymbol_markedSimilarity`, and deduces equation
`replicas:polynomial-symbol` for every noncommutative polynomial in `O_k, O_k^†`.

## Main declarations

* `TensorPower.norm_sandwich_approx_le`, `TensorPower.norm_pairing_approx_le` — the
  perturbation estimates.
* `TensorPower.hasCoherentSymbol_markedSimilarity` — `O_k` has coherent symbol `f_θ`.
* `TensorPower.eventually_norm_trace_freeAlgebra_markedSimilarity_sub_le` — equation
  `replicas:polynomial-symbol`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 6.4 (`lem:symbol`), section file `05-replicas.tex`, lines 615–638 and 663–836.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation Polynomial Filter Entropy
open scoped Matrix.Norms.L2Operator

namespace TensorPower

/-! ### Perturbation estimates -/

section Perturbation

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **A sandwiched vector under perturbation**: if `‖R - P‖ ≤ e_R`, `‖R⁻¹ z‖ ≤ C_I ‖z‖`,
`‖(R⁻¹ - Q) z‖ ≤ e_I ‖z‖` and `‖P‖ ≤ C_P`, then
`‖R a R⁻¹ z - P a Q z‖ ≤ ‖a‖ (e_R C_I + C_P e_I) ‖z‖`. -/
theorem norm_sandwich_approx_le (R Ri P Q a : Matrix X X ℂ) (z : X → ℂ) {eR eI CI CP : ℝ}
    (hR : ‖R - P‖ ≤ eR) (hRi : ‖(EuclideanSpace.equiv X ℂ).symm (Ri *ᵥ z)‖ ≤
      CI * ‖(EuclideanSpace.equiv X ℂ).symm z‖)
    (hI : ‖(EuclideanSpace.equiv X ℂ).symm (Ri *ᵥ z - Q *ᵥ z)‖ ≤
      eI * ‖(EuclideanSpace.equiv X ℂ).symm z‖) (hP : ‖P‖ ≤ CP) :
    ‖(EuclideanSpace.equiv X ℂ).symm (R *ᵥ (a *ᵥ (Ri *ᵥ z)) - P *ᵥ (a *ᵥ (Q *ᵥ z)))‖ ≤
      ‖a‖ * (eR * CI + CP * eI) * ‖(EuclideanSpace.equiv X ℂ).symm z‖ := by
  refine (norm_sandwich_sub_le R P a _ _).trans ?_
  have hz := norm_nonneg ((EuclideanSpace.equiv X ℂ).symm z)
  have ha := norm_nonneg a
  calc ‖R - P‖ * ‖a‖ * ‖(EuclideanSpace.equiv X ℂ).symm (Ri *ᵥ z)‖ +
        ‖P‖ * ‖a‖ * ‖(EuclideanSpace.equiv X ℂ).symm (Ri *ᵥ z - Q *ᵥ z)‖
      ≤ eR * ‖a‖ * (CI * ‖(EuclideanSpace.equiv X ℂ).symm z‖) +
        CP * ‖a‖ * (eI * ‖(EuclideanSpace.equiv X ℂ).symm z‖) := by
        have heR : 0 ≤ eR := (norm_nonneg _).trans hR
        have hCP : 0 ≤ CP := (norm_nonneg _).trans hP
        gcongr
    _ = _ := by ring

omit [DecidableEq X] in
/-- **A pairing under perturbation**: `|⟨y, x⟩ - ⟨y', x'⟩| ≤ e_y M_x + M_y e_x` when
`‖y - y'‖ ≤ e_y`, `‖x‖ ≤ M_x`, `‖y'‖ ≤ M_y` and `‖x - x'‖ ≤ e_x`. -/
theorem norm_pairing_approx_le (x x' y y' : X → ℂ) {ex ey Mx My : ℝ}
    (hx : ‖(EuclideanSpace.equiv X ℂ).symm (x - x')‖ ≤ ex)
    (hMx : ‖(EuclideanSpace.equiv X ℂ).symm x‖ ≤ Mx)
    (hy : ‖(EuclideanSpace.equiv X ℂ).symm (y - y')‖ ≤ ey)
    (hMy : ‖(EuclideanSpace.equiv X ℂ).symm y'‖ ≤ My) :
    ‖star y ⬝ᵥ x - star y' ⬝ᵥ x'‖ ≤ ey * Mx + My * ex := by
  refine (norm_star_dotProduct_sub_le x x' y y').trans ?_
  gcongr
  · exact (norm_nonneg _).trans hy
  · exact (norm_nonneg _).trans hMy

end Perturbation

/-- For `r > 0` and `s > 0` there is `δ ∈ (0, 1)` with `δ^r ≤ s`. -/
theorem exists_rpow_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ^ r ≤ s := by
  have h : Tendsto (fun δ : ℝ => δ ^ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have := (Real.continuousAt_rpow_const 0 r (Or.inr hr.le)).tendsto
    rw [Real.zero_rpow hr.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi 0), δ ^ r ≤ s ∧ 0 < δ ∧ δ < 1 :=
    (h.eventually (ge_mem_nhds hs)).and (Filter.eventually_of_mem self_mem_nhdsWithin
      (fun x hx => hx) |>.and (Filter.eventually_of_mem
        (inter_mem_nhdsWithin _ (Iio_mem_nhds one_pos)) fun x hx => hx.2))
  obtain ⟨δ, h1, h2, h3⟩ := hev.exists
  exact ⟨δ, h2, h3, h1⟩

/-! ### The polynomial words and their symbols -/

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- The commutation pattern `P^t Y^{-t} (b a) P^{-t} Y^t = (Y^{-t} b Y^t)(P^t a P^{-t})`
(`05-replicas.tex`, lines 668–683). -/
theorem sandwich_rearrange {X : Type*} [Fintype X] [DecidableEq X]
    {Pt Pm Yt Ym b a : Matrix X X ℂ} (h1 : Commute Pt Ym) (h2 : Commute Pt b)
    (h3 : Commute Yt Pm) (h4 : Commute Yt a) (h5 : Commute Pt Yt) :
    Pt * Ym * (b * a) * Pm * Yt = (Ym * b * Yt) * (Pt * a * Pm) := by
  calc Pt * Ym * (b * a) * Pm * Yt = (Pt * Ym * b) * (a * Pm * Yt) := by
        simp only [Matrix.mul_assoc]
    _ = (Ym * b * Pt) * (Yt * a * Pm) := by
        congr 1
        · rw [h1.eq, Matrix.mul_assoc, h2.eq, ← Matrix.mul_assoc]
        · rw [Matrix.mul_assoc, ← h3.eq, ← Matrix.mul_assoc, ← h4.eq, Matrix.mul_assoc]
    _ = Ym * b * (Pt * Yt) * a * Pm := by simp only [Matrix.mul_assoc]
    _ = Ym * b * (Yt * Pt) * a * Pm := by rw [h5.eq]
    _ = (Ym * b * Yt) * (Pt * a * Pm) := by simp only [Matrix.mul_assoc]

/-- `⟨θ, A B θ⟩ = ⟨Aᴴ θ, B θ⟩`. -/
theorem star_dotProduct_mul_mulVec {X : Type*} [Fintype X] (A B : Matrix X X ℂ) (θ : X → ℂ) :
    star θ ⬝ᵥ ((A * B) *ᵥ θ) = star (Aᴴ *ᵥ θ) ⬝ᵥ (B *ᵥ θ) := by
  rw [← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

/-- The one-copy symbol of the polynomial word: `∑_i (q(ρ_Y) b_i p(ρ_Y))(p(ρ_P) a_i q(ρ_P))`. -/
noncomputable def polyWordSymbol (P Y : Finset V) {N : ℕ}
    (a b : Fin N → Matrix (SiteConfig n) (SiteConfig n) ℂ) (p q : ℝ[X])
    (θ : SiteConfig n → ℂ) : Matrix (SiteConfig n) (SiteConfig n) ℂ :=
  ∑ i, (aeval (margLift Y θ) q * b i * aeval (margLift Y θ) p) *
    (aeval (margLift P θ) p * a i * aeval (margLift P θ) q)

/-- **Removing the clipping on the one-copy side** (`05-replicas.tex`, lines 813–826): if
`|p - u_+^t| ≤ s` and `|q - max(u, δ)^{-t}| ≤ s` on `[-1, 1]` and `√(d_Q δ^{1-2t}) ≤ s` for
`Q = P, Y`, then `|f_θ - ⟨θ, F(θ) θ⟩| ≤ s K ∑_i ‖a_i‖ ‖b_i‖` on unit vectors, where `F` is the
symbol of the polynomial word. -/
theorem norm_markedScalarSymbol_sub_le [∀ v, NeZero (n v)] {t δ s : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2)
    (hδ : 0 < δ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {P Y : Finset V} (hPY : Disjoint P Y)
    {h : Matrix (SiteConfig n) (SiteConfig n) ℂ} {N : ℕ}
    {a b : Fin N → Matrix (SiteConfig n) (SiteConfig n) ℂ} (ha : ∀ i, IsSupportedOn (a i) P)
    (hb : ∀ i, IsSupportedOn (b i) Y) (hdec : h = ∑ i, b i * a i) {p q : ℝ[X]}
    (hp : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |max x 0 ^ t - p.eval x| ≤ s)
    (hq : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |max x δ ^ (-t) - q.eval x| ≤ s)
    (hdP : √((Fintype.card (RegionConfig n P) : ℝ) * δ ^ (1 - 2 * t)) ≤ s)
    (hdY : √((Fintype.card (RegionConfig n Y) : ℝ) * δ ^ (1 - 2 * t)) ≤ s)
    {θ : SiteConfig n → ℂ} (hθ : θ ∈ unitSphere) :
    ‖markedScalarSymbol t P Y h θ - star θ ⬝ᵥ (polyWordSymbol P Y a b p q θ *ᵥ θ)‖ ≤
      s * ((√(Fintype.card (RegionConfig n Y) : ℝ) + 4) *
          √(Fintype.card (RegionConfig n P) : ℝ) +
        (2 * √(Fintype.card (RegionConfig n Y) : ℝ) + 4) *
          (√(Fintype.card (RegionConfig n P) : ℝ) + 4)) * ∑ i, ‖a i‖ * ‖b i‖ := by
  set dP := √(Fintype.card (RegionConfig n P) : ℝ)
  set dY := √(Fintype.card (RegionConfig n Y) : ℝ)
  have σ₀ : SiteConfig n := fun _ => 0
  set Pt := regionPow P t θ
  set Pm := regionPow P (-t) θ
  set Yt := regionPow Y t θ
  set Ym := regionPow Y (-t) θ
  set pP := aeval (margLift P θ) p
  set qP := aeval (margLift P θ) q
  set pY := aeval (margLift Y θ) p
  set qY := aeval (margLift Y θ) q
  -- The symbol as a sum of pairings.
  have hf : markedScalarSymbol t P Y h θ = ∑ i, star (Yt *ᵥ ((b i)ᴴ *ᵥ (Ym *ᵥ θ))) ⬝ᵥ
      (Pt *ᵥ (a i *ᵥ (Pm *ᵥ θ))) := by
    rw [markedScalarSymbol, hdec, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, sum_mulVec,
      dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have c1 : Commute Pt Ym := commute_localLift_of_disjoint hPY _ _
    have c2 : Commute Pt (b i) := commute_localLift_of_isSupportedOn hPY _ (hb i) σ₀
    have c3 : Commute Yt Pm := commute_localLift_of_disjoint hPY.symm _ _
    have c4 : Commute Yt (a i) := commute_localLift_of_isSupportedOn hPY.symm _ (ha i) σ₀
    have c5 : Commute Pt Yt := commute_localLift_of_disjoint hPY _ _
    rw [sandwich_rearrange c1 c2 c3 c4 c5, star_dotProduct_mul_mulVec, conjTranspose_mul,
      conjTranspose_mul, (isHermitian_regionPow Y t θ).eq, (isHermitian_regionPow Y (-t) θ).eq]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
    rfl
  have hψ : star θ ⬝ᵥ (polyWordSymbol P Y a b p q θ *ᵥ θ) = ∑ i,
      star (pY *ᵥ ((b i)ᴴ *ᵥ (qY *ᵥ θ))) ⬝ᵥ (pP *ᵥ (a i *ᵥ (qP *ᵥ θ))) := by
    rw [polyWordSymbol, sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_dotProduct_mul_mulVec, conjTranspose_mul, conjTranspose_mul,
      (isHermitian_aeval_margLift Y θ p).eq, (isHermitian_aeval_margLift Y θ q).eq]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
    rfl
  have hmv : ∀ (M : Matrix (SiteConfig n) (SiteConfig n) ℂ) (v : SiteConfig n → ℂ),
      ‖(EuclideanSpace.equiv _ ℂ).symm (M *ᵥ v)‖ ≤ ‖M‖ * ‖(EuclideanSpace.equiv _ ℂ).symm v‖ :=
    fun M v => by simpa using M.l2_opNorm_mulVec ((EuclideanSpace.equiv _ ℂ).symm v)
  -- Bounds for one sandwiched vector.
  have hsand : ∀ (Q : Finset V) (c : Matrix (SiteConfig n) (SiteConfig n) ℂ),
      √((Fintype.card (RegionConfig n Q) : ℝ) * δ ^ (1 - 2 * t)) ≤ s →
      ‖(EuclideanSpace.equiv _ ℂ).symm (regionPow Q t θ *ᵥ (c *ᵥ (regionPow Q (-t) θ *ᵥ θ)) -
          aeval (margLift Q θ) p *ᵥ (c *ᵥ (aeval (margLift Q θ) q *ᵥ θ)))‖ ≤
        s * ‖c‖ * (√(Fintype.card (RegionConfig n Q) : ℝ) + 4) ∧
      ‖(EuclideanSpace.equiv _ ℂ).symm (regionPow Q t θ *ᵥ (c *ᵥ (regionPow Q (-t) θ *ᵥ θ)))‖ ≤
        ‖c‖ * √(Fintype.card (RegionConfig n Q) : ℝ) := by
    intro Q c hd
    have hdn : 0 ≤ √(Fintype.card (RegionConfig n Q) : ℝ) := Real.sqrt_nonneg _
    have hc := norm_nonneg c
    refine ⟨(norm_regionPow_sandwich_sub_le ht0 ht1 hδ hs0 Q hθ c hp hq).trans ?_, ?_⟩
    · have h1 : (1 + s) * (√((Fintype.card (RegionConfig n Q) : ℝ) * δ ^ (1 - 2 * t)) + s) ≤
          2 * (s + s) := by
        gcongr
        · linarith
      nlinarith [mul_nonneg hc hs0, mul_nonneg (mul_nonneg hc hs0) hdn]
    · refine (hmv _ _).trans ?_
      refine (mul_le_mul (l2_opNorm_regionPow_le_one ht0 Q hθ) ((hmv _ _).trans
        (mul_le_mul_of_nonneg_left (norm_regionPow_neg_mulVec_le ht1 Q hθ) hc))
        (by positivity) zero_le_one).trans ?_
      rw [one_mul]
  rw [hf, hψ, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  obtain ⟨hxP, hMxP⟩ := hsand P (a i) hdP
  obtain ⟨hyY, hMyY⟩ := hsand Y (b i)ᴴ hdY
  rw [l2_opNorm_conjTranspose] at hyY hMyY
  have hMy' : ‖(EuclideanSpace.equiv _ ℂ).symm (pY *ᵥ ((b i)ᴴ *ᵥ (qY *ᵥ θ)))‖ ≤
      ‖b i‖ * (2 * dY + 4) := by
    have hsplit : pY *ᵥ ((b i)ᴴ *ᵥ (qY *ᵥ θ)) = Yt *ᵥ ((b i)ᴴ *ᵥ (Ym *ᵥ θ)) -
        (Yt *ᵥ ((b i)ᴴ *ᵥ (Ym *ᵥ θ)) - pY *ᵥ ((b i)ᴴ *ᵥ (qY *ᵥ θ))) := by abel
    rw [hsplit, map_sub]
    have hb0 := norm_nonneg (b i)
    have hdY0 : 0 ≤ dY := Real.sqrt_nonneg _
    calc _ ≤ ‖b i‖ * dY + s * ‖b i‖ * (dY + 4) := (norm_sub_le _ _).trans (add_le_add hMyY hyY)
      _ ≤ ‖b i‖ * dY + 1 * ‖b i‖ * (dY + 4) := by gcongr
      _ = ‖b i‖ * (2 * dY + 4) := by ring
  refine (norm_pairing_approx_le _ _ _ _ hxP hMxP hyY hMy').trans ?_
  have := mul_nonneg (norm_nonneg (a i)) (norm_nonneg (b i))
  apply le_of_eq
  ring

end TensorPower
