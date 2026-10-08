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
open scoped Matrix.Norms.L2Operator ComplexOrder

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
theorem sandwich_rearrange {X : Type*} [Fintype X]
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

/-- `⟨u, A B z⟩ = ⟨Aᴴ u, B z⟩`. -/
theorem star_dotProduct_mul_mulVec {X : Type*} [Fintype X] (A B : Matrix X X ℂ) (u z : X → ℂ) :
    star u ⬝ᵥ ((A * B) *ᵥ z) = star (Aᴴ *ᵥ u) ⬝ᵥ (B *ᵥ z) := by
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
theorem norm_markedScalarSymbol_sub_le [∀ v, NeZero (n v)] {t δ s : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1 / 2)
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

/-- The polynomial word on `m + 1` copies:
`∑_i (q(J_Y) b_i^{(k)} p(J_Y))(p(J_P) a_i^{(k)} q(J_P))` (`05-replicas.tex`, lines 693–702). -/
noncomputable def polyWord (P Y : Finset V) {N : ℕ}
    (a b : Fin N → Matrix (SiteConfig n) (SiteConfig n) ℂ) (p q : ℝ[X]) (m : ℕ) :
    Matrix (Fin (m + 1) → SiteConfig n) (Fin (m + 1) → SiteConfig n) ℂ :=
  ∑ i, (aeval (starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) Y)) q *
      siteOp (Fin.last m) (b i) * aeval (starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) Y)) p) *
    (aeval (starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) P)) p *
      siteOp (Fin.last m) (a i) * aeval (starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) P)) q)

/-- **The symbol of a polynomial word** (`05-replicas.tex`, lines 776–812): stars are replaced
by the corresponding marginals. -/
theorem hasMarkedSymbol_polyWord (P Y : Finset V) {N : ℕ}
    (a b : Fin N → Matrix (SiteConfig n) (SiteConfig n) ℂ) (p q : ℝ[X]) :
    HasMarkedSymbol (polyWord P Y a b p q) (polyWordSymbol P Y a b p q) := by
  have hJ : ∀ (Q : Finset V) (r : ℝ[X]), HasMarkedSymbol
      (fun m => aeval (starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) Q)) r)
      (fun θ => aeval (margLift Q θ) r) := fun Q r => (hasMarkedSymbol_starOp Q).aeval r
  exact HasMarkedSymbol.sum (Ω := SiteConfig n) Finset.univ fun i _ =>
    ((((hJ Y q).mul (HasMarkedSymbol.center (b i))).mul (hJ Y p)).mul
      (((hJ P p).mul (HasMarkedSymbol.center (a i))).mul (hJ P q)))

omit [Fintype V] [DecidableEq V] in
theorem commute_symProj_of_forall {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
    {M : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}
    (h : ∀ τ, Commute (permOp (copyPerm Ω k) τ) M) : Commute (symProj (copyPerm Ω k)) M := by
  rw [symProj]
  exact (Commute.sum_left _ _ _ fun τ _ => h τ).smul_left _

variable [∀ v, NeZero (n v)]

theorem isHermitian_markedRatio {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (Q : Finset V) :
    (markedRatio (fun v => Fin (n v)) t m Q).IsHermitian := by
  rw [markedRatio_eq_hom _ ht]
  exact (isOrthogonalResolution_branch m Q).isHermitian_hom (isHermitian_branch _ m Q) _

theorem isHermitian_markedRatio_inv {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (Q : Finset V) :
    ((markedRatio (fun v => Fin (n v)) t m Q)⁻¹).IsHermitian := by
  rw [markedRatio_inv_eq_hom _ ht]
  exact (isOrthogonalResolution_branch m Q).isHermitian_hom (isHermitian_branch _ m Q) _

/-- **The operator-side approximation** (`05-replicas.tex`, lines 693–708): if, at `m + 1`
copies and for `Q = P, Y`, `‖R_Q - p(J_Q)‖ ≤ 2s`, `‖p(J_Q)‖ ≤ 2`, `‖R_Q‖ ≤ C_R`, and on
symmetric vectors `‖R_Q^{-1} z‖ ≤ C_I ‖z‖` and `‖(R_Q^{-1} - q(J_Q)) z‖ ≤ 3s ‖z‖`, then
`‖(O_{m+1} - Π W Π) Π‖ ≤ s K ∑_i ‖a_i‖ ‖b_i‖` for the polynomial word `W`. -/
theorem norm_markedSimilarity_sub_polyWord_le {t s CR CI : ℝ} (ht0 : 0 ≤ t) (m : ℕ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hCR : 0 ≤ CR) (hCI : 0 ≤ CI)
    {P Y F : Finset V} (hPY : Disjoint P Y) (hPF : Disjoint P F) (hYF : Disjoint Y F)
    {h : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hh : IsSupportedOn h (P ∪ Y)) {N : ℕ}
    {a b : Fin N → Matrix (SiteConfig n) (SiteConfig n) ℂ} (ha : ∀ i, IsSupportedOn (a i) P)
    (hb : ∀ i, IsSupportedOn (b i) Y) (hdec : h = ∑ i, b i * a i) {p q : ℝ[X]}
    (hR : ∀ Q, Q = P ∨ Q = Y → ‖markedRatio (fun v => Fin (n v)) t m Q -
      aeval (starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) Q)) p‖ ≤ 2 * s)
    (hp : ∀ Q, Q = P ∨ Q = Y →
      ‖aeval (starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) Q)) p‖ ≤ 2)
    (hRn : ∀ Q, Q = P ∨ Q = Y → ‖markedRatio (fun v => Fin (n v)) t m Q‖ ≤ CR)
    (hRi : ∀ Q, Q = P ∨ Q = Y → ∀ z : (Fin (m + 1) → SiteConfig n) → ℂ,
      z ∈ symmetricSubspace (m + 1) (fun v => Fin (n v)) →
      ‖(EuclideanSpace.equiv _ ℂ).symm ((markedRatio (fun v => Fin (n v)) t m Q)⁻¹ *ᵥ z)‖ ≤
        CI * ‖(EuclideanSpace.equiv _ ℂ).symm z‖)
    (hI : ∀ Q, Q = P ∨ Q = Y → ∀ z : (Fin (m + 1) → SiteConfig n) → ℂ,
      z ∈ symmetricSubspace (m + 1) (fun v => Fin (n v)) →
      ‖(EuclideanSpace.equiv _ ℂ).symm ((markedRatio (fun v => Fin (n v)) t m Q)⁻¹ *ᵥ z -
        aeval (starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) Q)) q *ᵥ z)‖ ≤
        3 * s * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) :
    ‖(markedSimilarity n t (m + 1) P Y F h -
        HasMarkedSymbol.compress (polyWord P Y a b p q) (m + 1)) *
          symProj (copyPerm (SiteConfig n) (m + 1))‖ ≤
      s * ((2 * CI + 6) * CR * CI + (CR * CI + 2 * CI + 6) * (2 * CI + 6)) *
        ∑ i, ‖a i‖ * ‖b i‖ := by
  set Pi := symProj (copyPerm (SiteConfig n) (m + 1))
  set O := markedSimilarity n t (m + 1) P Y F h
  set W := polyWord P Y a b p q m
  set K := (2 * CI + 6) * CR * CI + (CR * CI + 2 * CI + 6) * (2 * CI + 6)
  have hK : 0 ≤ K := by positivity
  have hOc : Commute Pi O :=
    commute_symProj_of_forall (commute_copyPerm_markedSimilarity_succ ht0 m hPY hPF hYF hh)
  have hPP : Pi * Pi = Pi := symProj_mul_symProj
  have heq : (O - HasMarkedSymbol.compress (polyWord P Y a b p q) (m + 1)) * Pi =
      Pi * (O - W) * Pi := by
    change (O - Pi * W * Pi) * Pi = _
    rw [Matrix.sub_mul, Matrix.mul_assoc (Pi * W) Pi Pi, hPP, Matrix.mul_sub, Matrix.sub_mul,
      hOc.eq, Matrix.mul_assoc O Pi Pi, hPP]
  rw [heq]
  refine l2_opNorm_symProj_mul_mul_symProj_le (by positivity) fun u z hu hz => ?_
  have hmv : ∀ (M : Matrix (Fin (m + 1) → SiteConfig n) (Fin (m + 1) → SiteConfig n) ℂ)
      (v : (Fin (m + 1) → SiteConfig n) → ℂ),
      ‖(EuclideanSpace.equiv _ ℂ).symm (M *ᵥ v)‖ ≤ ‖M‖ * ‖(EuclideanSpace.equiv _ ℂ).symm v‖ :=
    fun M v => by simpa using M.l2_opNorm_mulVec ((EuclideanSpace.equiv _ ℂ).symm v)
  set R := fun Q : Finset V => markedRatio (fun v => Fin (n v)) t m Q
  set J := fun Q : Finset V => starOp (subsystemPerm (m + 1) (fun v => Fin (n v)) Q)
  -- One sandwiched vector and its approximation.
  have hsand : ∀ Q, Q = P ∨ Q = Y → ∀ (c : Matrix (SiteConfig n) (SiteConfig n) ℂ)
      (w : (Fin (m + 1) → SiteConfig n) → ℂ),
      w ∈ symmetricSubspace (m + 1) (fun v => Fin (n v)) →
      ‖(EuclideanSpace.equiv _ ℂ).symm (R Q *ᵥ (siteOp (Fin.last m) c *ᵥ ((R Q)⁻¹ *ᵥ w)) -
          aeval (J Q) p *ᵥ (siteOp (Fin.last m) c *ᵥ (aeval (J Q) q *ᵥ w)))‖ ≤
        s * (2 * CI + 6) * ‖c‖ * ‖(EuclideanSpace.equiv _ ℂ).symm w‖ ∧
      ‖(EuclideanSpace.equiv _ ℂ).symm (R Q *ᵥ (siteOp (Fin.last m) c *ᵥ ((R Q)⁻¹ *ᵥ w)))‖ ≤
        CR * ‖c‖ * CI * ‖(EuclideanSpace.equiv _ ℂ).symm w‖ := by
    intro Q hQ c w hw
    have hc : ‖siteOp (Fin.last m) c‖ ≤ ‖c‖ := l2_opNorm_siteOp_le _ _
    have hw0 := norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm w)
    refine ⟨(norm_sandwich_approx_le _ _ _ _ _ w (hR Q hQ) (hRi Q hQ w hw) (hI Q hQ w hw)
      (hp Q hQ)).trans ?_, ?_⟩
    · calc ‖siteOp (Fin.last m) c‖ * (2 * s * CI + 2 * (3 * s)) *
            ‖(EuclideanSpace.equiv _ ℂ).symm w‖
          ≤ ‖c‖ * (2 * s * CI + 2 * (3 * s)) * ‖(EuclideanSpace.equiv _ ℂ).symm w‖ := by gcongr
        _ = _ := by ring
    · calc _ ≤ ‖R Q‖ * (‖siteOp (Fin.last m) c‖ * (CI * ‖(EuclideanSpace.equiv _ ℂ).symm w‖)) :=
            (hmv _ _).trans (mul_le_mul_of_nonneg_left ((hmv _ _).trans
              (mul_le_mul_of_nonneg_left (hRi Q hQ w hw) (norm_nonneg _))) (norm_nonneg _))
        _ ≤ CR * (‖c‖ * (CI * ‖(EuclideanSpace.equiv _ ℂ).symm w‖)) := by
            gcongr
            exact hRn Q hQ
        _ = _ := by ring
  have hO := star_dotProduct_markedSimilarity_eq_sum (F := F) ht0 m hPY hPF hYF hh ha hb hdec
    hu hz
  have hW : star u ⬝ᵥ (W *ᵥ z) = ∑ i, star u ⬝ᵥ
      (((aeval (J Y) q * siteOp (Fin.last m) (b i) * aeval (J Y) p) *
        (aeval (J P) p * siteOp (Fin.last m) (a i) * aeval (J P) q)) *ᵥ z) := by
    simp only [W, polyWord, sum_mulVec, dotProduct_sum]
    rfl
  have e1 : (R Y)ᴴ = R Y := (isHermitian_markedRatio ht0 m Y).eq
  have e2 : ((R Y)⁻¹)ᴴ = (R Y)⁻¹ := (isHermitian_markedRatio_inv ht0 m Y).eq
  have e3 : (aeval (J Y) p)ᴴ = aeval (J Y) p :=
    (isHermitian_aeval_starOp (ι := fun v => Fin (n v)) m Y p).eq
  have e4 : (aeval (J Y) q)ᴴ = aeval (J Y) q :=
    (isHermitian_aeval_starOp (ι := fun v => Fin (n v)) m Y q).eq
  rw [sub_mulVec, dotProduct_sub, hO, hW, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  change ‖star u ⬝ᵥ ((((R Y)⁻¹ * siteOp (Fin.last m) (b i) * R Y) *
      (R P * siteOp (Fin.last m) (a i) * (R P)⁻¹)) *ᵥ z) - star u ⬝ᵥ
      (((aeval (J Y) q * siteOp (Fin.last m) (b i) * aeval (J Y) p) *
        (aeval (J P) p * siteOp (Fin.last m) (a i) * aeval (J P) q)) *ᵥ z)‖ ≤ _
  rw [star_dotProduct_mul_mulVec ((R Y)⁻¹ * siteOp (Fin.last m) (b i) * R Y),
    star_dotProduct_mul_mulVec (aeval (J Y) q * siteOp (Fin.last m) (b i) * aeval (J Y) p)]
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, conjTranspose_mul,
    e1, e2, e3, e4, conjTranspose_siteOp]
  simp only [← mulVec_mulVec]
  obtain ⟨hx, hMx⟩ := hsand P (Or.inl rfl) (a i) z hz
  obtain ⟨hy, hMy⟩ := hsand Y (Or.inr rfl) (b i)ᴴ u hu
  rw [l2_opNorm_conjTranspose] at hy hMy
  have hu0 := norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm u)
  have hz0 := norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm z)
  have ha0 := norm_nonneg (a i)
  have hb0 := norm_nonneg (b i)
  have hMy' : ‖(EuclideanSpace.equiv _ ℂ).symm (aeval (J Y) p *ᵥ
      (siteOp (Fin.last m) (b i)ᴴ *ᵥ (aeval (J Y) q *ᵥ u)))‖ ≤
      (CR * CI + 2 * CI + 6) * ‖b i‖ * ‖(EuclideanSpace.equiv _ ℂ).symm u‖ := by
    have hsplit : aeval (J Y) p *ᵥ (siteOp (Fin.last m) (b i)ᴴ *ᵥ (aeval (J Y) q *ᵥ u)) =
        R Y *ᵥ (siteOp (Fin.last m) (b i)ᴴ *ᵥ ((R Y)⁻¹ *ᵥ u)) -
        (R Y *ᵥ (siteOp (Fin.last m) (b i)ᴴ *ᵥ ((R Y)⁻¹ *ᵥ u)) -
          aeval (J Y) p *ᵥ (siteOp (Fin.last m) (b i)ᴴ *ᵥ (aeval (J Y) q *ᵥ u))) := by abel
    rw [hsplit, map_sub]
    calc _ ≤ CR * ‖b i‖ * CI * ‖(EuclideanSpace.equiv _ ℂ).symm u‖ +
          s * (2 * CI + 6) * ‖b i‖ * ‖(EuclideanSpace.equiv _ ℂ).symm u‖ :=
          (norm_sub_le _ _).trans (add_le_add hMy hy)
      _ ≤ CR * ‖b i‖ * CI * ‖(EuclideanSpace.equiv _ ℂ).symm u‖ +
          1 * (2 * CI + 6) * ‖b i‖ * ‖(EuclideanSpace.equiv _ ℂ).symm u‖ := by gcongr
      _ = _ := by ring
  refine (norm_pairing_approx_le _ _ _ _ hx hMx hy hMy').trans (le_of_eq ?_)
  ring

/-- **Lemma 6.4, the coherent symbol** (`05-replicas.tex`, lines 615–638 and 663–836): for
disjoint `P, Y, F`, `0 < t < 1/2` and `h` supported on `P ∪ Y`, the similarity transforms
`O_k = A_k^{-1/2} hbar A_k^{1/2}` have, on the symmetric subspace, the coherent symbol
`f_θ = ⟨θ, ρ_P^t ρ_Y^{-t} h ρ_P^{-t} ρ_Y^t θ⟩`. -/
theorem hasCoherentSymbol_markedSimilarity {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2)
    {P Y F : Finset V} (hPY : Disjoint P Y) (hPF : Disjoint P F) (hYF : Disjoint Y F)
    {h : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hh : IsSupportedOn h (P ∪ Y)) :
    HasCoherentSymbol (Ω := SiteConfig n) (fun k => markedSimilarity n t k P Y F h)
      (markedScalarSymbol t P Y h) := by
  set ι : V → Type := fun v => Fin (n v)
  have σ₀ : SiteConfig n := fun _ => 0
  obtain ⟨N, b, a, hb, ha, hdec⟩ :=
    (show IsSupportedOn h (Y ∪ P) by rwa [Finset.union_comm]).exists_sum_mul hPY.symm σ₀
  obtain ⟨C₁, hC₁⟩ := exists_l2_opNorm_markedRatio_sub_le ι ht0 (by linarith)
  obtain ⟨CR₀, hCR₀⟩ := exists_l2_opNorm_markedRatio_le ι ht0 (by linarith)
  obtain ⟨CI₀, hCI₀⟩ := exists_norm_markedRatio_inv_mulVec_le ι ht0 ht1
  obtain ⟨C₂, hC₂⟩ := exists_norm_markedRatio_inv_sub_clipped_le ι ht0 ht1
  obtain ⟨Cb, hCb⟩ := exists_norm_markedSimilarity_mulVec_le ht0 ht1 hPY hPF hYF hh
  set CR := max CR₀ 0
  set CI := max CI₀ 0
  have hCR : 0 ≤ CR := le_max_right _ _
  have hCI : 0 ≤ CI := le_max_right _ _
  have hmv : ∀ {k : ℕ} (M : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ)
      (v : (Fin k → SiteConfig n) → ℂ),
      ‖(EuclideanSpace.equiv _ ℂ).symm (M *ᵥ v)‖ ≤ ‖M‖ * ‖(EuclideanSpace.equiv _ ℂ).symm v‖ :=
    fun M v => by simpa using M.l2_opNorm_mulVec ((EuclideanSpace.equiv _ ℂ).symm v)
  have hzero : markedSimilarity n t 0 P Y F h = 0 := by
    have h0 : copyMean n 0 h = 0 := by simp [copyMean]
    simp [markedSimilarity, h0]
  refine HasCoherentSymbol.of_approx (fun k => ?_) ⟨max Cb 0, fun k => ?_⟩ fun ε hε => ?_
  · -- Commutation with the symmetric projector.
    rcases k with _ | m
    · exact hzero ▸ Commute.zero_right _
    · exact commute_symProj_of_forall (commute_copyPerm_markedSimilarity_succ ht0.le m hPY hPF
        hYF hh)
  · -- Uniform boundedness on the symmetric subspace.
    refine l2_opNorm_le_of_forall (le_max_right _ _) fun v => ?_
    rw [← mulVec_mulVec]
    have hPv : ‖(EuclideanSpace.equiv _ ℂ).symm (symProj (copyPerm (SiteConfig n) k) *ᵥ v)‖ ≤
        ‖(EuclideanSpace.equiv _ ℂ).symm v‖ :=
      (hmv _ _).trans (mul_le_of_le_one_left (norm_nonneg _) l2_opNorm_symProj_le)
    calc _ ≤ Cb * ‖(EuclideanSpace.equiv _ ℂ).symm (symProj (copyPerm (SiteConfig n) k) *ᵥ v)‖ :=
          hCb k _ (symProj_mulVec_mem _ v)
      _ ≤ max Cb 0 * ‖(EuclideanSpace.equiv _ ℂ).symm
            (symProj (copyPerm (SiteConfig n) k) *ᵥ v)‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max Cb 0 * ‖(EuclideanSpace.equiv _ ℂ).symm v‖ :=
          mul_le_mul_of_nonneg_left hPv (le_max_right _ _)
  -- The approximation: first `δ`, then the polynomials, then `k`.
  set dP : ℝ := (Fintype.card (RegionConfig n P) : ℝ)
  set dY : ℝ := (Fintype.card (RegionConfig n Y) : ℝ)
  set S := ∑ i, ‖a i‖ * ‖b i‖
  set Kop := (2 * CI + 6) * CR * CI + (CR * CI + 2 * CI + 6) * (2 * CI + 6)
  set Ksym := (√dY + 4) * √dP + (2 * √dY + 4) * (√dP + 4)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hKop : 0 ≤ Kop := by positivity
  have hKsym : 0 ≤ Ksym := by positivity
  set s := min 1 (ε / ((Kop + Ksym) * S + 1))
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsK : ∀ K, 0 ≤ K → K ≤ Kop + Ksym → s * K * S ≤ ε := fun K hK0 hK => by
    have h1 : s ≤ ε / ((Kop + Ksym) * S + 1) := min_le_right _ _
    have h2 : s * ((Kop + Ksym) * S + 1) ≤ ε := by
      rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith [mul_le_mul_of_nonneg_left hK hs0.le, mul_nonneg hs0.le hK0]
  set C₂' := max C₂ 0
  set r := (1 - 2 * t) / 2
  have hr : 0 < r := by simp only [r]; linarith
  obtain ⟨δ, hδ0, hδ1, hδr⟩ := exists_rpow_le hr
    (show 0 < s / (C₂' + √dP + √dY + 1) by positivity)
  have hδr' : ∀ c, 0 ≤ c → c ≤ C₂' + √dP + √dY + 1 → c * δ ^ r ≤ s := fun c hc0 hc => by
    rw [le_div_iff₀ (by positivity)] at hδr
    have := mul_le_mul hc (le_refl (δ ^ r)) (Real.rpow_nonneg hδ0.le _) (by positivity)
    nlinarith [Real.rpow_nonneg hδ0.le r]
  have hsqrt : ∀ d : ℝ, 0 ≤ d → √d ≤ C₂' + √dP + √dY + 1 → √(d * δ ^ (1 - 2 * t)) ≤ s :=
    fun d hd hdle => by
      have : √(d * δ ^ (1 - 2 * t)) = √d * δ ^ r := by
        rw [Real.sqrt_mul hd, Real.sqrt_eq_rpow (δ ^ (1 - 2 * t)), ← Real.rpow_mul hδ0.le]
        congr 2
        simp only [r]; ring
      rw [this]
      exact hδr' _ (Real.sqrt_nonneg _) hdle
  have hdP : √(dP * δ ^ (1 - 2 * t)) ≤ s :=
    hsqrt dP (by positivity) (by have := Real.sqrt_nonneg dY; have := le_max_right C₂ 0; linarith)
  have hdY : √(dY * δ ^ (1 - 2 * t)) ≤ s :=
    hsqrt dY (by positivity) (by have := Real.sqrt_nonneg dP; have := le_max_right C₂ 0; linarith)
  have hclip : C₂ * δ ^ r ≤ s := (mul_le_mul_of_nonneg_right (le_max_left C₂ 0)
    (Real.rpow_nonneg hδ0.le _)).trans (hδr' _ (le_max_right _ _) (by
      have := Real.sqrt_nonneg dP; have := Real.sqrt_nonneg dY; linarith))
  -- The polynomials.
  have hfc : ContinuousOn (fun x : ℝ => max x 0 ^ t) (Set.Icc (-1) 1) :=
    ((continuous_id.max continuous_const).rpow_const fun _ => Or.inr ht0.le).continuousOn
  have hgc : ContinuousOn (fun x : ℝ => max x δ ^ (-t)) (Set.Icc (-1) 1) :=
    ((continuous_id.max continuous_const).rpow_const fun x =>
      Or.inl (lt_max_of_lt_right hδ0).ne').continuousOn
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 _ hfc s hs0
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1 _ hgc s hs0
  have hp' : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |max x 0 ^ t - p.eval x| ≤ s := fun x hx => by
    rw [abs_sub_comm]; exact (hp x hx).le
  have hq' : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |max x δ ^ (-t) - q.eval x| ≤ s := fun x hx => by
    rw [abs_sub_comm]; exact (hq x hx).le
  refine ⟨HasMarkedSymbol.compress (polyWord P Y a b p q),
    fun θ => star θ ⬝ᵥ (polyWordSymbol P Y a b p q θ *ᵥ θ),
    (hasMarkedSymbol_polyWord P Y a b p q).hasCoherentSymbol_compress, fun θ hθ => ?_, ?_⟩
  · exact (norm_markedScalarSymbol_sub_le ht0 ht1 hδ0 hs0.le hs1 hPY ha hb hdec hp' hq' hdP hdY
      hθ).trans (hsK Ksym hKsym (by linarith))
  -- The operator side, for large `k`.
  obtain ⟨K₁, hK₁⟩ := hC₂ δ hδ0 hδ1 s hs0
  have hlim : Tendsto (fun m : ℕ => C₁ * ((m + 1 : ℕ) : ℝ) ^ (-t)) atTop (nhds 0) := by
    have := (tendsto_rpow_neg_atTop ht0).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    simpa using this.const_mul C₁
  obtain ⟨K₂, hK₂⟩ := eventually_atTop.mp (hlim.eventually (ge_mem_nhds hs0))
  filter_upwards [eventually_ge_atTop (K₁ + K₂ + 1)] with k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm1 : K₁ ≤ m := by omega
  have hm2 : K₂ ≤ m := by omega
  have hfJ : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |max x 0 ^ t| ≤ 1 := fun x hx => by
    rw [abs_of_nonneg (Real.rpow_nonneg (le_max_right _ _) _)]
    exact Real.rpow_le_one (le_max_right _ _) (max_le hx.2 zero_le_one) ht0.le
  refine (norm_markedSimilarity_sub_polyWord_le (F := F) ht0.le m hs0.le hs1 hCR hCI hPY hPF
    hYF hh ha hb hdec ?_ ?_ ?_ ?_ ?_).trans (hsK Kop hKop (by linarith))
  · intro Q _
    calc _ ≤ ‖markedRatio ι t m Q - cfc (fun x : ℝ => max x 0 ^ t)
            (starOp (subsystemPerm (m + 1) ι Q))‖ +
          ‖cfc (fun x : ℝ => max x 0 ^ t) (starOp (subsystemPerm (m + 1) ι Q)) -
            aeval (starOp (subsystemPerm (m + 1) ι Q)) p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ s + s := add_le_add ((hC₁ m Q).trans (hK₂ m hm2))
          (l2_opNorm_cfc_starOp_sub_aeval_le m Q _ p hs0.le hp')
      _ = 2 * s := by ring
  · intro Q _
    refine l2_opNorm_aeval_starOp_le m Q p (by norm_num) fun x hx => ?_
    have h1 := hp' x hx
    have h2 := hfJ x hx
    calc |p.eval x| = |max x 0 ^ t - (max x 0 ^ t - p.eval x)| := by ring_nf
      _ ≤ |max x 0 ^ t| + |max x 0 ^ t - p.eval x| := abs_sub _ _
      _ ≤ 2 := by linarith
  · intro Q _
    exact (hCR₀ m Q).trans (le_max_left _ _)
  · intro Q _ z hz
    exact (hCI₀ m Q z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · intro Q _ z hz
    have hsplit : (markedRatio ι t m Q)⁻¹ *ᵥ z - aeval (starOp (subsystemPerm (m + 1) ι Q)) q *ᵥ z =
        ((markedRatio ι t m Q)⁻¹ - cfc (fun x : ℝ => max x δ ^ (-t))
          (starOp (subsystemPerm (m + 1) ι Q))) *ᵥ z +
        (cfc (fun x : ℝ => max x δ ^ (-t)) (starOp (subsystemPerm (m + 1) ι Q)) -
          aeval (starOp (subsystemPerm (m + 1) ι Q)) q) *ᵥ z := by
      rw [sub_mulVec, sub_mulVec]; abel
    rw [hsplit, map_add]
    have hz0 := norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm z)
    calc _ ≤ (C₂ * δ ^ r + s) * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ +
          s * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ :=
          (norm_add_le _ _).trans (add_le_add (hK₁ m hm1 Q z hz) ((hmv _ _).trans
            (mul_le_mul_of_nonneg_right (l2_opNorm_cfc_starOp_sub_aeval_le m Q _ q hs0.le hq')
              hz0)))
      _ ≤ (s + s) * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ +
          s * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ := by gcongr
      _ = 3 * s * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ := by ring

/-- **Lemma 6.4, equation `replicas:polynomial-symbol`** (`05-replicas.tex`, lines 631–638):
for every noncommutative polynomial `q` in two variables,
`sup_σ |Tr σ q(O_k, O_k^†) - ∫ q(f_θ, conj f_θ) dμ_σ(θ)| → 0` over symmetric density
matrices `σ`. -/
theorem eventually_norm_trace_freeAlgebra_markedSimilarity_sub_le {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1 / 2) {P Y F : Finset V} (hPY : Disjoint P Y) (hPF : Disjoint P F)
    (hYF : Disjoint Y F) {h : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hh : IsSupportedOn h (P ∪ Y)) (q : FreeAlgebra ℂ (Fin 2)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ (a : SiteConfig n)
      (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
      σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
        ‖(σ * FreeAlgebra.lift ℂ ![markedSimilarity n t k P Y F h,
            (markedSimilarity n t k P Y F h)ᴴ] q).trace -
          coherentIntegral a σ (fun θ => FreeAlgebra.lift ℂ
            ![markedScalarSymbol t P Y h θ, star (markedScalarSymbol t P Y h θ)] q)‖ ≤ ε :=
  ((hasCoherentSymbol_markedSimilarity ht0 ht1 hPY hPF hYF hh).freeAlgebra
    q).eventually_norm_trace_sub_le hε

end TensorPower
