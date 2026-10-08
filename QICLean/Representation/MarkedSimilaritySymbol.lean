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

end TensorPower
