/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LiebOperatorIntegral
import QICLean.Analysis.LogClipping

/-!
# Inverse-power filters with clipped eigenvalues

A common unitary eigenbasis and a clipped formula for shifted eigenvalues
imply commutation and a logarithmic eigenvalue bound for the inverse filter.
The bound compares only positive marginal coordinates and retains the factor
one half of the filter exponent.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
states*, Proposition 4.1, `03-patches.tex`, lines 190–205,
`eq:patch-clipped-eigenvalues` and `eq:patch-log-ratio`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Suppose `x` and `ρ` have a common unitary diagonalization and their real
coordinates satisfy `s i + b = max (p i / lam) b`, with positive `b` and `lam`.
For every nonnegative exponent `a`, the inverse filter `(x + b 1)^(-a/2)`
commutes with `ρ` and has positive eigenvalues whose logarithmic differences
are bounded by `a/2` times those of the positive coordinates of `ρ`.
No positivity or trace condition on `ρ` is required for this implication.

Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 190–205,
`eq:patch-clipped-eigenvalues` and `eq:patch-log-ratio`; revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem exists_clipped_rpow_add_smul_one_of_diagonal_max
    {x ρ U : Matrix ι ι ℂ} {s p : ι → ℝ}
    (hU : Uᴴ * U = 1)
    (hx : x = U * diagonal (fun i ↦ (s i : ℂ)) * Uᴴ)
    (hρ : ρ = U * diagonal (fun i ↦ (p i : ℂ)) * Uᴴ)
    {b lam a : ℝ} (hb : 0 < b) (hlam : 0 < lam) (ha : 0 ≤ a)
    (hclip : ∀ i, s i + b = max (p i / lam) b) :
    (x + b • (1 : Matrix ι ι ℂ)) ^ (-a / 2) * ρ =
        ρ * (x + b • (1 : Matrix ι ι ℂ)) ^ (-a / 2) ∧
      ∃ (W : Matrix ι ι ℂ) (l q : ι → ℝ),
        Wᴴ * W = 1 ∧ (∀ i, 0 < l i) ∧
        (x + b • (1 : Matrix ι ι ℂ)) ^ (-a / 2) =
          W * diagonal (fun i ↦ (l i : ℂ)) * Wᴴ ∧
        ρ = W * diagonal (fun i ↦ (q i : ℂ)) * Wᴴ ∧
        ∀ i k, 0 < q i → 0 < q k →
          |Real.log (l i) - Real.log (l k)| ≤
            a / 2 * |Real.log (q i) - Real.log (q k)| := by
  let u : unitary (Matrix ι ι ℂ) := ⟨U, mem_unitaryGroup_iff'.mpr hU⟩
  let e := Unitary.conjStarAlgAut ℝ (Matrix ι ι ℂ) u
  have hg (i : ι) : 0 < s i + b := (hclip i).symm ▸ lt_max_of_lt_right hb
  have hd : diagonal (fun i ↦ ((s i + b : ℝ) : ℂ)) =
      diagonal (fun i ↦ (s i : ℂ)) + b • (1 : Matrix ι ι ℂ) := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_one_eq_diagonal,
      diagonal_add, Complex.ofReal_add]
    rfl
  have hshift : x + b • (1 : Matrix ι ι ℂ) =
      e (diagonal (fun i ↦ ((s i + b : ℝ) : ℂ))) := by
    simpa only [map_add, map_smul, map_one, hx, e, Unitary.conjStarAlgAut_apply,
      Unitary.coe_star, u, star_eq_conjTranspose] using (congrArg e hd).symm
  have hfilter : (x + b • (1 : Matrix ι ι ℂ)) ^ (-a / 2) =
      e (diagonal (fun i ↦ (((s i + b) ^ (-a / 2) : ℝ) : ℂ))) := by
    simpa only [hshift, e, Unitary.conjStarAlgAut_apply, Unitary.coe_star,
      rpow_diagonal hg] using
      rpow_conj_unitary (PosSemidef.diagonal fun i ↦ Complex.zero_le_real.mpr (hg i).le)
        (-a / 2) u
  have hlogPos (i k : ι) (hi : 0 < p i) (hk : 0 < p k) :
      |Real.log ((s i + b) ^ (a / 2)) - Real.log ((s k + b) ^ (a / 2))| ≤
        a / 2 * |Real.log (p i) - Real.log (p k)| := by
    simpa only [hclip, max_comm] using Entropy.abs_log_clipped_sub_le hb hlam ha hi hk
  have hlog (i k : ι) (hi : 0 < p i) (hk : 0 < p k) :
      |Real.log ((s i + b) ^ (-a / 2)) - Real.log ((s k + b) ^ (-a / 2))| ≤
        a / 2 * |Real.log (p i) - Real.log (p k)| := by
    simpa only [neg_div, Real.rpow_neg (hg i).le, Real.rpow_neg (hg k).le,
      Real.log_inv, neg_sub_neg, abs_sub_comm] using hlogPos i k hi hk
  refine ⟨?_, U, (fun i ↦ (s i + b) ^ (-a / 2)), p, hU,
    (fun i ↦ Real.rpow_pos_of_pos (hg i) _), ?_, hρ, hlog⟩
  · simpa only [hfilter, hρ, e, Unitary.conjStarAlgAut_apply, Unitary.coe_star, u,
      star_eq_conjTranspose] using
      ((commute_diagonal (fun i ↦ (((s i + b) ^ (-a / 2) : ℝ) : ℂ))
        (fun i ↦ (p i : ℂ))).map e).eq
  · simpa only [e, Unitary.conjStarAlgAut_apply, Unitary.coe_star, u,
      star_eq_conjTranspose] using hfilter

end Matrix
