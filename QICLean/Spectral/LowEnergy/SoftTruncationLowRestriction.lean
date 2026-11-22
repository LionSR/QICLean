/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.LowEnergy.WeightedLowRestriction
import QICLean.Spectral.Filter.SoftTruncationHardResidual
import QICLean.Spectral.Filter.ShiftedSoftHardTruncation

/-!
# Soft truncation on a low spectral span

Let `A` be Hermitian with `A ≥ p`, let `X` commute with `A` and dominate `u Q`, where `Q` is the
spectral projection of `A` onto the energies at least `c`, and let a conjugation bound
`‖e^{s(A - c)} Y e^{-s(A - c)}‖ ≤ C < u - e` hold. On the span `G` of the eigenvectors of
`X + Y` of energy at most `e`, the soft truncation of `A - p` at level `t` and order `m` changes
`A - p` by at most
`exp(-s (p + T - c) - 1)/s · C/(u - e - C) + (t/m) (T/t)^m`
for every `T ≥ 0` with `c ≤ p + T`. The first term is the hard truncation at `p + T` on `G`
(AKL14, Theorem `lowspec`); the second compares the soft and the hard truncations of `A - p`
at `T` (ALVV, `lem:exp-approx`).

The projection floor `u` and the threshold `c` of the projection are independent, and no
upper bound on the norm of `A` is used.

Moved from TNLean, `TNLean/MPS/AreaLaw/RegionalBarrierResidual.lean` at commit `49b78ed821`
(Apache-2.0). Changes: stated for arbitrary matrices `A`, `X`, `Y` with a conjugation bound
`C` on `Y` as a hypothesis, in place of regional sums of the terms of a chain interaction and
the bound `C = 2 |J|` that those terms satisfy.

## Main results

* `Matrix.norm_soft_truncation_excess_low_le_of_conjugation_le` — the soft residual on the low
  spectral span.

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168.
* Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The soft residual on a low spectral span.** For Hermitian `A ≥ p`, `X` commuting with
`A` with `u Q ≤ X` for the spectral projection `Q` of `A` onto the energies at least `c`, an
eigenbasis of `X + Y`, and `‖e^{s(A - c)} Y e^{-s(A - c)}‖ ≤ C < u - e`, the soft truncation
of `A - p` changes it, on the span of the eigenvectors of `X + Y` of energy at most `e`, by at
most `exp(-s (p + T - c) - 1)/s · C/(u - e - C) + (t/m) (T/t)^m` whenever `0 ≤ T` and
`c ≤ p + T`. AKL14, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168; ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem norm_soft_truncation_excess_low_le_of_conjugation_le
    (A X Y : Matrix n n ℂ) (hA : A.IsHermitian) (p c u e s t T C : ℝ) (m : ℕ)
    (hp : (p : ℂ) • (1 : Matrix n n ℂ) ≤ A)
    (hs0 : 0 < s) (ht : 0 < t) (hm : 1 ≤ m) (hT : 0 ≤ T) (hcut : c ≤ p + T)
    (hXA : Commute X A) (horder : u • spectralProjectionGE A c ≤ X)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hEigen : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) (X + Y) (b j) = (a j : ℂ) • b j)
    (hconj : ‖NormedSpace.exp (s • (A - c • (1 : Matrix n n ℂ))) * Y *
      NormedSpace.exp (-(s • (A - c • (1 : Matrix n n ℂ))))‖ ≤ C)
    (hgap : C < u - e) :
    ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)
        (A - (p : ℂ) • 1 - cfc (Real.softTruncation t m) (A - (p : ℂ) • 1))).domRestrict
      (Submodule.spectralSpanLE b a e)‖ ≤
      (Real.exp (-s * ((p + T) - c) - 1) / s) * (C / (u - e - C)) +
        (t / (m : ℝ)) * (T / t) ^ m := by
  have hc : (c - u) + u = c := sub_add_cancel c u
  have hhard := norm_truncation_excess_low_le_of_conjugation_le A X Y hA (c - u) u e s
    (p + T - (c - u)) C hs0 (by linarith) hXA (by rwa [hc]) b a hEigen (by rwa [hc]) hgap
  rw [show c - u + (p + T - (c - u)) = p + T by ring,
    show p + T - (c - u) - u = p + T - c by ring] at hhard
  have hcmp := (le_iff.mp hp).norm_softTruncation_residual_domRestrict_le t m T ht hm hT
    (Submodule.spectralSpanLE b a e)
  have hclip : A - (p : ℂ) • 1 - energyTruncation (A - (p : ℂ) • 1) T =
      A - cfc (fun x : ℝ ↦ min x (p + T)) A := by
    rw [hA.energyTruncation_sub_smul_one p T, energyTruncation]
    abel
  rw [hclip] at hcmp
  exact hcmp.trans (add_le_add hhard le_rfl)

end Matrix
