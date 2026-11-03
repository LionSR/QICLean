/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceTrimming

/-!
# Collective trimming relative to a nearby reference space

ALVV, arXiv:1602.08828v2, proof of Theorem `t:alg1`, lines 1801–1813, uses
an approximating space of bounded Schmidt rank to control collective trimming
of a viable subspace. Weighted robustness keeps the coefficient of the
initial viability error arbitrarily close to one. The estimate below uses
the actual collective trimming projections; it does not require the entire
trimmed image to remain close to the entire untrimmed space.

**Local fix (the collective trimming constant):** The proven error increment
is `2 ξ √(m b)` rather than the printed `ξ √(ℓ b s)`. The reference-space
argument below retains this corrected constant. See
`docs/paper-gaps/alvv16_trimming_constant.tex`.
-/

open Matrix

namespace Entropy

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β]
  {n : V → ℕ} {s : ℕ}

/-- Target-relative collective trimming with a free positive robustness weight.
The reference has bounded Schmidt rank across each actual cut. This refines
ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1813. -/
theorem isCloseTo_prodExt_trimSubspace_of_reference_weighted
    {D : ℕ → Finset V} {ξ δ ε θ : ℝ} (hD : Monotone D) (hξ : 0 < ξ)
    (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hθ : 0 < θ)
    {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (bS : OrthonormalBasis (Fin s) ℂ S)
    {T R : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))}
    (hS : Submodule.IsCloseTo δ (Submodule.prodExt S β) T)
    (hTR : Submodule.IsCloseTo ε T R) (hRT : Submodule.IsCloseTo ε R T)
    {m b : ℕ}
    (hb : ∀ t ∈ R, ∀ j < m, Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (D j) t)) ≤ b) :
    Submodule.IsCloseTo
      ((1 + θ) * ((1 + θ) * δ + (1 + 1 / θ) * ε + 2 * (ξ * √(m * b))) +
        (1 + 1 / θ) * ε)
      (Submodule.prodExt (trimSubspace D ξ (fun i ↦ (bS i : _)) m) β) T := by
  have hSR := hS.trans_weighted hTR hδ hθ
  have ht := isCloseTo_prodExt_trimSubspace hD hξ bS hSR hb
  exact ht.trans_weighted hRT (by positivity) hθ

end Entropy
