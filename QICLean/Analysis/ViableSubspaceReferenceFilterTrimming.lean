/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceReferenceTrimming
import QICLean.Analysis.ViableSubspaceOrder
import QICLean.Analysis.ViableSubspaceSharpErrorReduction
import QICLean.Analysis.ViableFilterTrimmingIteration

/-!
# One stable step of filtering and collective trimming

The actual image of a viable space is contained in the recorded filtered
space, to which the actual collective trimming projections are applied.
A low-Schmidt-rank reference controls this trim. The error recurrence supports
ALVV, arXiv:1602.08828v2, Algorithm `t:alg1`, lines 1634–1640, and the reference
argument in its proof, lines 1801–1813.

**Local fix (the collective trimming constant):** The reference argument uses
the proved increment `2 ξ √(m b)`; see
`docs/paper-gaps/alvv16_trimming_constant.tex`.
-/

namespace Entropy

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β]
  {n : V → ℕ} {s : ℕ}

/-- A stable error bound for the actual filter image followed by collective trimming.
The reference accuracy and threshold are explicit. This auxiliary is the operator
and trimming step in ALVV, arXiv:1602.08828v2, proof of `t:alg1`, lines 1801–1813;
the construction of the physical reference and its parameters is separate. -/
theorem isCloseTo_prodExt_trimSubspace_after_filter
    {D : ℕ → Finset V} {ξ c δ ε η : ℝ} (hD : Monotone D) (hξ : 0 < ξ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hε0 : 0 ≤ ε)
    {U S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (bS : OrthonormalBasis (Fin s) ℂ S)
    {T R : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))}
    (K : EuclideanSpace ℂ (SiteConfig n × β) →L[ℂ]
      EuclideanSpace ℂ (SiteConfig n × β))
    (hU : Submodule.IsCloseTo δ (Submodule.prodExt U β) T)
    (himage : (Submodule.prodExt U β).map K.toLinearMap ≤ Submodule.prodExt S β)
    (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ q ∈ Tᗮ, K q ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ q ∈ Tᗮ, ‖K q‖ ^ 2 ≤ (1 - c) * ‖q‖ ^ 2)
    (hTR : Submodule.IsCloseTo ε T R) (hRT : Submodule.IsCloseTo ε R T)
    {m b : ℕ}
    (hb : ∀ t ∈ R, ∀ j < m, Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (D j) t)) ≤ b)
    (hε : ε ≤ c ^ 2 * η / 1024) (hξbudget : ξ * √(m * b) ≤ c * η / 48) :
    Submodule.IsCloseTo ((1 - c / 4) * δ + c * η / 8)
      (Submodule.prodExt (trimSubspace D ξ (fun i ↦ (bS i : _)) m) β) T := by
  have hΔ : 0 ≤ 1 - c := by linarith
  have hd : 0 < 1 - δ + (1 - c) * δ := by nlinarith [mul_nonneg hΔ hδ0]
  have hF : 0 ≤ (1 - c) * δ / (1 - δ + (1 - c) * δ) := by positivity
  have hf := (hU.map_of_contract_sharp K hδ0 (by linarith) hΔ hKT hKTo hlow hhigh).mono himage
  have ht := isCloseTo_prodExt_trimSubspace_of_reference_weighted hD hξ hF hε0
    (show 0 < c / 16 by positivity) bS hf hTR hRT hb
  have hrec : 1 / (c / 16) = 16 / c := by field_simp
  rw [hrec] at ht
  have he := Real.reference_filter_trim_error_le hc hc1 hδ0 hδ hε0
    (by positivity : 0 ≤ ξ * √(m * b)) hε hξbudget
  exact ht.of_le he

end Entropy
