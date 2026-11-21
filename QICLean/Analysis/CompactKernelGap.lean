/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Normed.Group.Basic
import QICLean.Topology.CompactUniformBounds
import QICLean.Analysis.KernelGapPerturbation
import QICLean.Analysis.OrthogonalKernelGap

/-!
# Uniform norm gaps on compact parameter sets

Locally uniform norm lower bounds, valid for every length beyond a threshold, have one positive
constant and one threshold over a compact parameter set. A continuous family of operators on a
finite-dimensional Hilbert space has a uniform positive lower norm bound away from its kernels on
a compact parameter set, provided the orthogonal kernel projections are continuous. Positivity
and self-adjointness are unnecessary for these norm estimates. Both are the compactness step of
the gap argument in arXiv:1010.3732, Appendix A, lines 2575--2578; the matrix form of the second
statement is `IsCompact.exists_uniform_isGapped`.

Moved from TNLean, `TNLean/Algebra/CompactGapBounds.lean` and
`TNLean/Algebra/CompactKernelGap.lean` at commit `414a18fb88`, with no change to the statements.

## Main results

* `IsCompact.exists_uniform_norm_lower_bound_on_tail` — locally uniform norm lower bounds beyond
  a threshold are uniform on a compact set.
* `ContinuousLinearMap.exists_uniform_norm_gap_of_compact` — a uniform norm gap away from the
  kernels on a compact parameter set.
-/

open scoped Topology

namespace IsCompact

/-- Locally uniform norm lower bounds on a tail have one positive constant
and one threshold over a compact parameter set. This specializes the compactness
step of arXiv:1010.3732, Appendix A; linearity is unnecessary. -/
theorem exists_uniform_norm_lower_bound_on_tail
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    {E F : ℕ → Type*} [∀ N, SeminormedAddCommGroup (E N)]
    [∀ N, SeminormedAddCommGroup (F N)]
    (H : X → ∀ N : ℕ, E N → F N) (V : X → ∀ N : ℕ, Set (E N))
    (hlocal : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ,
      ∀ᶠ y in 𝓝 x, ∀ N : ℕ, N₀ ≤ N → ∀ v ∈ V y N, δ * ‖v‖ ≤ ‖H y N v‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ x ∈ S, ∀ N : ℕ, N₀ ≤ N →
      ∀ v ∈ V x N, δ * ‖v‖ ≤ ‖H x N v‖ := by
  apply hS.exists_uniform_pos_nat_bounds
    (fun δ N₀ x => ∀ N : ℕ, N₀ ≤ N → ∀ v ∈ V x N, δ * ‖v‖ ≤ ‖H x N v‖)
  · intro δ δ' N₀ x hle hgap N hN v hv
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap N hN v hv)
  · intro δ N₀ N₁ x hle hgap N hN
    exact hgap N (hle.trans hN)
  · exact hlocal

end IsCompact

namespace ContinuousLinearMap

/-- Continuous operators with continuous orthogonal kernel projections have a
uniform positive norm gap on compact parameter sets. The pointwise gaps follow
from finite dimensionality. Source: arXiv:1010.3732, Appendix A, lines 2575--2578,
for the application to finite-window parent Hamiltonians. -/
theorem exists_uniform_norm_gap_of_compact
    {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (H : X → E →L[ℂ] E) (hH : Continuous H)
    (hK : Continuous fun x => (LinearMap.ker (H x).toLinearMap).starProjection)
    {S : Set X} (hS : IsCompact S) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ, δ * ‖v‖ ≤ ‖H x v‖ := by
  suffices ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ x ∈ S,
      ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ, δ * ‖v‖ ≤ ‖H x v‖ by
    obtain ⟨δ, hδ, _, hgap⟩ := this
    exact ⟨δ, hδ, hgap⟩
  apply hS.exists_uniform_pos_nat_bounds
    (fun δ _ x => ∀ v ∈ (LinearMap.ker (H x).toLinearMap)ᗮ,
      δ * ‖v‖ ≤ ‖H x v‖)
  · exact fun hle hgap v hv =>
      (mul_le_mul_of_nonneg_right hle (norm_nonneg v)).trans (hgap v hv)
  · exact fun _ hgap => hgap
  · intro x _hx
    obtain ⟨γ, hγ, hgap⟩ :=
      (H x).toLinearMap.exists_pos_mul_norm_le_of_mem_orthogonal_ker
    refine ⟨γ / 2, half_pos hγ, 0, ?_⟩
    apply eventually_norm_gap_on_orthogonal H
      (fun y => LinearMap.ker (H y).toLinearMap)
      hH.continuousAt hK.continuousAt le_rfl hγ (half_lt_self hγ) hgap

end ContinuousLinearMap
