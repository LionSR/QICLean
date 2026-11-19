/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Ring
import QICLean.Circuit.Model.Protocol

/-!
# Protocols on the ring

On the ring of `N` sites, with cells `{k, k + 1}` of cost `1`, the `T`-fold neighbourhood of a
region is its ring ball of radius `T`. The light cone of a protocol of depth `T` is therefore the
ring ball of radius `T`: its trace-pairing adjoint maps an operator on a region `R` to an
operator on the ring ball of radius `T` about `R`, and is multiplicative on operators on regions
whose balls of radius `T` are disjoint. A state converted in depth `T` from a product state has
no connected correlations between regions at ring distance larger than `2T`.

The local-channel model, with ancillas and discarding but without measurements, is the one of
`docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

The declarations restate, on `Geometry.ring`, the ring light cone and correlation results of
`TNLean/Circuit/Channel/Conversion.lean` and `TNLean/Circuit/Channel/Layer.lean` at commit
`e41c3b6371c44bcecb7004d78ff5ec11ae2282f3` (Apache-2.0). The changes: the protocols are
`IsProtocol (Geometry.ring N)` with any finite basis at each site, in place of inductive families
of onsite channels and bond-channel layers with one dimension at every site; the existential
dual is the trace-pairing adjoint `traceAdjointMap`.

## Main results

* `QuantumCircuit.IsProtocol.traceAdjointMap_mem_supportedOperators_ringBall`,
  `QuantumCircuit.IsProtocol.traceAdjointMap_mul_of_disjoint_ringBall` — the light cone of a
  protocol on the ring.
* `QuantumCircuit.IsConversion.trace_mul_mul_eq_of_isRingSeparated` — vanishing connected
  correlations beyond ring distance `2T`.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {N : ℕ} [NeZero N] {X Z : Fin N → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] {T : ℕ}
  {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}

/-- **Light cone of a protocol on the ring.** The trace-pairing adjoint of a protocol of depth
`T` on the ring maps an operator on `R` to an operator on the ring ball of radius `T` about `R`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (the light cone of a
depth-`T` circuit), here with channels, ancillas and discarding. -/
theorem IsProtocol.traceAdjointMap_mem_supportedOperators_ringBall
    (h : IsProtocol (Geometry.ring N) T Φ) {R : Finset (Fin N)}
    {A : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R) :
    traceAdjointMap Φ A ∈ supportedOperators X (ringBall R T) := by
  simpa only [Geometry.iterate_neighbourhood_ring] using
    h.traceAdjointMap_mem_supportedOperators Geometry.ring_cost_pos hA

/-- The trace-pairing adjoint of a protocol of depth `T` on the ring is multiplicative on
operators on regions whose ring balls of radius `T` are disjoint.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1. -/
theorem IsProtocol.traceAdjointMap_mul_of_disjoint_ringBall
    (h : IsProtocol (Geometry.ring N) T Φ) {R R' : Finset (Fin N)}
    (hRR' : Disjoint (ringBall R T) (ringBall R' T)) {A B : Matrix (Config Z) (Config Z) ℂ}
    (hA : A ∈ supportedOperators Z R) (hB : B ∈ supportedOperators Z R') :
    traceAdjointMap Φ (A * B) = traceAdjointMap Φ A * traceAdjointMap Φ B :=
  h.traceAdjointMap_mul Geometry.ring_cost_pos
    (by simpa only [Geometry.iterate_neighbourhood_ring] using hRR') hA hB

/-- **Vanishing connected correlations beyond distance `2T`.** If `σ` is converted in depth `T`
on the ring from a product `⊗ₛ σ₀ s` of unit-trace factors, then for operators `A`, `B` on
regions separated by `2T`, `tr(σ AB) = tr(σ A) tr(σ B)`.

Source: arXiv:2103.13367, main text, Proposition `propQCA2`, eq. `eq:necessary_condition`, stated
there for pure states prepared from `|0⟩^{⊗M}` by unitary circuits of depth `ℓ`; here for product
inputs and local channels with ancillas and discarding, without measurements. -/
theorem IsConversion.trace_mul_mul_eq_of_isRingSeparated
    {σ₀ : (s : Fin N) → Matrix (X s) (X s) ℂ} (hσ₀ : ∀ s, (σ₀ s).trace = 1)
    {σ : Matrix (Config Z) (Config Z) ℂ} (h : IsConversion (Geometry.ring N) T (prodOp σ₀) σ)
    {R R' : Finset (Fin N)} (hRR' : IsRingSeparated R R' (2 * T))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    (σ * (A * B)).trace = (σ * A).trace * (σ * B).trace :=
  h.trace_mul_mul_eq Geometry.ring_cost_pos hσ₀
    (by simpa only [Geometry.iterate_neighbourhood_ring] using hRR'.disjoint_ringBall) hA hB

end QuantumCircuit
