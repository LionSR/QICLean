/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Ring
import QICLean.Circuit.Model.Unitary

/-!
# Unitary circuits on the ring

On the ring of `N` sites, with cells `{k, k + 1}` of cost `1`, the `T`-fold neighbourhood of a
region is its ring ball of radius `T` (`Geometry.iterate_neighbourhood_ring`). The light cone of
a unitary circuit of depth `T` is therefore the ring ball of radius `T`, and in a vector prepared
in depth `T` the connected correlations of operators at ring distance larger than `2T` vanish.
These are the facts about the states of the lower bound of arXiv:2307.01696 (Theorem 1) used in
its proof.

The source applies the correlation statement at `s = 2T + 1`, where `𝒪₁` and `𝒪'ₛ` sit at ring
distance exactly `2T`; the separation hypothesis here excludes that case, which would need a
sharper light cone than the symmetric one, such as that of a brickwork circuit.

The declarations restate `conj_circuitOp_mem_supportedOperators`,
`expect_mul_mul_expect_one_of_isPreparedInDepth` and `expect_mul_eq_of_isPreparedInDepth` of
`TNLean/Circuit/LocalCircuit.lean` at commit `414a18fb88` (Apache-2.0). The changes: the
circuits are `IsUnitaryCircuit (Geometry.ring N)` with any finite basis at each site; the
expectation `⟨ψ|A|ψ⟩` is written `star ψ ⬝ᵥ (A *ᵥ ψ)`; the ring ball and the separation on the
ring are `ManyBody.graphNeighborhood` and `ManyBody.IsGraphSeparated` in the cycle graph.

## Main results

In the namespace `QuantumCircuit`:

* `IsUnitaryCircuit.conjTranspose_mul_mul_mem_supportedOperators_graphNeighborhood_cycleGraph` —
  the ring light cone.
* `IsPreparedInDepth.dotProduct_mul_mul_of_isGraphSeparated`,
  `IsPreparedInDepth.dotProduct_mul_eq_of_isGraphSeparated` — vanishing connected correlations
  beyond ring distance `2T`.
-/

open Matrix ManyBody SimpleGraph

namespace QuantumCircuit

variable {N : ℕ} [NeZero N] {Y : Fin N → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- **The ring light cone.** If `U` is a unitary circuit of depth at most `T` on the ring and `A`
is supported on `R`, then `Uᴴ A U` is supported on the sites within ring distance `T` of `R`.

Source: arXiv:2307.01696, main text after Theorem 1 ("`|ψ_N⟩` have a strictly finite light
cone") and Supplemental Material, proof of Theorem 1. -/
theorem IsUnitaryCircuit.conjTranspose_mul_mul_mem_supportedOperators_graphNeighborhood_cycleGraph
    {T : ℕ} {U : Matrix (Config Y) (Config Y) ℂ} (hU : IsUnitaryCircuit (Geometry.ring N) T U)
    {R : Finset (Fin N)} {A : Matrix (Config Y) (Config Y) ℂ}
    (hA : A ∈ supportedOperators Y R) :
    Uᴴ * A * U ∈ supportedOperators Y (graphNeighborhood (cycleGraph N) R T) := by
  rw [← Geometry.iterate_neighbourhood_ring]
  exact hU.conjTranspose_mul_mul_mem_supportedOperators Geometry.ring_cost_pos hA

/-- **Vanishing connected correlations beyond ring distance `2T`.** For a vector `ψ` prepared in
depth `T` on the ring and operators `A`, `B` on sets at ring distance larger than `2T`,
`⟨ψ|AB|ψ⟩⟨ψ|ψ⟩ = ⟨ψ|A|ψ⟩⟨ψ|B|ψ⟩`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1: "since `ψ` is created
from a product state by a depth-`T` circuit, every connected correlation for operators at a
distance larger than `2T` vanishes". -/
theorem IsPreparedInDepth.dotProduct_mul_mul_of_isGraphSeparated {T : ℕ}
    {ψ : Config Y → ℂ} (hψ : IsPreparedInDepth (Geometry.ring N) T ψ) {R R' : Finset (Fin N)}
    (hRR' : IsGraphSeparated (cycleGraph N) R R' (2 * T)) {A B : Matrix (Config Y) (Config Y) ℂ}
    (hA : A ∈ supportedOperators Y R) (hB : B ∈ supportedOperators Y R') :
    star ψ ⬝ᵥ ((A * B) *ᵥ ψ) * (star ψ ⬝ᵥ ψ) =
      (star ψ ⬝ᵥ (A *ᵥ ψ)) * (star ψ ⬝ᵥ (B *ᵥ ψ)) := by
  refine hψ.dotProduct_mul_mul Geometry.ring_cost_pos ?_ hA hB
  rw [Geometry.iterate_neighbourhood_ring, Geometry.iterate_neighbourhood_ring]
  exact hRR'.disjoint_graphNeighborhood

/-- For a unit vector `ψ` prepared in depth `T` on the ring, the connected correlation of
operators at ring distance larger than `2T` vanishes: `⟨AB⟩ = ⟨A⟩⟨B⟩`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 ("every connected
correlation for operators at a distance larger than `2T` vanishes"). -/
theorem IsPreparedInDepth.dotProduct_mul_eq_of_isGraphSeparated {T : ℕ}
    {ψ : Config Y → ℂ} (hψ : IsPreparedInDepth (Geometry.ring N) T ψ)
    (hnorm : star ψ ⬝ᵥ ψ = 1) {R R' : Finset (Fin N)}
    (hRR' : IsGraphSeparated (cycleGraph N) R R' (2 * T))
    {A B : Matrix (Config Y) (Config Y) ℂ} (hA : A ∈ supportedOperators Y R)
    (hB : B ∈ supportedOperators Y R') :
    star ψ ⬝ᵥ ((A * B) *ᵥ ψ) = (star ψ ⬝ᵥ (A *ᵥ ψ)) * (star ψ ⬝ᵥ (B *ᵥ ψ)) := by
  have h := hψ.dotProduct_mul_mul_of_isGraphSeparated hRR' hA hB
  rwa [hnorm, mul_one] at h

end QuantumCircuit
