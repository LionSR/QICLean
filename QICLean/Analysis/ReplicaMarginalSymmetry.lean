/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.PermutationRepresentation
import QICLean.Channel.PartialTrace
import QICLean.Analysis.ReplicaExcitationSymmetry

/-!
# Marginal symmetry of exact excitation components

A vector fixed by a simultaneous permutation of two registers has a reduced
density matrix commuting with the permutation on the retained register.
The same conclusion holds for an actual excitation component when the
physical permutation stabilizes its excitation set.

These are the partial-trace identities used in *A two-dimensional area law
from a global spectral gap*, `07-comparators.tex`, lines 540–549, following
equation `comparator:merge-moments`. No normalization or independent-copy
assumption is needed. Selecting and regrouping the good-copy registers and
proving the merge-moment bound are separate assertions.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix
open scoped Matrix Kronecker

namespace PermutationRepresentation

variable {G X Y : Type*} [Group G] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 540–549.
-/

/-- The literal reduced density of a simultaneously fixed vector commutes with
the permutation of its retained register. *A two-dimensional area law from a
global spectral gap*, `07-comparators.tex`, lines 540–549, following equation
`comparator:merge-moments`. The vector need not be normalized. -/
theorem commute_partialTraceLeft_vecMulVec_of_fixed_kronecker_permOp
    (φ : G →* Equiv.Perm X) (χ : G →* Equiv.Perm Y) (g : G)
    (v : X × Y → ℂ) (hv : (permOp φ g ⊗ₖ permOp χ g) *ᵥ v = v) :
    Commute (permOp χ g) (partialTraceLeft (vecMulVec v (star v))) := by
  have hA : (permOp φ g)ᴴ * permOp φ g = 1 := by
    rw [conjTranspose_permOp, permOp_inv_mul_self]
  have hconj : (permOp φ g ⊗ₖ permOp χ g) * vecMulVec v (star v) *
      (permOp φ g ⊗ₖ permOp χ g)ᴴ = vecMulVec v (star v) := by
    rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hv]
  have hpartial := congrArg partialTraceLeft hconj
  rw [partialTraceLeft_kronecker_conj_of_left_isometry _ _ hA] at hpartial
  have hright := congrArg (fun K => K * permOp χ g) hpartial
  change permOp χ g * partialTraceLeft (vecMulVec v (star v)) =
    partialTraceLeft (vecMulVec v (star v)) * permOp χ g
  simpa only [mul_assoc, conjTranspose_permOp, permOp_inv_mul_self, mul_one] using hright

end PermutationRepresentation

namespace Matrix

variable {A C : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]

open PermutationRepresentation TensorPower

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 540–549.
-/

/-- Tracing the physical register of an actual excitation component preserves
its auxiliary permutation symmetry. The symmetry of the component is derived
from that of the original vector and the stabilizer condition.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 540–549, following equation `comparator:merge-moments`. -/
theorem commute_partialTraceLeft_replicaExcitationComponent
    (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k)) (σ : Equiv.Perm (Fin k))
    (hB : B.image σ = B) (χ : Equiv.Perm (Fin k) →* Equiv.Perm C)
    (v : (Fin k → A) × C → ℂ)
    (hv : (permOp (copyPerm A k) σ ⊗ₖ permOp χ σ) *ᵥ v = v) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ v
    Commute (permOp χ σ) (partialTraceLeft (vecMulVec w (star w))) := by
  exact commute_partialTraceLeft_vecMulVec_of_fixed_kronecker_permOp
    (copyPerm A k) χ σ _
    (replicaExcitationProjection_kronecker_mulVec_preserves_fixed Ω k B σ hB _ v hv)

end Matrix
