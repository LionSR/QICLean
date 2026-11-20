/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.SupportedMarginalTails
import QICLean.Entropy.FilterMoment
import QICLean.ManyBody.Sites.RegionState

/-!
# The algebra of operators supported on a region

On a finite tensor product `⊗_{v ∈ V} ℂ^{n_v}`, the operators supported on a region `D` form
the unital `*`-subalgebra `ManyBody.supportedOperators (fun v ↦ Fin (n v)) D` of the matrix
algebra. Its closure properties are membership in a `*`-subalgebra (`add_mem`, `mul_mem`,
`star_mem`, `pow_mem`, `sum_mem`, ...), and operators supported on disjoint regions commute
(`ManyBody.commute_of_mem_supportedOperators_of_disjoint`); none of these needs a reference
configuration.

## Main results

* `Entropy.kronecker_one_mul_one_kronecker_comm` — `A ⊗ 1` and `1 ⊗ B` commute.
-/

open Matrix

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {D : Finset V}

omit [Fintype V] [DecidableEq V] in
/-- `A ⊗ 1` and `1 ⊗ B` commute. -/
theorem kronecker_one_mul_one_kronecker_comm {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (KA : Matrix a a ℂ) (KB : Matrix b b ℂ) :
    KA.kroneckerMap (· * ·) (1 : Matrix b b ℂ) * (1 : Matrix a a ℂ).kroneckerMap (· * ·) KB =
      (1 : Matrix a a ℂ).kroneckerMap (· * ·) KB * KA.kroneckerMap (· * ·) (1 : Matrix b b ℂ) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul]; simp

end Entropy
