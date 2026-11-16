/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift

/-!
# The algebra of operators supported on a region

On a finite tensor product `⊗_{v ∈ V} ℂ^{n_v}`, the operators supported on a region `D` form
the unital `*`-subalgebra `ManyBody.supportedOperators (fun v ↦ Fin (n v)) D` of the matrix
algebra. Its closure properties are membership in a `*`-subalgebra (`add_mem`, `mul_mem`,
`star_mem`, `pow_mem`, `sum_mem`, ...), and operators supported on disjoint regions commute
(`ManyBody.commute_of_mem_supportedOperators_of_disjoint`); none of these needs a reference
configuration.

This file keeps the names `Entropy.supportedOperators`, `Entropy.isSupportedOn_one` and
`Entropy.commute_of_isSupportedOn_disjoint` as temporary abbreviations and forwarding lemmas
for the callers of the entropy layer. They are deleted in step 4.0 of the many-body plan
.

## Main results

* `Entropy.kronecker_one_mul_one_kronecker_comm` — `A ⊗ 1` and `1 ⊗ B` commute.
-/

open Matrix

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {D : Finset V}

/-- The operators supported on the region `D`, as a unital `*`-subalgebra of the matrix
algebra on all the sites.

**Temporary abbreviation** of `ManyBody.supportedOperators`; deleted in
step 4.0. -/
abbrev supportedOperators (n : V → ℕ) (D : Finset V) :
    StarSubalgebra ℂ (Matrix (SiteConfig n) (SiteConfig n) ℂ) :=
  ManyBody.supportedOperators (fun v ↦ Fin (n v)) D

omit [DecidableEq V] in
/-- **Temporary** restatement of `one_mem` in `ManyBody.supportedOperators`. -/
theorem isSupportedOn_one (D : Finset V) :
    IsSupportedOn (1 : Matrix (SiteConfig n) (SiteConfig n) ℂ) D := by
  classical
  exact one_mem (supportedOperators n D)

omit [Fintype V] [DecidableEq V] in
/-- `A ⊗ 1` and `1 ⊗ B` commute. -/
theorem kronecker_one_mul_one_kronecker_comm {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (KA : Matrix a a ℂ) (KB : Matrix b b ℂ) :
    KA.kroneckerMap (· * ·) (1 : Matrix b b ℂ) * (1 : Matrix a a ℂ).kroneckerMap (· * ·) KB =
      (1 : Matrix a a ℂ).kroneckerMap (· * ·) KB * KA.kroneckerMap (· * ·) (1 : Matrix b b ℂ) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul]; simp

/-- **Temporary** restatement of `ManyBody.commute_of_mem_supportedOperators_of_disjoint`;
the configuration `σ₀` is not used. -/
theorem commute_of_isSupportedOn_disjoint {D D' : Finset V}
    {X Y : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hX : IsSupportedOn X D)
    (hY : IsSupportedOn Y D') (hDD : Disjoint D' D) (_σ₀ : SiteConfig n) : X * Y = Y * X :=
  ManyBody.commute_of_mem_supportedOperators_of_disjoint (X := fun v ↦ Fin (n v)) hX hY
    hDD.symm

end Entropy
