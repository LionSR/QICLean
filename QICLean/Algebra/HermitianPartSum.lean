/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Replacing local terms by their Hermitian parts

A Hamiltonian is often given as a finite sum `H = ∑ i, h i` of local terms whose total is
self-adjoint while the individual terms need not be. Replacing every term by its Hermitian
part `ℜ (h i) = (h i + (h i)⋆) / 2` loses nothing: the sum is unchanged, each new term is
self-adjoint, and the operations that describe locality and size are preserved.

* `sum_coe_realPart_of_isSelfAdjoint`: if `∑ i ∈ s, h i` is self-adjoint, then
  `∑ i ∈ s, ℜ (h i) = ∑ i ∈ s, h i`.
* `coe_realPart_mem_of_star_mem`: a real subspace containing `x` and `x⋆` contains `ℜ x`,
  so membership in any star-closed class of operators (such as the operators supported on
  a fixed region) passes to the Hermitian part.

Two further facts needed in the same reduction are already in Mathlib: `realPart.norm_le`
gives `‖ℜ x‖ ≤ ‖x‖` in any normed star module over `ℂ` with isometric star, and
`map_realPart` commutes `ℜ` with a star-preserving linear map, such as the embedding of
operators on a region into operators on the whole system.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem `thm:main`, `eq:model`,
  `00-introduction.tex`, lines 39–44: a Hermitian Hamiltonian `H = ∑ h_v + ∑ h_e` with
  `‖h_v‖, ‖h_e‖ ≤ J`, where only the total is assumed Hermitian.
* The reduction reaches the hypothesis of the companion area-law theorem, in which every
  summand is Hermitian: two-dimensional area-law manuscript (September 24, 2026),
  `eq:hamiltonian`, `00-introduction.tex`, lines 19–23; Polynomial-PEPS manuscript,
  `01-preliminaries.tex`, lines 52–56.

Adapted from openai/math (Apache-2.0), commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
file `lean/OAI/MathematicalPhysics/PEPSFilters/HamiltonianEnergy.lean`, declarations
`hermitianPart_sum`, `hermitianPart_eq` and `hermitianPart_supported`; changes: Mathlib's
`realPart` replaces the auxiliary Hermitian-part definition, the statements hold in any
complex star module rather than for lattice operators, the sum is over an arbitrary finite
set, and lattice supports are replaced by an arbitrary star-closed real subspace.
-/

open ComplexStarModule

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- If a finite sum of terms is self-adjoint, replacing every term by its Hermitian part does
not change the sum. -/
theorem sum_coe_realPart_of_isSelfAdjoint {ι : Type*} (s : Finset ι) (h : ι → A)
    (hs : IsSelfAdjoint (∑ i ∈ s, h i)) :
    ∑ i ∈ s, (ℜ (h i) : A) = ∑ i ∈ s, h i := by
  rw [← hs.coe_realPart, map_sum, AddSubmonoidClass.coe_finsetSum]

/-- A real subspace containing `x` and `x⋆` contains the Hermitian part `ℜ x`. -/
theorem coe_realPart_mem_of_star_mem {S : Submodule ℝ A} {x : A} (hx : x ∈ S)
    (hsx : star x ∈ S) : (ℜ x : A) ∈ S := by
  rw [realPart_apply_coe]
  exact S.smul_mem _ (S.add_mem hx hsx)
