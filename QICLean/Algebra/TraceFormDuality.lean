/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixTracePairing
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Span criteria from nondegenerate trace pairings

A nondegenerate bilinear form on a finite-dimensional space identifies that space with its
dual, so a subspace annihilated by no nonzero vector is the whole space. This file records
that criterion and instantiates it for the trace pairing of a single finite complex matrix
algebra, of a finite family of such algebras, and of a product of two of them.

The block-indexed and product forms are genuinely different: a product of two matrix
algebras of different sizes is not a dependent family over a two-element index type, so the
two cases carry their own pairings and their own nondegeneracy proofs.

## Main definitions

* `Matrix.piTraceForm` — the trace pairing of a finite family of matrix algebras, summed
  over the blocks
* `Matrix.prodTraceForm` — the trace pairing of a product of two matrix algebras

## Main results

* `LinearMap.BilinForm.eq_top_of_forall_apply_eq_zero` — a subspace paired to zero only by
  the zero vector of a nondegenerate form is everything
* `Matrix.piTraceForm_nondegenerate`, `Matrix.prodTraceForm_nondegenerate` — nondegeneracy
  of the block-indexed and product trace pairings
* `Matrix.eq_top_of_trace_separating`, `Matrix.eq_top_of_pi_trace_separating`,
  `Matrix.eq_top_of_prod_trace_separating` — the span criteria in trace form
-/

open scoped Matrix BigOperators

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A subspace of a finite-dimensional space is everything as soon as the only vector
pairing to zero with all of it under a nondegenerate bilinear form is the zero vector. -/
theorem eq_top_of_forall_apply_eq_zero {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {W : Submodule K V} (h : ∀ v : V, (∀ x ∈ W, B v x = 0) → v = 0) :
    W = ⊤ := by
  rw [← Submodule.dualAnnihilator_eq_bot_iff, eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  have hv : (B.toDual hB).symm f = 0 :=
    h _ fun x hx ↦ by
      rw [LinearMap.BilinForm.apply_toDual_symm_apply]
      exact (Submodule.mem_dualAnnihilator f).mp hf x hx
  simpa using congrArg (B.toDual hB) hv

end LinearMap.BilinForm

namespace Matrix

section Single

variable {n : Type*} [Fintype n]

/-- A subspace of a finite complex matrix algebra paired to zero by no nonzero matrix is
the whole algebra. -/
theorem eq_top_of_trace_separating {W : Submodule ℂ (Matrix n n ℂ)}
    (hSep : ∀ Δ : Matrix n n ℂ, (∀ M ∈ W, Matrix.trace (Δ * M) = 0) → Δ = 0) :
    W = ⊤ :=
  LinearMap.BilinForm.eq_top_of_forall_apply_eq_zero traceBilinForm_nondegenerate hSep

end Single

section Pi

variable {ι : Type*} [Fintype ι] {n : ι → Type*} [∀ i, Fintype (n i)]

/-- The trace pairing of a finite family of complex matrix algebras: the sum over the
blocks of the trace pairings of the blocks. -/
noncomputable def piTraceForm (n : ι → Type*) [∀ i, Fintype (n i)] :
    LinearMap.BilinForm ℂ ((i : ι) → Matrix (n i) (n i) ℂ) :=
  LinearMap.mk₂ ℂ (fun X Y ↦ ∑ i, Matrix.trace (X i * Y i))
    (by intros; simp [Matrix.add_mul, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum])
    (by intros; simp [Matrix.mul_add, Finset.sum_add_distrib])
    (by intros; simp [Finset.mul_sum])

@[simp] theorem piTraceForm_apply (X Y : (i : ι) → Matrix (n i) (n i) ℂ) :
    piTraceForm n X Y = ∑ i, Matrix.trace (X i * Y i) := rfl

/-- A family of matrices pairing to zero with every family under the block-indexed trace
pairing vanishes blockwise. -/
theorem eq_zero_of_forall_sum_trace_mul_eq_zero
    (Δ : (i : ι) → Matrix (n i) (n i) ℂ)
    (hΔ : ∀ M : (i : ι) → Matrix (n i) (n i) ℂ, ∑ i, Matrix.trace (Δ i * M i) = 0) :
    Δ = 0 := by
  classical
  refine funext fun i ↦ (trace_mul_right_eq_zero_iff (Δ i)).1 fun N ↦ ?_
  have hsum := hΔ (Pi.single i N)
  rwa [Finset.sum_eq_single i (fun j _ hj ↦ by simp [Pi.single_eq_of_ne hj])
    (fun hi ↦ absurd (Finset.mem_univ i) hi), Pi.single_eq_same] at hsum

/-- Nondegeneracy of the block-indexed trace pairing. -/
theorem piTraceForm_nondegenerate : (piTraceForm n).Nondegenerate := by
  refine ⟨fun Δ hΔ ↦ eq_zero_of_forall_sum_trace_mul_eq_zero Δ hΔ, fun Δ hΔ ↦ ?_⟩
  refine eq_zero_of_forall_sum_trace_mul_eq_zero Δ fun M ↦ ?_
  calc ∑ i, Matrix.trace (Δ i * M i)
      = ∑ i, Matrix.trace (M i * Δ i) :=
        Finset.sum_congr rfl fun i _ ↦ Matrix.trace_mul_comm _ _
    _ = 0 := hΔ M

/-- A subspace of a finite family of complex matrix algebras paired to zero by no nonzero
family is everything. -/
theorem eq_top_of_pi_trace_separating
    {W : Submodule ℂ ((i : ι) → Matrix (n i) (n i) ℂ)}
    (hSep : ∀ Δ : (i : ι) → Matrix (n i) (n i) ℂ,
      (∀ M ∈ W, ∑ i, Matrix.trace (Δ i * M i) = 0) → Δ = 0) :
    W = ⊤ :=
  LinearMap.BilinForm.eq_top_of_forall_apply_eq_zero piTraceForm_nondegenerate hSep

end Pi

section Prod

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The trace pairing of a product of two complex matrix algebras: the sum of the trace
pairings of the two factors. -/
noncomputable def prodTraceForm (m n : Type*) [Fintype m] [Fintype n] :
    LinearMap.BilinForm ℂ (Matrix m m ℂ × Matrix n n ℂ) :=
  LinearMap.mk₂ ℂ (fun X Y ↦ Matrix.trace (X.1 * Y.1) + Matrix.trace (X.2 * Y.2))
    (by intros; simp [Matrix.add_mul]; ring)
    (by intros; simp [mul_add])
    (by intros; simp [Matrix.mul_add]; ring)
    (by intros; simp [mul_add])

@[simp] theorem prodTraceForm_apply (X Y : Matrix m m ℂ × Matrix n n ℂ) :
    prodTraceForm m n X Y = Matrix.trace (X.1 * Y.1) + Matrix.trace (X.2 * Y.2) := rfl

/-- A pair of matrices pairing to zero with every pair under the product trace pairing
vanishes in both factors. -/
theorem eq_zero_of_forall_trace_mul_add_eq_zero (Δ : Matrix m m ℂ × Matrix n n ℂ)
    (hΔ : ∀ M : Matrix m m ℂ × Matrix n n ℂ,
      Matrix.trace (Δ.1 * M.1) + Matrix.trace (Δ.2 * M.2) = 0) :
    Δ = 0 := by
  refine Prod.ext ?_ ?_
  · refine (trace_mul_right_eq_zero_iff Δ.1).1 fun N ↦ ?_
    simpa using hΔ (N, 0)
  · refine (trace_mul_right_eq_zero_iff Δ.2).1 fun N ↦ ?_
    simpa using hΔ (0, N)

/-- Nondegeneracy of the product trace pairing. -/
theorem prodTraceForm_nondegenerate : (prodTraceForm m n).Nondegenerate := by
  refine ⟨fun Δ hΔ ↦ eq_zero_of_forall_trace_mul_add_eq_zero Δ hΔ, fun Δ hΔ ↦ ?_⟩
  refine eq_zero_of_forall_trace_mul_add_eq_zero Δ fun M ↦ ?_
  rw [Matrix.trace_mul_comm Δ.1 M.1, Matrix.trace_mul_comm Δ.2 M.2]
  exact hΔ M

/-- A subspace of a product of two complex matrix algebras paired to zero by no nonzero
pair is everything. -/
theorem eq_top_of_prod_trace_separating
    {W : Submodule ℂ (Matrix m m ℂ × Matrix n n ℂ)}
    (hSep : ∀ Δ : Matrix m m ℂ × Matrix n n ℂ,
      (∀ M ∈ W, Matrix.trace (Δ.1 * M.1) + Matrix.trace (Δ.2 * M.2) = 0) → Δ = 0) :
    W = ⊤ :=
  LinearMap.BilinForm.eq_top_of_forall_apply_eq_zero prodTraceForm_nondegenerate hSep

end Prod

end Matrix
