/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity
import QICLean.Algebra.Word.OrderedProduct

/-!
# Kronecker powers of the matrix of a map, and traces of products of sums

For a constant family `u^{⊗N}` of the Kronecker product `Matrix.piKronecker`, when `u` is the
matrix of a map on basis labels, the Kronecker power acts on configurations by applying that map
at every site. The trace of an ordered product of linear combinations expands as a sum over
choice functions.

Moved from TNLean, `TNLean/Algebra/FinKronecker.lean` at commit `49b78ed821` (Apache-2.0).

## Main results

* `Matrix.piKronecker_mul_apply_of_eq_ite`, `Matrix.mul_piKronecker_apply_of_eq_ite`.
* `Matrix.trace_prod_ofFn_sum_smul`.
-/

open scoped Matrix BigOperators

namespace Matrix

section ConstantFamily

variable {N : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Left multiplication by the Kronecker power of the matrix of a map `f` moves the row
configuration along `f`. -/
theorem piKronecker_mul_apply_of_eq_ite {u : Matrix ι ι ℂ} {f : ι → ι}
    (hu : ∀ i j, u i j = if j = f i then 1 else 0) (B : Matrix (Fin N → ι) κ ℂ)
    (σ : Fin N → ι) (τ : κ) :
    ((piKronecker fun _ : Fin N => u) * B) σ τ = B (fun k => f (σ k)) τ := by
  simp only [mul_apply, piKronecker_apply, hu, Fintype.prod_boole, ← funext_iff, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Right multiplication by the Kronecker power of the transposed matrix of a map `g` moves
the column configuration along `g`. -/
theorem mul_piKronecker_apply_of_eq_ite {u : Matrix ι ι ℂ} {g : ι → ι}
    (hu : ∀ i j, u i j = if i = g j then 1 else 0) (B : Matrix κ (Fin N → ι) ℂ)
    (σ : κ) (τ : Fin N → ι) :
    (B * piKronecker fun _ : Fin N => u) σ τ = B σ (fun k => g (τ k)) := by
  simp only [mul_apply, piKronecker_apply, hu, Fintype.prod_boole, ← funext_iff, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end ConstantFamily

/-- Expansion of the trace of an ordered product of linear combinations: the trace of
`∏_l (∑_j f_{l j} B_{l j})` is the sum over choice functions `ch` of
`(∏_l f_{l, ch l}) tr(∏_l B_{l, ch l})`. -/
theorem trace_prod_ofFn_sum_smul {n J : Type*} [Fintype n] [DecidableEq n] [Fintype J] {L : ℕ}
    (f : Fin L → J → ℂ) (B : Fin L → J → Matrix n n ℂ) :
    trace ((List.ofFn fun l => ∑ j, f l j • B l j).prod) =
      ∑ ch : Fin L → J, (∏ l, f l (ch l)) * trace ((List.ofFn fun l => B l (ch l)).prod) := by
  rw [List.prod_ofFn_sum, trace_sum]
  refine Finset.sum_congr rfl fun ch _ => ?_
  rw [List.prod_ofFn_smul, trace_smul, smul_eq_mul]

end Matrix
