/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Placement

/-!
# Linear maps and traces against product operators

On a system of sites `V` with basis `X v` at the site `v`, the product operators `⊗_v m_v`
span all operators. Two linear maps on the operators therefore agree once they agree on the
product operators. For a product operator `σ = ⊗_v σ_v` and operators `A`, `B` supported on
disjoint regions, the traces factorize as `tr(σ A B) tr σ = tr(σ A) tr(σ B)`; no normalization
of the factors `σ_v` is assumed (with `tr σ_v = 1` this is `ManyBody.trace_piKronecker_mul_mul`).

Moved from TNLean, `TNLean/Circuit/SupportedOperators.lean`, restated on a system of sites
with any basis `X v` at the site `v` in place of one local dimension `Fin d`.

## Main results

* `ManyBody.linearMap_ext_piKronecker` — linear maps agreeing on the product operators are
  equal.
* `ManyBody.trace_piKronecker_mul_mul_mul_trace` — product operators factorize traces of
  products of operators supported on disjoint regions.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), Supplemental Material, proof of Theorem 1.
-/

open Matrix
open scoped BigOperators

namespace ManyBody

variable {V : Type*} [Fintype V] {X : V → Type*}

/-- Two linear maps on the operators of a system of sites agree once they agree on the product
operators `⊗_v m_v`. -/
theorem linearMap_ext_piKronecker [∀ v, Finite (X v)] {M : Type*} [AddCommMonoid M]
    [Module ℂ M] (Φ Ψ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] M)
    (h : ∀ m : (v : V) → Matrix (X v) (X v) ℂ, Φ (piKronecker m) = Ψ (piKronecker m)) :
    Φ = Ψ := by
  classical
  have : ∀ v, Fintype (X v) := fun v ↦ Fintype.ofFinite (X v)
  apply LinearMap.ext
  intro A
  have hA : A ∈ supportedOperators X Finset.univ := by simp
  induction hA using supportedOperators_induction with
  | prod m _ => exact h m
  | add A B _ _ hA hB => rw [map_add, map_add, hA, hB]
  | smul c A _ hA => rw [map_smul, map_smul, hA]

variable [DecidableEq V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- Product operators factorize traces of products of operators supported on disjoint regions:
`tr(σ A B) tr σ = tr(σ A) tr(σ B)` for `σ = ⊗_v σ_v`. -/
theorem trace_piKronecker_mul_mul_mul_trace {S S' : Finset V} (hSS' : Disjoint S S')
    (σ : (v : V) → Matrix (X v) (X v) ℂ) {A B : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X S) (hB : B ∈ supportedOperators X S') :
    trace (piKronecker σ * (A * B)) * trace (piKronecker σ) =
      trace (piKronecker σ * A) * trace (piKronecker σ * B) := by
  let φ := traceLinearMap (Config X) ℂ ℂ ∘ₗ LinearMap.mulLeft ℂ (piKronecker σ)
  rw [mul_comm]
  refine eq_of_mem_supportedOperators₂
    (trace (piKronecker σ) • (LinearMap.mul ℂ _).compr₂ φ)
    ((LinearMap.mul ℂ ℂ).compl₁₂ φ φ) (fun m m' hm hm' ↦ ?_) hA hB
  change trace (piKronecker σ) * trace (piKronecker σ * (piKronecker m * piKronecker m')) =
    trace (piKronecker σ * piKronecker m) * trace (piKronecker σ * piKronecker m')
  simp only [piKronecker_mul, trace_piKronecker, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ S
  · simp [hm' i (Finset.disjoint_left.mp hSS' hi), mul_comm]
  · simp [hm i hi]

end ManyBody
