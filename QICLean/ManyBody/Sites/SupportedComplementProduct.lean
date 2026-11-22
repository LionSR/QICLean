/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Projection.DetectabilityLemma
import QICLean.ManyBody.Sites.Support
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Support of ordered complementary products

For operators `h_k`, the ordered product `(1 - h_{n-1}) ⋯ (1 - h_0)` of their complements
(`ContinuousLinearMap.complementProd`) is supported on every region on which all the `h_k` are
supported. No commutativity, projection or positivity assumption is needed. This is the support
argument for the regional parity products in ALVV, arXiv:1602.08828v2, `thm:FF-tH`,
lines 1543–1568.

Moved from TNLean, `TNLean/Circuit/SupportedComplementProduct.lean` at commit `49b78ed821`
(Apache-2.0). Changes: any finite set of sites with any basis at every site, in place of one
local dimension `q`.
-/

open ManyBody

namespace QuantumCircuit

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

local notation "T" => Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Config X)

/-- An ordered complementary product belongs to the same supported-operator algebra as each
selected term. ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and
1543–1568. -/
theorem mem_supportedOperators_complementProd
    (h : ℕ → EuclideanSpace ℂ (Config X) →L[ℂ] EuclideanSpace ℂ (Config X))
    (S : Finset V) (n : ℕ)
    (hh : ∀ k, k < n → (T).symm (h k) ∈ supportedOperators X S) :
    (T).symm (ContinuousLinearMap.complementProd h n) ∈ supportedOperators X S := by
  induction n with
  | zero =>
    simpa only [ContinuousLinearMap.complementProd_zero, map_one] using
      (one_mem (supportedOperators X S))
  | succ n ih =>
    rw [ContinuousLinearMap.complementProd_succ, map_mul, map_sub, map_one]
    exact mul_mem
      (sub_mem (one_mem (supportedOperators X S))
        (hh n (Nat.lt_succ_self n))) (ih fun k hk ↦ hh k (Nat.lt_succ_of_lt hk))

end QuantumCircuit
