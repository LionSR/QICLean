/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DetectabilityLemma

/-!
# Partitioning a commuting complementary product

A product of commuting complementary factors splits into the products
selected by a predicate and its complement. No projection hypothesis is
needed. This is the parity regrouping used in ALVV, arXiv:1602.08828v2,
`def:FF-tH` and `thm:FF-tH`, lines 1467–1487 and 1543–1550.
-/

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- A pairwise-commuting complementary product splits over a predicate
and its complement. The factors need not be projections. This is the
regrouping in ALVV, arXiv:1602.08828v2, `def:FF-tH` and `thm:FF-tH`,
lines 1467–1487 and 1543–1550. -/
theorem complementProd_partition
    {h : ℕ → E →L[𝕜] E} (hc : ∀ i j, Commute (h i) (h j))
    (s : ℕ → Prop) [DecidablePred s] (n : ℕ) :
    complementProd h n =
      complementProd (fun k ↦ if s k then h k else 0) n *
        complementProd (fun k ↦ if s k then 0 else h k) n := by
  induction n with
  | zero => simp only [complementProd_zero, one_mul]
  | succ n ih =>
    simp only [complementProd_succ, ih]
    by_cases hs : s n
    · simp only [ite_eq_left hs, sub_zero, one_mul, mul_assoc]
    · have hcP : Commute (h n)
          (complementProd (fun k ↦ if s k then h k else 0) n) :=
        commute_complementProd (fun j _ ↦ by
          split_ifs <;> first | exact hc n j | exact Commute.zero_right _)
      simpa only [ite_eq_right hs, sub_zero, one_mul, ← mul_assoc] using
        congrArg (fun A ↦ A * complementProd (fun k ↦ if s k then 0 else h k) n)
          ((Commute.one_left _).sub_left hcP).eq

end ContinuousLinearMap
