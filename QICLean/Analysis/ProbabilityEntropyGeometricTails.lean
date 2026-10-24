/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Ring.GeomSum
import QICLean.Analysis.ProbabilityEntropyRankTails

/-!
# Entropy from geometric rank tails

A finite probability distribution with geometric bounds on its mass beyond
geometric ranks has an explicit Shannon entropy bound. The proof applies the
finite rank-tail entropy estimate and sums a finite geometric progression.

## Main statements

* `Entropy.probabilityEntropy_le_of_geometricRankTailBounds`: the bound for a
  finite covering cutoff and geometric tail majorants.

## References

* AKLV, arXiv:1301.1162v1, entropy summation, lines 1059–1075.
* Hastings, arXiv:0705.2024v4, equations `constraint` and `constraint2`.
* ALVV, arXiv:1602.08828v2, proof of `thm:al-dg`.
-/

open scoped BigOperators

namespace Entropy

/-- A geometric bound on masses beyond geometric ranks gives a uniform
finite entropy estimate. The case `D = 1` is included.

Supporting entropy summation in AKLV, arXiv:1301.1162v1, lines 1059–1075;
Hastings, arXiv:0705.2024v4, equations constraint and constraint2; and ALVV,
arXiv:1602.08828v2, proof of thm:al-dg. This is a finite-probability
auxiliary, not the full source theorem. -/
theorem probabilityEntropy_le_of_geometricRankTailBounds
    {N : ℕ} (p : Fin N → ℝ) (a M D : ℕ) (θ : ℝ)
    (hp : ∀ b, 0 ≤ p b) (hsum : ∑ b, p b = 1)
    (hD : 1 ≤ D) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hcover : N ≤ D ^ (a + M))
    (htail : ∀ i < M,
      (∑ b ∈ Finset.univ.filter (fun b : Fin N ↦ D ^ (a + i) ≤ b.val), p b)
        ≤ θ ^ (i + 1)) :
    probabilityEntropy p ≤
      (a : ℝ) * Real.log (D : ℝ) +
        (Real.log 2 + θ * Real.log (D : ℝ)) / (1 - θ) := by
  classical
  have hDpos : 0 < D := lt_of_lt_of_le Nat.zero_lt_one hD
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hlogD : 0 ≤ Real.log (D : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hD)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  let s : ℝ := ∑ i ∈ Finset.range M, θ ^ (i + 1)
  have hgeom :
      s = θ * (∑ i ∈ Finset.range M, θ ^ i) := by
    dsimp [s]
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    ring
  have hgeom_product : s * (1 - θ) = θ * (1 - θ ^ M) := by
    rw [hgeom, mul_assoc, geom_sum_mul_neg]
  have hs : s ≤ θ / (1 - θ) := by
    apply (le_div_iff₀ hden).2
    rw [hgeom_product]
    have hn : 0 ≤ θ * θ ^ M := mul_nonneg hθ0 (pow_nonneg hθ0 M)
    nlinarith
  have hstart :
      Real.log (((D ^ (a + 0)) : ℕ) : ℝ) =
        (a : ℝ) * Real.log (D : ℝ) := by
    simp only [Nat.add_zero, Nat.cast_pow, Real.log_pow]
  have hratio (i : ℕ) :
      Real.log
          ((((D ^ (a + (i + 1))) : ℕ) : ℝ) /
            (((D ^ (a + i)) : ℕ) : ℝ)) =
        Real.log (D : ℝ) := by
    simp only [Nat.cast_pow]
    rw [Real.log_div (pow_ne_zero _ hDreal.ne') (pow_ne_zero _ hDreal.ne'),
      Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hweighted :
      (∑ i ∈ Finset.range M,
        θ ^ (i + 1) *
          Real.log
            ((((D ^ (a + (i + 1))) : ℕ) : ℝ) /
              (((D ^ (a + i)) : ℕ) : ℝ))) =
        s * Real.log (D : ℝ) := by
    simp_rw [hratio]
    exact (Finset.sum_mul (Finset.range M)
      (fun i ↦ θ ^ (i + 1)) (Real.log (D : ℝ))).symm
  have hbound := probabilityEntropy_le_of_rankTailBounds (M := M)
    p (fun i ↦ D ^ (a + i)) (fun i ↦ θ ^ (i + 1)) hp hsum
    (by simpa only [Nat.add_zero] using pow_pos hDpos a)
    (by
      intro i _hi
      exact pow_le_pow_right' hD (Nat.add_le_add_left (Nat.le_succ i) a))
    hcover htail
  change probabilityEntropy p ≤
    Real.log (((D ^ (a + 0)) : ℕ) : ℝ) + Real.log 2 * (1 + s) +
      (∑ i ∈ Finset.range M,
        θ ^ (i + 1) *
          Real.log
            ((((D ^ (a + (i + 1))) : ℕ) : ℝ) /
              (((D ^ (a + i)) : ℕ) : ℝ))) at hbound
  rw [hstart, hweighted] at hbound
  calc
    probabilityEntropy p ≤
        (a : ℝ) * Real.log (D : ℝ) + Real.log 2 * (1 + s) +
          s * Real.log (D : ℝ) := hbound
    _ = (a : ℝ) * Real.log (D : ℝ) + Real.log 2 +
        s * (Real.log 2 + Real.log (D : ℝ)) := by ring
    _ ≤ (a : ℝ) * Real.log (D : ℝ) + Real.log 2 +
        (θ / (1 - θ)) * (Real.log 2 + Real.log (D : ℝ)) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_right hs (add_nonneg hlog2 hlogD)) _
    _ = (a : ℝ) * Real.log (D : ℝ) +
        (Real.log 2 + θ * Real.log (D : ℝ)) / (1 - θ) := by
      field_simp [hden.ne']
      ring

end Entropy
