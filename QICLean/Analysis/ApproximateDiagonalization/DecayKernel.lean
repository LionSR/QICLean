/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Kernels under repeated square roots

The generic decay estimates used by Hastings's finite-dimensional spectral
refinement, arXiv:cond-mat/0508554v3, lines 1695–1708.
-/

namespace ApproximateDiagonalization

variable {ι : Type*}

/-- Successive square roots of a decay kernel. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1695–1708, with the cross terms retained. -/
noncomputable def sqrtKernel (k : ι → ι → ℝ) : ℕ → ι → ι → ℝ
  | 0 => k
  | n + 1 => fun i j => Real.sqrt (sqrtKernel k n i j)

@[simp]
theorem sqrtKernel_zero (k : ι → ι → ℝ) (i j : ι) : sqrtKernel k 0 i j = k i j := rfl

@[simp]
theorem sqrtKernel_succ (k : ι → ι → ℝ) (n : ℕ) (i j : ι) :
    sqrtKernel k (n + 1) i j = Real.sqrt (sqrtKernel k n i j) := rfl

theorem sqrtKernel_nonneg {k : ι → ι → ℝ} (hk : ∀ i j, 0 ≤ k i j) :
    ∀ n i j, 0 ≤ sqrtKernel k n i j
  | 0, i, j => hk i j
  | _ + 1, _, _ => Real.sqrt_nonneg _

theorem sqrtKernel_le_one {k : ι → ι → ℝ} (hk : ∀ i j, k i j ≤ 1) :
    ∀ n i j, sqrtKernel k n i j ≤ 1
  | 0, i, j => hk i j
  | n + 1, i, j => Real.sqrt_le_one.mpr (sqrtKernel_le_one hk n i j)

theorem sqrtKernel_symm {k : ι → ι → ℝ} (hk : ∀ i j, k i j = k j i) :
    ∀ n i j, sqrtKernel k n i j = sqrtKernel k n j i
  | 0, i, j => hk i j
  | n + 1, i, j => congrArg Real.sqrt (sqrtKernel_symm hk n i j)

theorem sqrtKernel_succ_sq {k : ι → ι → ℝ} (hk : ∀ i j, 0 ≤ k i j) (n : ℕ) (i j : ι) :
    sqrtKernel k (n + 1) i j ^ 2 = sqrtKernel k n i j :=
  Real.sq_sqrt (sqrtKernel_nonneg hk n i j)

theorem sqrtKernel_mono {k : ι → ι → ℝ} (hk0 : ∀ i j, 0 ≤ k i j)
    (hk1 : ∀ i j, k i j ≤ 1) (i j : ι) : Monotone fun n => sqrtKernel k n i j := by
  apply monotone_nat_of_le_succ
  intro n
  rw [sqrtKernel_succ]
  apply Real.le_sqrt_of_sq_le
  have h0 := sqrtKernel_nonneg hk0 n i j
  have h1 := sqrtKernel_le_one hk1 n i j
  nlinarith

/-- The multiplicative triangle inequality persists under taking square roots. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem sqrtKernel_mul_le {k : ι → ι → ℝ} (hk0 : ∀ i j, 0 ≤ k i j)
    (hmul : ∀ i j l, k i j * k j l ≤ k i l) :
    ∀ n i j l, sqrtKernel k n i j * sqrtKernel k n j l ≤ sqrtKernel k n i l
  | 0, i, j, l => hmul i j l
  | n + 1, i, j, l => by
      rw [sqrtKernel_succ, sqrtKernel_succ, sqrtKernel_succ,
        ← Real.sqrt_mul (sqrtKernel_nonneg hk0 n i j)]
      exact Real.sqrt_le_sqrt (sqrtKernel_mul_le hk0 hmul n i j l)

/-- The sum of a kernel over a finite list of selected terms, allowing repeated selections
at different spectral splits. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1695–1708. -/
def listKernelSum (k : ι → ι → ℝ) (s : List ι) (i : ι) : ℝ := (s.map (k i)).sum

@[simp]
theorem listKernelSum_nil (k : ι → ι → ℝ) (i : ι) : listKernelSum k [] i = 0 := rfl

@[simp]
theorem listKernelSum_cons (k : ι → ι → ℝ) (j : ι) (s : List ι) (i : ι) :
    listKernelSum k (j :: s) i = k i j + listKernelSum k s i := rfl

@[simp]
theorem listKernelSum_append (k : ι → ι → ℝ) (s t : List ι) (i : ι) :
    listKernelSum k (s ++ t) i = listKernelSum k s i + listKernelSum k t i := by
  simp only [listKernelSum, List.map_append, List.sum_append]

theorem listKernelSum_nonneg {k : ι → ι → ℝ} (hk : ∀ i j, 0 ≤ k i j)
    (s : List ι) (i : ι) : 0 ≤ listKernelSum k s i := by
  induction s with
  | nil => exact le_rfl
  | cons j s hs => exact add_nonneg (hk i j) hs

/-- Iterated square roots commute with restriction of a kernel along an anchor map.
Hastings, arXiv:cond-mat/0508554v3, lines 1698–1708. -/
theorem sqrtKernel_comp {α κ : Type*} (k : α → α → ℝ) (a : κ → α) (n : ℕ) (i j : κ) :
    sqrtKernel (fun i j ↦ k (a i) (a j)) n i j = sqrtKernel k n (a i) (a j) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sqrtKernel_succ, ih]


end ApproximateDiagonalization
