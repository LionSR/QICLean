/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RootChannel
import QICLean.Analysis.GlobalGap
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite words of square-root contractions

For positive contractions `k i` sharing a ground vector, chronological products of
`G i = √(1 - k i)` preserve the ground vector and its orthogonal complement. A gap
`∑ i, k i ≥ g (1 - |Ω⟩⟨Ω|)` gives a squared-norm bound summed over every word of a
fixed length. The estimate is obtained from the actual matrix products and their
one-step energy loss. No commutation between distinct factors is required.

This is the finite-word part of the excited-state estimate in the two-dimensional
area-law manuscript, `09-amplification.tex`, lines 237–253, source revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Identifying a probability
law with independent clocks is a separate assertion.
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- Chronological product, with the latest square-root factor acting on the left
(area-law manuscript, `09-amplification.tex`, lines 237–253). -/
noncomputable def contractionWord (k : ι → Matrix n n ℂ) :
    (m : ℕ) → (Fin m → ι) → Matrix n n ℂ
  | 0, _ => 1
  | m + 1, w => CFC.sqrt (1 - k (w (Fin.last m))) *
      contractionWord k m (fun j => w j.castSucc)

@[simp] theorem contractionWord_zero (k : ι → Matrix n n ℂ) (w : Fin 0 → ι) :
    contractionWord k 0 w = 1 := rfl

@[simp] theorem contractionWord_snoc (k : ι → Matrix n n ℂ) {m : ℕ}
    (w : Fin m → ι) (i : ι) :
    contractionWord k (m + 1) (Fin.snoc w i) =
      CFC.sqrt (1 - k i) * contractionWord k m w := by
  simp [contractionWord]

/-- Each square-root factor fixes any vector annihilated by its deficit. -/
theorem sqrt_one_sub_toEuclideanLin_eq_self {k : Matrix n n ℂ} (hk : k ≤ 1)
    {Ω : EuclideanSpace ℂ n} (hΩ : toEuclideanLin k Ω = 0) :
    toEuclideanLin (CFC.sqrt (1 - k)) Ω = Ω := by
  have hmul : k *ᵥ WithLp.ofLp Ω = 0 := by
    simpa using congrArg WithLp.ofLp hΩ
  apply WithLp.ofLp_injective
  exact sqrt_one_sub_mulVec_eq_self hk hmul

/-- The orthogonal complement of a common ground vector is preserved. -/
theorem inner_sqrt_one_sub_eq_zero {k : Matrix n n ℂ} (hk : k ≤ 1)
    {Ω v : EuclideanSpace ℂ n} (hΩ : toEuclideanLin k Ω = 0)
    (hv : ⟪Ω, v⟫_ℂ = 0) : ⟪Ω, toEuclideanLin (CFC.sqrt (1 - k)) v⟫_ℂ = 0 := by
  have hs := isSymmetric_toEuclideanLin_iff.mpr
    (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (1 - k))).isHermitian
  rw [← hs, sqrt_one_sub_toEuclideanLin_eq_self hk hΩ, hv]

/-- Exact squared-norm change at a square-root factor. -/
theorem norm_sq_sqrt_one_sub {k : Matrix n n ℂ} (hk : k ≤ 1)
    (v : EuclideanSpace ℂ n) :
    ‖toEuclideanLin (CFC.sqrt (1 - k)) v‖ ^ 2 =
      ‖v‖ ^ 2 - (⟪v, toEuclideanLin k v⟫_ℂ).re := by
  have hs := isSymmetric_toEuclideanLin_iff.mpr
    (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (1 - k))).isHermitian
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), hs, ← LinearMap.comp_apply, ← toLpLin_mul_same,
    CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hk)]
  simp [inner_sub_right, inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

variable [Fintype ι]

/-- Summing the exact losses and applying the operator gap gives the one-step estimate
from the area-law manuscript, `09-amplification.tex`, lines 237–253. -/
theorem sum_norm_sq_sqrt_one_sub_le (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω v : EuclideanSpace ℂ n} {g : ℝ}
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hv : ⟪Ω, v⟫_ℂ = 0) :
    ∑ i, ‖toEuclideanLin (CFC.sqrt (1 - k i)) v‖ ^ 2 ≤
      (Fintype.card ι - g) * ‖v‖ ^ 2 := by
  have hp : (∑ i, k i - (0 : ℂ) • 1 -
      (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
    simpa using nonneg_iff_posSemidef.mp (sub_nonneg.mpr hgap)
  have hg := hp.gap_le v
  simp only [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, zero_mul] at hg
  simp only [norm_sq_sqrt_one_sub (hk _), Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hsum : (⟪v, toEuclideanLin (∑ i, k i) v⟫_ℂ).re =
      ∑ i, (⟪v, toEuclideanLin (k i) v⟫_ℂ).re := by simp [inner_sum]
  rw [hsum] at hg
  nlinarith

/-- A gap larger than the number of terms forces the entire excited sector to vanish.
Thus no upper bound on the gap need be imposed in the final decay assertion. -/
theorem eq_zero_of_card_lt_gap (k : ι → Matrix n n ℂ) (hk : ∀ i, k i ≤ 1)
    {Ω v : EuclideanSpace ℂ n} {g : ℝ}
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hv : ⟪Ω, v⟫_ℂ = 0) (hg : (Fintype.card ι : ℝ) < g) : v = 0 := by
  have h := sum_norm_sq_sqrt_one_sub_le k hk hgap hv
  have hn : 0 ≤ ∑ i, ‖toEuclideanLin (CFC.sqrt (1 - k i)) v‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hz : ‖v‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖v‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

omit [Fintype ι] in
/-- Every chronological product preserves the common ground vector. -/
theorem contractionWord_fix (k : ι → Matrix n n ℂ) (hk : ∀ i, k i ≤ 1)
    {Ω : EuclideanSpace ℂ n} (hΩ : ∀ i, toEuclideanLin (k i) Ω = 0)
    (m : ℕ) (w : Fin m → ι) : toEuclideanLin (contractionWord k m w) Ω = Ω := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [contractionWord, toLpLin_mul_same, LinearMap.comp_apply, ih]
      exact sqrt_one_sub_toEuclideanLin_eq_self (hk _) (hΩ _)

omit [Fintype ι] in
/-- Every chronological product preserves the excited sector. -/
theorem inner_contractionWord_eq_zero (k : ι → Matrix n n ℂ) (hk : ∀ i, k i ≤ 1)
    {Ω v : EuclideanSpace ℂ n} (hΩ : ∀ i, toEuclideanLin (k i) Ω = 0)
    (hv : ⟪Ω, v⟫_ℂ = 0) (m : ℕ) (w : Fin m → ι) :
    ⟪Ω, toEuclideanLin (contractionWord k m w) v⟫_ℂ = 0 := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
      simp only [contractionWord, toLpLin_mul_same, LinearMap.comp_apply]
      exact inner_sqrt_one_sub_eq_zero (hk _) (hΩ _) (ih _)

/-- Sum of squared norms over all words of length `m`, before probability weights. -/
noncomputable def contractionWordSum (k : ι → Matrix n n ℂ) (m : ℕ)
    (v : EuclideanSpace ℂ n) : ℝ :=
  ∑ w : Fin m → ι, ‖toEuclideanLin (contractionWord k m w) v‖ ^ 2

@[simp] theorem contractionWordSum_zero (k : ι → Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    contractionWordSum k 0 v = ‖v‖ ^ 2 := by simp [contractionWordSum]

/-- The actual word sum splits into prefixes and final labels. -/
theorem contractionWordSum_succ (k : ι → Matrix n n ℂ) (m : ℕ)
    (v : EuclideanSpace ℂ n) :
    contractionWordSum k (m + 1) v =
      ∑ w : Fin m → ι, ∑ i, ‖toEuclideanLin (CFC.sqrt (1 - k i))
        (toEuclideanLin (contractionWord k m w) v)‖ ^ 2 := by
  unfold contractionWordSum
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (m + 1) => ι))
    (fun w => ‖toEuclideanLin (contractionWord k (m + 1) w) v‖ ^ 2)]
  change (∑ p : ι × (Fin m → ι),
    ‖toEuclideanLin (contractionWord k (m + 1) (Fin.snoc p.2 p.1)) v‖ ^ 2) = _
  simp only [Fintype.sum_prod_type, contractionWord_snoc, toLpLin_mul_same,
    LinearMap.comp_apply]
  rw [Finset.sum_comm]

/-- The finite word recurrence follows from the gap at each actual prefix vector. -/
theorem contractionWordSum_succ_le (k : ι → Matrix n n ℂ) (hk : ∀ i, k i ≤ 1)
    {Ω v : EuclideanSpace ℂ n} {g : ℝ} (hΩ : ∀ i, toEuclideanLin (k i) Ω = 0)
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hv : ⟪Ω, v⟫_ℂ = 0) (m : ℕ) :
    contractionWordSum k (m + 1) v ≤ (Fintype.card ι - g) * contractionWordSum k m v := by
  rw [contractionWordSum_succ, contractionWordSum, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => sum_norm_sq_sqrt_one_sub_le k hk hgap
    (inner_contractionWord_eq_zero k hk hΩ hv m w)

/-- Finite-word decay for a nonnegative recurrence coefficient. The complementary case
`g > card ι` is covered by `eq_zero_of_card_lt_gap`. -/
theorem contractionWordSum_le_pow (k : ι → Matrix n n ℂ) (hk : ∀ i, k i ≤ 1)
    {Ω v : EuclideanSpace ℂ n} {g : ℝ} (hΩ : ∀ i, toEuclideanLin (k i) Ω = 0)
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hg : g ≤ Fintype.card ι) (hv : ⟪Ω, v⟫_ℂ = 0) (m : ℕ) :
    contractionWordSum k m v ≤ (Fintype.card ι - g) ^ m * ‖v‖ ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        contractionWordSum k (m + 1) v ≤
            (Fintype.card ι - g) * contractionWordSum k m v :=
          contractionWordSum_succ_le k hk hΩ hgap hv m
        _ ≤ (Fintype.card ι - g) * ((Fintype.card ι - g) ^ m * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hg)
        _ = (Fintype.card ι - g) ^ (m + 1) * ‖v‖ ^ 2 := by rw [pow_succ]; ring

end Matrix
