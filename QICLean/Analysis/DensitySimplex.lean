/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Necessary conditions for a regularized density simplex

The first-order conditions are deduced from an actual minimum on the probability
simplex. The concrete application is a single diagonal regularized filter. This
is the last-filter case of the patch argument; no identity for a noncommuting
ordered chain is asserted.

**Scope restriction (last-filter case):** The concrete declarations describe
one diagonal filter. The descending trace argument needed for earlier factors
of the source's ordered chain is recorded in
`docs/paper-gaps/openai_peps_patch_stationarity_gap.tex`.

Source: OpenAI, polynomial PEPS manuscript, September 24, 2026,
`03-patches.tex`, equations `eq:patch-simplex-derivative`, `eq:patch-kkt`,
and `eq:patch-clipped-eigenvalues`, lines 170–200, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently written from the mathematical manuscript; no upstream Lean proof
text is reused.
-/

/-!
## Original proof provenance

Source: September 24, 2026,
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex
Labels: eq:patch-variational-problem, eq:patch-simplex-derivative,
eq:patch-kkt, eq:patch-clipped-eigenvalues.
Independently formalized; no upstream Lean proof text reused.

Provenance-ID: 8767-density-simplex-01
Downstream declaration: Entropy.simplex_ratio_conditions_of_isMinOn

Provenance-ID: 8767-density-simplex-02
Downstream declaration: Entropy.simplexFilterObjective

Provenance-ID: 8767-density-simplex-03
Downstream declaration: Entropy.normalizedFilterWeights

Provenance-ID: 8767-density-simplex-04
Downstream declaration: Entropy.hasFDerivAt_simplexFilterObjective

Provenance-ID: 8767-density-simplex-05
Downstream declaration: Entropy.simplexFilterObjective_pos

Provenance-ID: 8767-density-simplex-06
Downstream declaration: Entropy.normalizedFilterWeights_nonneg

Provenance-ID: 8767-density-simplex-07
Downstream declaration: Entropy.sum_normalizedFilterWeights

Provenance-ID: 8767-density-simplex-08
Downstream declaration: Entropy.normalizedFilterWeights_clipped_of_isMinOn
-/

open scoped BigOperators
open Set

namespace Entropy

variable {ι : Type*} [Fintype ι]

/-- A genuine minimum with the regularized simplex derivative satisfies the
clipped eigenvalue equation. Source: OpenAI `03-patches.tex`, lines 170–200,
`eq:patch-kkt` and `eq:patch-clipped-eigenvalues`. -/
theorem simplex_ratio_conditions_of_isMinOn
    {x p : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1)
    (hp : ∀ i, 0 ≤ p i) (hsp : ∑ i, p i = 1)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    {f : (ι → ℝ) → ℝ} {f' : (ι → ℝ) →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x)
    (hd : ∀ v, f' v = -c * ∑ i, p i / (x i + b) * v i)
    (hm : IsMinOn f {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} x) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      (∀ i, p i / (x i + b) ≤ lam) ∧
      (∀ i, 0 < x i → p i / (x i + b) = lam) ∧
      (∀ i, x i + b = max (p i / lam) b) := by
  classical
  let lam := ∑ i, p i / (x i + b) * x i
  have hconv : Convex ℝ {y : ι → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} := by
    refine fun u hu v hv s t hs ht hst ↦ ⟨?_, ?_⟩
    · exact fun i ↦ add_nonneg (mul_nonneg hs (hu.1 i)) (mul_nonneg ht (hv.1 i))
    · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
        ← Finset.mul_sum, hu.2, hv.2, mul_one] using hst
  have hratio : ∀ i, p i / (x i + b) ≤ lam := by
    intro i
    have hvtx : (Pi.single i 1 : ι → ℝ) ∈
        {y | (∀ k, 0 ≤ y k) ∧ ∑ k, y k = 1} := by
      simp [Pi.single_apply, apply_ite]
    have hi := hm.isLocalMinOn.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hconv.segment_subset ⟨hx, hsx⟩ hvtx))
    simp only [hd, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hi
    nlinarith
  have hgap : ∑ i, (lam - p i / (x i + b)) * x i = 0 := by
    simp [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsx, lam]
  have hzero : ∀ i, (lam - p i / (x i + b)) * x i = 0 :=
    fun i ↦ (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ ↦ mul_nonneg (sub_nonneg.mpr (hratio k)) (hx k))).mp hgap i
      (Finset.mem_univ i)
  have heq : ∀ i, 0 < x i → p i / (x i + b) = lam :=
    fun i hi ↦ (sub_eq_zero.mp ((mul_eq_zero.mp (hzero i)).resolve_right hi.ne')).symm
  have hpos : 0 < lam := by
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ ↦ hp i)).mp (hsp.symm ▸ zero_lt_one)
    exact (div_pos hi (add_pos_of_nonneg_of_pos (hx i) hb)).trans_le (hratio i)
  have htotal : 1 = lam + b * ∑ i, p i / (x i + b) := by
    change 1 = (∑ i, p i / (x i + b) * x i) + b * ∑ i, p i / (x i + b)
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← hsp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    linear_combination -(div_mul_cancel₀ (p i) (add_pos_of_nonneg_of_pos (hx i) hb).ne')
  have hle : lam ≤ 1 := by
    have hs : 0 ≤ b * ∑ i, p i / (x i + b) :=
      mul_nonneg hb.le (Finset.sum_nonneg fun i _ ↦ div_nonneg (hp i)
        (add_nonneg (hx i) hb.le))
    linarith
  refine ⟨lam, hpos, hle, hratio, heq, ?_⟩
  intro i
  have hden : 0 < x i + b := add_pos_of_nonneg_of_pos (hx i) hb
  rcases (hx i).eq_or_lt with hi | hi
  · have hbnd : p i / lam ≤ b := (div_le_iff₀ hpos).mpr (by
      simpa [← hi, mul_comm] using (div_le_iff₀ hden).mp (hratio i))
    simp [← hi, max_eq_right hbnd]
  · have hpi : p i / lam = x i + b := (div_eq_iff hpos.ne').mpr (by
      simpa only [mul_comm] using (div_eq_iff hden.ne').mp (heq i hi))
    rw [hpi, max_eq_left (le_add_of_nonneg_left (hx i))]

/-- Squared norm of a single diagonal regularized filter with initial weights
`r`. Source: OpenAI `03-patches.tex`, `eq:patch-variational-problem` and
`eq:patch-simplex-derivative`. -/
noncomputable def simplexFilterObjective (r : ι → ℝ) (a b : ℝ) (y : ι → ℝ) : ℝ :=
  ∑ i, r i * (y i + b) ^ (-a)

/-- The actual normalized output weights of a single diagonal regularized
filter. Source: OpenAI `03-patches.tex`, lines 170–178. -/
noncomputable def normalizedFilterWeights (r : ι → ℝ) (a b : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  r i * (x i + b) ^ (-a) / simplexFilterObjective r a b x

/-- Differentiate the actual squared norm of the diagonal last filter.
Source: OpenAI `03-patches.tex`, `eq:patch-simplex-derivative`, lines 170–178. -/
theorem hasFDerivAt_simplexFilterObjective (r : ι → ℝ) (a b : ℝ) (x : ι → ℝ)
    (hxb : ∀ i, 0 < x i + b) :
    HasFDerivAt (simplexFilterObjective r a b)
      (∑ i, (r i * ((-a) * (x i + b) ^ (-a - 1))) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
  simpa [simplexFilterObjective, Finset.sum_apply, smul_smul, mul_assoc] using!
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
      (((hasFDerivAt_add_const_iff (f := fun y : ι → ℝ ↦ y i) (x := x) b).mpr
        (hasFDerivAt_apply i x)).rpow_const (p := -a)
        (Or.inl (hxb i).ne')).const_mul (r i))

/-- A nonzero initial probability weight gives a strictly positive filtered
squared norm. Source: OpenAI `03-patches.tex`, lines 68–99. -/
theorem simplexFilterObjective_pos {r x : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (hru : 0 < ∑ i, r i) (a : ℝ) {b : ℝ} (hb : 0 < b) (hx : ∀ i, 0 ≤ x i) :
    0 < simplexFilterObjective r a b x := by
  obtain ⟨i, hi, hri⟩ := (Finset.sum_pos_iff_of_nonneg (fun k _ ↦ hr k)).mp hru
  exact (Finset.sum_pos_iff_of_nonneg (fun k _ ↦ mul_nonneg (hr k)
    (Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos (hx k) hb) (-a)).le)).mpr
      ⟨i, hi, mul_pos hri (Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos (hx i) hb) (-a))⟩

/-- Normalized last-filter weights are nonnegative, allowing zero input weights.
Source: OpenAI `03-patches.tex`, lines 170–178. -/
theorem normalizedFilterWeights_nonneg {r x : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (hru : 0 < ∑ i, r i) (a : ℝ) {b : ℝ} (hb : 0 < b) (hx : ∀ i, 0 ≤ x i)
    (i : ι) : 0 ≤ normalizedFilterWeights r a b x i :=
  div_nonneg (mul_nonneg (hr i)
    (Real.rpow_pos_of_pos (add_pos_of_nonneg_of_pos (hx i) hb) (-a)).le)
    (simplexFilterObjective_pos hr hru a hb hx).le

/-- The actual normalized last-filter weights sum to one.
Source: OpenAI `03-patches.tex`, lines 170–178. -/
theorem sum_normalizedFilterWeights {r x : ι → ℝ} (hr : ∀ i, 0 ≤ r i)
    (hru : 0 < ∑ i, r i) (a : ℝ) {b : ℝ} (hb : 0 < b) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, normalizedFilterWeights r a b x i = 1 := by
  simpa only [normalizedFilterWeights, div_eq_mul_inv, ← Finset.sum_mul,
    simplexFilterObjective] using
    div_self (simplexFilterObjective_pos hr hru a hb hx).ne'

/-- Every genuine simplex minimizer of the diagonal last-filter squared norm
has the clipped spectrum of its actual normalized output weights. The positive
exponent is essential. Source: OpenAI `03-patches.tex`, `eq:patch-kkt` and
`eq:patch-clipped-eigenvalues`, lines 170–200. -/
theorem normalizedFilterWeights_clipped_of_isMinOn {r x : ι → ℝ}
    (hr : ∀ i, 0 ≤ r i) (hru : 0 < ∑ i, r i)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : ∀ i, 0 ≤ x i) (hsx : ∑ i, x i = 1)
    (hm : IsMinOn (simplexFilterObjective r a b)
      {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} x) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      (∀ i, normalizedFilterWeights r a b x i / (x i + b) ≤ lam) ∧
      (∀ i, 0 < x i → normalizedFilterWeights r a b x i / (x i + b) = lam) ∧
      (∀ i, x i + b = max (normalizedFilterWeights r a b x i / lam) b) := by
  have hF := simplexFilterObjective_pos hr hru a hb hx
  have hxb : ∀ i, 0 < x i + b := fun i ↦ add_pos_of_nonneg_of_pos (hx i) hb
  refine simplex_ratio_conditions_of_isMinOn hx hsx
    (normalizedFilterWeights_nonneg hr hru a hb hx)
    (sum_normalizedFilterWeights hr hru a hb hx) hb (mul_pos ha hF)
    (hasFDerivAt_simplexFilterObjective r a b x hxb) ?_ hm
  intro v
  simp only [sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Real.rpow_sub_one (hxb i).ne', normalizedFilterWeights]
  field_simp [hF.ne', (hxb i).ne']

end Entropy
