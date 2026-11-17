/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.MatrixPowers
import Mathlib.Analysis.Convex.Jensen

/-!
# Joint convexity of quadratic perspectives

The Schur complement proves a finite weighted inequality for `Lᴴ * R⁻¹ * L`,
including a larger denominator than the weighted sum. Consequently a concave
positive definite denominator gives a jointly convex quadratic perspective.
Applying operator concavity of the real power gives Wolf's Corollary 5.4(1)
(the first corollary after Theorem 5.14), for every exponent in `[0, 1]`.
The numerator may be rectangular and need not be positive or Hermitian.

This proves the quadratic case of Theorem 5.14, not its general functional
calculus assertion. Inverse powers are used only on positive definite matrices,
as in that theorem's invertibility condition. See
`docs/paper-gaps/wolf_ch5_quadratic_perspective_domain.tex`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace Matrix

variable {m n ι : Type*} [Finite m] [Fintype n] [DecidableEq n]

/-- Finite weighted quadratic-perspective inequality, with a denominator that
majorizes the weighted denominators. This is the Schur-complement form of the
quadratic case of Wolf Theorem 5.14. The weights need not sum to one. -/
theorem sum_conjTranspose_inv_mul_le (s : Finset ι) (w : ι → ℝ)
    (L : ι → Matrix n m ℂ) (R : ι → Matrix n n ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hR : ∀ i ∈ s, (R i).PosDef)
    {S : Matrix n n ℂ} (hS : S.PosDef) (hle : ∑ i ∈ s, w i • R i ≤ S) :
    (∑ i ∈ s, w i • L i)ᴴ * S⁻¹ * (∑ i ∈ s, w i • L i) ≤
      ∑ i ∈ s, w i • ((L i)ᴴ * (R i)⁻¹ * L i) := by
  classical
  let := Fintype.ofFinite m
  have hblock (i : ι) (hi : i ∈ s) :
      (fromBlocks ((L i)ᴴ * (R i)⁻¹ * L i) (L i)ᴴ (L i) (R i)).PosSemidef := by
    let : Invertible (R i) := (hR i hi).isUnit.invertible
    simpa using (PosDef.fromBlocks₂₂ ((L i)ᴴ * (R i)⁻¹ * L i) (L i)ᴴ
      (hR i hi)).mpr (by simpa using (PosSemidef.zero : (0 : Matrix m m ℂ).PosSemidef))
  have hsum := posSemidef_sum s (fun i hi => (hblock i hi).smul (hw i hi))
  let P : Matrix n (m ⊕ n) ℂ := fun i => Sum.elim (fun _ => 0) (fun j => if i = j then 1 else 0)
  have hslack := (le_iff.mp hle).conjTranspose_mul_mul_same P
  have htotal := hsum.add hslack
  have heq :
      (∑ i ∈ s, w i • fromBlocks ((L i)ᴴ * (R i)⁻¹ * L i) (L i)ᴴ (L i) (R i)) +
        Pᴴ * (S - ∑ i ∈ s, w i • R i) * P =
      fromBlocks (∑ i ∈ s, w i • ((L i)ᴴ * (R i)⁻¹ * L i))
        (∑ i ∈ s, w i • L i)ᴴ (∑ i ∈ s, w i • L i) S := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [add_apply, Matrix.sum_apply, smul_apply, Matrix.mul_apply]
    all_goals simp [P, Matrix.conjTranspose, Matrix.transpose, Matrix.mul_apply, Matrix.sum_apply,
      sub_apply, smul_apply]
  rw [heq] at htotal
  let : Invertible S := hS.isUnit.invertible
  have h := (PosDef.fromBlocks₂₂ _ (∑ i ∈ s, w i • L i)ᴴ hS).mp
    (by simpa using htotal)
  exact le_iff.mpr (by simpa using h)

/-- Binary quadratic-perspective convexity with a concave denominator.
This allows arbitrary rectangular numerators, and includes zero weights. -/
theorem conjTranspose_inv_mul_le_of_concave
    (L₁ L₂ : Matrix n m ℂ) {R₁ R₂ S : Matrix n n ℂ}
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef) (hS : S.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hle : a • R₁ + b • R₂ ≤ S) :
    (a • L₁ + b • L₂)ᴴ * S⁻¹ * (a • L₁ + b • L₂) ≤
      a • (L₁ᴴ * R₁⁻¹ * L₁) + b • (L₂ᴴ * R₂⁻¹ * L₂) := by
  simpa [Fin.sum_univ_two] using sum_conjTranspose_inv_mul_le Finset.univ
    ![a, b] ![L₁, L₂] ![R₁, R₂]
    (by intro i _; fin_cases i <;> assumption)
    (by intro i _; fin_cases i <;> assumption) hS
    (by simpa [Fin.sum_univ_two] using hle)

/-- The quadratic case of Wolf Theorem 5.14: a concave positive definite
matrix-valued denominator gives a jointly operator convex perspective.
The parameter space may itself be a product of any number of matrix spaces. -/
theorem convexOn_quadraticPerspective {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {D : Set E} {g : E → Matrix n n ℂ} (hg : ConcaveOn ℝ D g)
    (hpos : ∀ x ∈ D, (g x).PosDef) :
    ConvexOn ℝ (Set.univ ×ˢ D)
      (fun p : Matrix n m ℂ × E => p.1ᴴ * (g p.2)⁻¹ * p.1) := by
  refine ⟨convex_univ.prod hg.1, ?_⟩
  intro x hx y hy a b ha hb hab
  exact conjTranspose_inv_mul_le_of_concave x.1 y.1 (hpos x.2 hx.2)
    (hpos y.2 hy.2) (hpos _ (hg.1 hx.2 hy.2 ha hb hab)) ha hb
    (hg.2 hx.2 hy.2 ha hb hab)

/-- The quadratic case of Wolf Theorem 5.14(2) with an affine numerator.
Both maps may depend on all components of the parameter space. -/
theorem convexOn_affine_quadraticPerspective
    {E : Type*} [AddCommGroup E] [Module ℝ E] {D : Set E}
    {g : E → Matrix n n ℂ} (hg : ConcaveOn ℝ D g)
    (hpos : ∀ x ∈ D, (g x).PosDef) (h : E →ᵃ[ℝ] Matrix n m ℂ) :
    ConvexOn ℝ D (fun x => (h x)ᴴ * (g x)⁻¹ * h x) := by
  refine ⟨hg.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh : h (a • x + b • y) = a • h x + b • h y := by
    simpa only [AffineMap.lineMap_apply_module, show 1 - b = a by linarith] using
      h.apply_lineMap x y b
  dsimp only
  rw [hh]
  exact conjTranspose_inv_mul_le_of_concave (h x) (h y) (hpos x hx) (hpos y hy)
    (hpos _ (hg.1 hx hy ha hb hab)) ha hb (hg.2 hx hy ha hb hab)

/-- Negative powers in Wolf Corollary 5.4(1) are ordinary inverses of positive
powers on the positive definite cone. -/
private theorem inv_rpow_eq_neg {R : Matrix n n ℂ} (hR : R.PosDef) (p : ℝ) :
    (R ^ p)⁻¹ = R ^ (-p) := by
  apply inv_eq_left_inv
  exact hR.rpow_neg_mul_rpow p

/-- Wolf Corollary 5.4(1), with arbitrary rectangular numerator:
`(L, R) ↦ Lᴴ R^(-p) L` is jointly operator convex for `p ∈ [0, 1]` and `R > 0`.
No positivity, Hermitian, or invertibility assumption is needed on `L`.

**Local fix (inverse domain):** The invertible denominator convention is recorded in
`docs/paper-gaps/wolf_ch5_quadratic_perspective_domain.tex`. -/
theorem conjTranspose_rpow_neg_mul_convex {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (L₁ L₂ : Matrix n m ℂ) {R₁ R₂ : Matrix n n ℂ}
    (hR₁ : R₁.PosDef) (hR₂ : R₂.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • L₁ + b • L₂)ᴴ * (a • R₁ + b • R₂) ^ (-p) * (a • L₁ + b • L₂) ≤
      a • (L₁ᴴ * R₁ ^ (-p) * L₁) + b • (L₂ᴴ * R₂ ^ (-p) * L₂) := by
  have hR : (a • R₁ + b • R₂).PosDef := by
    rcases eq_or_lt_of_le ha with ha0 | ha
    · have hb1 : b = 1 := by linarith
      simpa [← ha0, hb1] using hR₂
    · exact (hR₁.smul ha).add_posSemidef (hR₂.posSemidef.smul hb)
  have h := conjTranspose_inv_mul_le_of_concave L₁ L₂ (hR₁.rpow p) (hR₂.rpow p)
    (hR.rpow p) ha hb ((CFC.concaveOn_rpow hp).2 hR₁.posSemidef.nonneg
      hR₂.posSemidef.nonneg ha hb hab)
  simpa only [inv_rpow_eq_neg hR, inv_rpow_eq_neg hR₁, inv_rpow_eq_neg hR₂] using h

/-- Product-domain formulation of Wolf Corollary 5.4(1), including arbitrary
rectangular numerators and every exponent endpoint. -/
theorem convexOn_conjTranspose_rpow_neg_mul {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ConvexOn ℝ {q : Matrix n m ℂ × Matrix n n ℂ | q.2.PosDef}
      (fun q => q.1ᴴ * q.2 ^ (-p) * q.1) := by
  refine ⟨?_, ?_⟩
  · rw [convex_iff_forall_pos]
    intro x hx y hy a b ha hb _
    exact (hx.smul ha).add (hy.smul hb)
  · intro x hx y hy a b ha hb hab
    exact conjTranspose_rpow_neg_mul_convex hp x.1 y.1 hx hy ha hb hab

/-- Finite probability-mixture form of Wolf Corollary 5.4(1). -/
theorem sum_conjTranspose_rpow_neg_mul_le {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (s : Finset ι) (w : ι → ℝ) (L : ι → Matrix n m ℂ) (R : ι → Matrix n n ℂ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (hR : ∀ i ∈ s, (R i).PosDef) :
    (∑ i ∈ s, w i • L i)ᴴ * (∑ i ∈ s, w i • R i) ^ (-p) *
        (∑ i ∈ s, w i • L i) ≤
      ∑ i ∈ s, w i • ((L i)ᴴ * (R i) ^ (-p) * L i) := by
  classical
  let := Fintype.ofFinite m
  simpa only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd] using
    (convexOn_conjTranspose_rpow_neg_mul hp).map_sum_le (p := fun i => (L i, R i))
      hw hsum hR

end Matrix
