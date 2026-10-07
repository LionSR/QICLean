/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.TreeDerivative

/-!
# Block-diagonal inputs of finite mean trees

Fix an orthogonal decomposition `ℂ^n ⊕ ℂ^m` and write `X ⊕ Y` for the
block-diagonal matrix `fromBlocks X 0 0 Y`. The functional calculus, the weighted
geometric mean, and the roots of finite mean trees act blockwise on block-diagonal
inputs. The normalized derivative maps of a tree with block-diagonal inputs preserve
each of the four matrix blocks; on the first diagonal block they are the normalized
derivative maps of the tree of first diagonal blocks, so they do not depend on the
other diagonal block.

## Main definitions

* `Matrix.blockProj b` — the orthogonal projection onto the first (`b = true`) or the
  second (`b = false`) summand.
* `Matrix.IsBlockDiagonalMap L L₁ L₂` — `L` commutes with compression to each block and
  acts as `L₁` on the first and as `L₂` on the second diagonal block.

## Main results

* `Matrix.cfc_fromBlocks_diag`, `Matrix.rpow_fromBlocks_diag`,
  `Matrix.geomMean_fromBlocks_diag`, `Matrix.MeanTree.eval_fromBlocks_diag` — blockwise
  action of the functional calculus, the mean and the tree root.
* `Matrix.MeanTree.isBlockDiagonalMap_leafMap` — the block clause of area-law Lemma 7.2.
* `Matrix.IsBlockDiagonalMap.toBlocks₁₁` — the first diagonal block of `L H` is
  `L₁` applied to the first diagonal block of `H`.

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, Lemma 7.2 (`transport:cp`), lines 151--154 and
  173--176. The proofs are written independently from the paper.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Set MeasureTheory

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- **The functional calculus of a block-diagonal Hermitian matrix acts blockwise.** -/
theorem cfc_fromBlocks_diag {X : Matrix n n ℂ} {Y : Matrix m m ℂ} (hX : X.IsHermitian)
    (hY : Y.IsHermitian) (f : ℝ → ℝ) :
    cfc f (fromBlocks X 0 0 Y) = fromBlocks (cfc f X) 0 0 (cfc f Y) := by
  set U₁ : Matrix n n ℂ := (hX.eigenvectorUnitary : Matrix n n ℂ)
  set U₂ : Matrix m m ℂ := (hY.eigenvectorUnitary : Matrix m m ℂ)
  set W : Matrix (n ⊕ m) (n ⊕ m) ℂ := fromBlocks U₁ 0 0 U₂
  have hU₁ : star U₁ * U₁ = 1 := Unitary.coe_star_mul_self _
  have hU₂ : star U₂ * U₂ = 1 := Unitary.coe_star_mul_self _
  have hstarW : star W = fromBlocks (star U₁) 0 0 (star U₂) := by
    simp [W, star_eq_conjTranspose, fromBlocks_conjTranspose]
  have hWW : star W * W = 1 := by
    rw [hstarW, fromBlocks_multiply]; simp [hU₁, hU₂, fromBlocks_one]
  have hWW' : W * star W = 1 := mul_eq_one_comm.mp hWW
  let Wu : unitary (Matrix (n ⊕ m) (n ⊕ m) ℂ) := ⟨W, by
    rw [Unitary.mem_iff]; exact ⟨hWW, hWW'⟩⟩
  set g : n ⊕ m → ℝ := Sum.elim hX.eigenvalues hY.eigenvalues
  have hblock : ∀ (d₁ : n → ℝ) (d₂ : m → ℝ),
      W * diagonal (fun i ↦ ((Sum.elim d₁ d₂ i : ℝ) : ℂ)) * star W =
        fromBlocks (U₁ * diagonal (fun i ↦ (d₁ i : ℂ)) * star U₁) 0 0
          (U₂ * diagonal (fun i ↦ (d₂ i : ℂ)) * star U₂) := by
    intro d₁ d₂
    have hd : diagonal (fun i ↦ ((Sum.elim d₁ d₂ i : ℝ) : ℂ)) =
        fromBlocks (diagonal fun i ↦ (d₁ i : ℂ)) 0 0 (diagonal fun i ↦ (d₂ i : ℂ)) := by
      rw [fromBlocks_diagonal]; congr 1; ext i; cases i <;> rfl
    rw [hd, hstarW, fromBlocks_multiply, fromBlocks_multiply]
    simp
  have hXs : X = U₁ * diagonal (fun i ↦ (hX.eigenvalues i : ℂ)) * star U₁ := by
    conv_lhs => rw [hX.spectral_theorem]
    rfl
  have hYs : Y = U₂ * diagonal (fun i ↦ (hY.eigenvalues i : ℂ)) * star U₂ := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have hbd : fromBlocks X 0 0 Y = (Wu : Matrix (n ⊕ m) (n ⊕ m) ℂ) *
      diagonal (fun i ↦ (g i : ℂ)) * star (Wu : Matrix (n ⊕ m) (n ⊕ m) ℂ) := by
    rw [hblock, ← hXs, ← hYs]
  have hdh : (diagonal (fun i ↦ (g i : ℂ))).IsHermitian := by
    rw [IsHermitian, diagonal_conjTranspose]; congr 1; ext i; simp [Complex.conj_ofReal]
  rw [hbd, cfc_conj_unitary hdh f Wu, cfc_diagonal g f ((Set.finite_range g).continuousOn _)]
  change W * diagonal (fun i ↦ ((f (Sum.elim hX.eigenvalues hY.eigenvalues i) : ℝ) : ℂ)) *
    star W = _
  have hcomp : (fun i ↦ ((f (Sum.elim hX.eigenvalues hY.eigenvalues i) : ℝ) : ℂ)) =
      fun i ↦ ((Sum.elim (f ∘ hX.eigenvalues) (f ∘ hY.eigenvalues) i : ℝ) : ℂ) := by
    ext i; cases i <;> rfl
  rw [hcomp, hblock, hX.cfc_eq, hY.cfc_eq]
  rfl

set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
/-- A block-diagonal matrix with positive definite blocks is positive definite. -/
theorem PosDef.fromBlocks_diag {X : Matrix n n ℂ} {Y : Matrix m m ℂ} (hX : X.PosDef)
    (hY : Y.PosDef) : (fromBlocks X 0 0 Y).PosDef := by
  have := hX.isUnit.invertible
  have hpsd : (fromBlocks X 0 0 Y).PosSemidef := by
    have h := (PosDef.fromBlocks₁₁ (0 : Matrix n m ℂ) Y hX).mpr (by simpa using hY.posSemidef)
    simpa using h
  refine hpsd.posDef_iff_isUnit.mpr ?_
  rw [isUnit_iff_isUnit_det, det_fromBlocks_zero₁₂]
  exact (isUnit_iff_isUnit_det _ |>.mp hX.isUnit).mul (isUnit_iff_isUnit_det _ |>.mp hY.isUnit)

/-- **Real powers of block-diagonal positive definite matrices act blockwise.** -/
theorem rpow_fromBlocks_diag {X : Matrix n n ℂ} {Y : Matrix m m ℂ} (hX : X.PosDef)
    (hY : Y.PosDef) (r : ℝ) :
    (fromBlocks X 0 0 Y) ^ r = fromBlocks (X ^ r) 0 0 (Y ^ r) := by
  rw [CFC.rpow_eq_cfc_real (hX.fromBlocks_diag hY).posSemidef.nonneg,
    CFC.rpow_eq_cfc_real hX.posSemidef.nonneg, CFC.rpow_eq_cfc_real hY.posSemidef.nonneg]
  exact cfc_fromBlocks_diag hX.isHermitian hY.isHermitian _

/-- **The weighted geometric mean of block-diagonal inputs acts blockwise.** -/
theorem geomMean_fromBlocks_diag {A₁ B₁ : Matrix n n ℂ} {A₂ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef) (p : ℝ) :
    geomMean p (fromBlocks A₁ 0 0 A₂) (fromBlocks B₁ 0 0 B₂) =
      fromBlocks (geomMean p A₁ B₁) 0 0 (geomMean p A₂ B₂) := by
  unfold geomMean
  rw [rpow_fromBlocks_diag hA₁ hA₂, rpow_fromBlocks_diag hA₁ hA₂, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [rpow_fromBlocks_diag (hA₁.whiten hB₁) (hA₂.whiten hB₂), fromBlocks_multiply,
    fromBlocks_multiply]
  simp

namespace MeanTree

variable {ι : Type*}

/-- **The root of a tree with block-diagonal inputs is block diagonal**, with the roots
of the two trees of diagonal blocks. -/
theorem eval_fromBlocks_diag {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef) (T : MeanTree ι) :
    T.eval (fun i ↦ fromBlocks (A i) 0 0 (B i)) = fromBlocks (T.eval A) 0 0 (T.eval B) := by
  induction T with
  | leaf i => rfl
  | node p l r ihl ihr =>
    rw [eval_node, eval_node, eval_node, ihl, ihr]
    exact geomMean_fromBlocks_diag (posDef_eval hA l) (posDef_eval hB l) (posDef_eval hA r)
      (posDef_eval hB r) p

end MeanTree

/-! ### Maps preserving the block structure -/

/-- The orthogonal projections onto the two summands: `blockProj true = 1 ⊕ 0` and
`blockProj false = 0 ⊕ 1`. -/
def blockProj : Bool → Matrix (n ⊕ m) (n ⊕ m) ℂ
  | true => fromBlocks 1 0 0 0
  | false => fromBlocks 0 0 0 1

/-- A block-diagonal matrix commutes with the block projections. -/
theorem fromBlocks_diag_mul_blockProj (V₁ : Matrix n n ℂ) (V₂ : Matrix m m ℂ) (b : Bool) :
    fromBlocks V₁ 0 0 V₂ * blockProj b = blockProj b * fromBlocks V₁ 0 0 V₂ := by
  cases b <;> simp [blockProj, fromBlocks_multiply]

/-- A linear map on matrices over `n ⊕ m` **preserves the block structure** with diagonal
parts `L₁` and `L₂` if it commutes with compression to each of the four blocks, and acts
as `L₁` on the first diagonal block and as `L₂` on the second.

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 151--154. -/
structure IsBlockDiagonalMap (L : Matrix (n ⊕ m) (n ⊕ m) ℂ →L[ℂ] Matrix (n ⊕ m) (n ⊕ m) ℂ)
    (L₁ : Matrix n n ℂ →L[ℂ] Matrix n n ℂ) (L₂ : Matrix m m ℂ →L[ℂ] Matrix m m ℂ) : Prop where
  /-- Compression to each matrix block commutes with the map. -/
  compress : ∀ a b H, L (blockProj a * H * blockProj b) = blockProj a * L H * blockProj b
  /-- On the first diagonal block the map is `L₁`. -/
  first : ∀ Z, L (fromBlocks Z 0 0 0) = fromBlocks (L₁ Z) 0 0 0
  /-- On the second diagonal block the map is `L₂`. -/
  second : ∀ Z, L (fromBlocks 0 0 0 Z) = fromBlocks 0 0 0 (L₂ Z)

namespace IsBlockDiagonalMap

variable {L K : Matrix (n ⊕ m) (n ⊕ m) ℂ →L[ℂ] Matrix (n ⊕ m) (n ⊕ m) ℂ}
  {L₁ K₁ : Matrix n n ℂ →L[ℂ] Matrix n n ℂ} {L₂ K₂ : Matrix m m ℂ →L[ℂ] Matrix m m ℂ}

theorem comp (hL : IsBlockDiagonalMap L L₁ L₂) (hK : IsBlockDiagonalMap K K₁ K₂) :
    IsBlockDiagonalMap (L ∘L K) (L₁ ∘L K₁) (L₂ ∘L K₂) where
  compress a b H := by simp [hK.compress, hL.compress]
  first Z := by simp [hK.first, hL.first]
  second Z := by simp [hK.second, hL.second]

theorem add (hL : IsBlockDiagonalMap L L₁ L₂) (hK : IsBlockDiagonalMap K K₁ K₂) :
    IsBlockDiagonalMap (L + K) (L₁ + K₁) (L₂ + K₂) where
  compress a b H := by simp [hK.compress, hL.compress, Matrix.mul_add, Matrix.add_mul]
  first Z := by simp [hK.first, hL.first, fromBlocks_add]
  second Z := by simp [hK.second, hL.second, fromBlocks_add]

theorem smul (hL : IsBlockDiagonalMap L L₁ L₂) (c : ℝ) :
    IsBlockDiagonalMap (c • L) (c • L₁) (c • L₂) where
  compress a b H := by simp [hL.compress]
  first Z := by simp [hL.first, fromBlocks_smul]
  second Z := by simp [hL.second, fromBlocks_smul]

theorem zero : IsBlockDiagonalMap (0 : Matrix (n ⊕ m) (n ⊕ m) ℂ →L[ℂ] _)
    (0 : Matrix n n ℂ →L[ℂ] _) (0 : Matrix m m ℂ →L[ℂ] _) where
  compress a b H := by simp
  first Z := by simp
  second Z := by simp

theorem id : IsBlockDiagonalMap (ContinuousLinearMap.id ℂ (Matrix (n ⊕ m) (n ⊕ m) ℂ))
    (ContinuousLinearMap.id ℂ _) (ContinuousLinearMap.id ℂ _) where
  compress _ _ _ := rfl
  first _ := rfl
  second _ := rfl

/-- The first diagonal block of `L H` is `L₁` applied to the first diagonal block of `H`;
in particular it does not depend on the other blocks of `H`. -/
theorem toBlocks₁₁ (hL : IsBlockDiagonalMap L L₁ L₂) (H : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (L H).toBlocks₁₁ = L₁ H.toBlocks₁₁ := by
  have h1 : blockProj true * H * blockProj true = fromBlocks H.toBlocks₁₁ 0 0 0 := by
    conv_lhs => rw [← fromBlocks_toBlocks H]
    simp [blockProj, fromBlocks_multiply]
  have h2 := hL.compress true true H
  rw [h1, hL.first] at h2
  have h3 : blockProj true * L H * blockProj true = fromBlocks (L H).toBlocks₁₁ 0 0 0 := by
    conv_lhs => rw [← fromBlocks_toBlocks (L H)]
    simp [blockProj, fromBlocks_multiply]
  rw [h3] at h2
  exact (Matrix.fromBlocks_inj.mp h2).1.symm

/-- The second diagonal block of `L H` is `L₂` applied to the second diagonal block of
`H`. -/
theorem toBlocks₂₂ (hL : IsBlockDiagonalMap L L₁ L₂) (H : Matrix (n ⊕ m) (n ⊕ m) ℂ) :
    (L H).toBlocks₂₂ = L₂ H.toBlocks₂₂ := by
  have h1 : blockProj false * H * blockProj false = fromBlocks 0 0 0 H.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks H]
    simp [blockProj, fromBlocks_multiply]
  have h2 := hL.compress false false H
  rw [h1, hL.second] at h2
  have h3 : blockProj false * L H * blockProj false = fromBlocks 0 0 0 (L H).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (L H)]
    simp [blockProj, fromBlocks_multiply]
  rw [h3] at h2
  exact (Matrix.fromBlocks_inj.mp h2).2.2.2.symm

end IsBlockDiagonalMap

/-- Sandwiching by a block-diagonal matrix preserves the block structure. -/
theorem isBlockDiagonalMap_sandwichL (V₁ : Matrix n n ℂ) (V₂ : Matrix m m ℂ) :
    IsBlockDiagonalMap (sandwichL (fromBlocks V₁ 0 0 V₂)) (sandwichL V₁) (sandwichL V₂) where
  compress a b H := by
    simp only [sandwichL_apply]
    have ha := fromBlocks_diag_mul_blockProj V₁ V₂ a
    have hb := fromBlocks_diag_mul_blockProj V₁ V₂ b
    rw [show fromBlocks V₁ 0 0 V₂ * (blockProj a * H * blockProj b) * fromBlocks V₁ 0 0 V₂ =
        (fromBlocks V₁ 0 0 V₂ * blockProj a) * H * (blockProj b * fromBlocks V₁ 0 0 V₂) by
      noncomm_ring, ha, ← hb]
    noncomm_ring
  first Z := by simp [fromBlocks_multiply]
  second Z := by simp [fromBlocks_multiply]

/-- The embedding of the first diagonal block, `Z ↦ Z ⊕ 0`. -/
noncomputable def fromBlocks₁₁L : Matrix n n ℂ →L[ℂ] Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z ↦ fromBlocks Z 0 0 0
      map_add' := fun X Y ↦ by simp [fromBlocks_add]
      map_smul' := fun c X ↦ by simp [fromBlocks_smul] }

/-- The embedding of the second diagonal block, `Z ↦ 0 ⊕ Z`. -/
noncomputable def fromBlocks₂₂L : Matrix m m ℂ →L[ℂ] Matrix (n ⊕ m) (n ⊕ m) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun Z ↦ fromBlocks 0 0 0 Z
      map_add' := fun X Y ↦ by simp [fromBlocks_add]
      map_smul' := fun c X ↦ by simp [fromBlocks_smul] }

/-- Shifted inverses of a block-diagonal positive definite matrix are block diagonal. -/
theorem ringInverse_smul_one_add_fromBlocks {C₁ : Matrix n n ℂ} {C₂ : Matrix m m ℂ}
    (hC₁ : C₁.PosDef) (hC₂ : C₂.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    Ring.inverse (t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂) =
      fromBlocks (Ring.inverse (t • (1 : Matrix n n ℂ) + C₁)) 0 0
        (Ring.inverse (t • (1 : Matrix m m ℂ) + C₂)) := by
  have e : t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂ =
      fromBlocks (t • (1 : Matrix n n ℂ) + C₁) 0 0 (t • (1 : Matrix m m ℂ) + C₂) := by
    rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]; simp
  have hu₁ := (isStrictlyPositive_smul_one_add hC₁ ht).isUnit
  have hu₂ := (isStrictlyPositive_smul_one_add hC₂ ht).isUnit
  have hu : IsUnit (fromBlocks (t • (1 : Matrix n n ℂ) + C₁) 0 0
      (t • (1 : Matrix m m ℂ) + C₂)) := by
    rw [← e]
    exact (isStrictlyPositive_smul_one_add (hC₁.fromBlocks_diag hC₂) ht).isUnit
  rw [e, ← mul_one (Ring.inverse _), Ring.inverse_mul_eq_iff_eq_mul _ _ _ hu,
    fromBlocks_multiply]
  simp [Ring.mul_inverse_cancel _ hu₁, Ring.mul_inverse_cancel _ hu₂, fromBlocks_one]

/-- **The derivative of a real power at a block-diagonal matrix preserves the block
structure**, acting as the derivatives at the two diagonal blocks.

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex`
lines 173--175: all sandwich factors in the derivative integral are block diagonal. -/
theorem isBlockDiagonalMap_rpowFDeriv {C₁ : Matrix n n ℂ} {C₂ : Matrix m m ℂ}
    (hC₁ : C₁.PosDef) (hC₂ : C₂.PosDef) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    IsBlockDiagonalMap (rpowFDeriv p (fromBlocks C₁ 0 0 C₂)) (rpowFDeriv p C₁)
      (rpowFDeriv p C₂) := by
  have hC := hC₁.fromBlocks_diag hC₂
  have hR : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) →
      Ring.inverse (t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂) =
        fromBlocks (Ring.inverse (t • (1 : Matrix n n ℂ) + C₁)) 0 0
          (Ring.inverse (t • (1 : Matrix m m ℂ) + C₂)) := fun t ht ↦
    ringInverse_smul_one_add_fromBlocks hC₁ hC₂ (le_of_lt ht)
  have hint : ∀ H, IntegrableOn (fun t ↦ rpowFDerivIntegrand p (fromBlocks C₁ 0 0 C₂) t H)
      (Ioi 0) := fun H ↦ (integrableOn_rpowFDerivIntegrand hC hp).apply_continuousLinearMap H
  have hint₁ : ∀ H, IntegrableOn (fun t ↦ rpowFDerivIntegrand p C₁ t H) (Ioi 0) := fun H ↦
    (integrableOn_rpowFDerivIntegrand hC₁ hp).apply_continuousLinearMap H
  have hint₂ : ∀ H, IntegrableOn (fun t ↦ rpowFDerivIntegrand p C₂ t H) (Ioi 0) := fun H ↦
    (integrableOn_rpowFDerivIntegrand hC₂ hp).apply_continuousLinearMap H
  refine ⟨fun a b H ↦ ?_, fun Z ↦ ?_, fun Z ↦ ?_⟩
  · rw [rpowFDeriv_apply hC hp, rpowFDeriv_apply hC hp]
    have hcomm : ∀ t ∈ Ioi (0 : ℝ),
        t ^ p • (Ring.inverse (t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂) *
          (blockProj a * H * blockProj b) *
          Ring.inverse (t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂)) =
        ContinuousLinearMap.mulLeftRight ℂ _ (blockProj a) (blockProj b)
          (rpowFDerivIntegrand p (fromBlocks C₁ 0 0 C₂) t H) := by
      intro t ht
      rw [rpowFDerivIntegrand_apply, hR t ht, ContinuousLinearMap.mulLeftRight_apply,
        mul_smul_comm, smul_mul_assoc]
      congr 1
      have ha := fromBlocks_diag_mul_blockProj (Ring.inverse (t • (1 : Matrix n n ℂ) + C₁))
        (Ring.inverse (t • (1 : Matrix m m ℂ) + C₂)) a
      have hb := fromBlocks_diag_mul_blockProj (Ring.inverse (t • (1 : Matrix n n ℂ) + C₁))
        (Ring.inverse (t • (1 : Matrix m m ℂ) + C₂)) b
      rw [show ∀ R : Matrix (n ⊕ m) (n ⊕ m) ℂ, R * (blockProj a * H * blockProj b) * R =
          (R * blockProj a) * H * (blockProj b * R) from fun R ↦ by noncomm_ring, ha, ← hb]
      noncomm_ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcomm,
      ContinuousLinearMap.integral_comp_comm _ (hint H)]
    simp only [ContinuousLinearMap.mulLeftRight_apply, rpowFDerivIntegrand_apply, mul_smul_comm,
      smul_mul_assoc]
  · rw [rpowFDeriv_apply hC hp, rpowFDeriv_apply hC₁ hp]
    have hcomm : ∀ t ∈ Ioi (0 : ℝ),
        t ^ p • (Ring.inverse (t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂) *
          fromBlocks Z 0 0 0 *
          Ring.inverse (t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂)) =
        fromBlocks₁₁L (m := m) (rpowFDerivIntegrand p C₁ t Z) := by
      intro t ht
      rw [hR t ht, rpowFDerivIntegrand_apply]
      simp [fromBlocks₁₁L, fromBlocks_multiply, fromBlocks_smul]
    rw [setIntegral_congr_fun measurableSet_Ioi hcomm,
      ContinuousLinearMap.integral_comp_comm _ (hint₁ Z)]
    simp [fromBlocks₁₁L, fromBlocks_smul, rpowFDerivIntegrand_apply]
  · rw [rpowFDeriv_apply hC hp, rpowFDeriv_apply hC₂ hp]
    have hcomm : ∀ t ∈ Ioi (0 : ℝ),
        t ^ p • (Ring.inverse (t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂) *
          fromBlocks 0 0 0 Z *
          Ring.inverse (t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) + fromBlocks C₁ 0 0 C₂)) =
        fromBlocks₂₂L (n := n) (rpowFDerivIntegrand p C₂ t Z) := by
      intro t ht
      rw [hR t ht, rpowFDerivIntegrand_apply]
      simp [fromBlocks₂₂L, fromBlocks_multiply, fromBlocks_smul]
    rw [setIntegral_congr_fun measurableSet_Ioi hcomm,
      ContinuousLinearMap.integral_comp_comm _ (hint₂ Z)]
    simp [fromBlocks₂₂L, fromBlocks_smul, rpowFDerivIntegrand_apply]

/-- The derivative of a real power `0 ≤ p ≤ 1` at a block-diagonal matrix preserves the
block structure. -/
theorem isBlockDiagonalMap_rpowDeriv {C₁ : Matrix n n ℂ} {C₂ : Matrix m m ℂ}
    (hC₁ : C₁.PosDef) (hC₂ : C₂.PosDef) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    IsBlockDiagonalMap (rpowDeriv p (fromBlocks C₁ 0 0 C₂)) (rpowDeriv p C₁)
      (rpowDeriv p C₂) := by
  unfold rpowDeriv
  split_ifs with hp0 hp1
  · exact IsBlockDiagonalMap.zero
  · exact IsBlockDiagonalMap.id
  · exact isBlockDiagonalMap_rpowFDeriv hC₁ hC₂
      ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩

/-- The partial derivative of the mean in its second argument, at block-diagonal inputs,
preserves the block structure. -/
theorem isBlockDiagonalMap_geomMeanDerivRight {A₁ B₁ : Matrix n n ℂ} {A₂ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    IsBlockDiagonalMap (geomMeanDerivRight p (fromBlocks A₁ 0 0 A₂) (fromBlocks B₁ 0 0 B₂))
      (geomMeanDerivRight p A₁ B₁) (geomMeanDerivRight p A₂ B₂) := by
  have hw : (fromBlocks A₁ 0 0 A₂) ^ (-(1 / 2) : ℝ) * fromBlocks B₁ 0 0 B₂ *
      (fromBlocks A₁ 0 0 A₂) ^ (-(1 / 2) : ℝ) =
      fromBlocks (A₁ ^ (-(1 / 2) : ℝ) * B₁ * A₁ ^ (-(1 / 2) : ℝ)) 0 0
        (A₂ ^ (-(1 / 2) : ℝ) * B₂ * A₂ ^ (-(1 / 2) : ℝ)) := by
    rw [rpow_fromBlocks_diag hA₁ hA₂, fromBlocks_multiply, fromBlocks_multiply]; simp
  simp only [geomMeanDerivRight]
  rw [hw, rpow_fromBlocks_diag hA₁ hA₂, rpow_fromBlocks_diag hA₁ hA₂]
  have h1 := isBlockDiagonalMap_sandwichL (A₁ ^ (1 / 2 : ℝ)) (A₂ ^ (1 / 2 : ℝ))
  have h2 := isBlockDiagonalMap_rpowDeriv (hA₁.whiten hB₁) (hA₂.whiten hB₂) hp
  have h3 := isBlockDiagonalMap_sandwichL (A₁ ^ (-(1 / 2) : ℝ)) (A₂ ^ (-(1 / 2) : ℝ))
  exact IsBlockDiagonalMap.comp h1 (IsBlockDiagonalMap.comp h2 h3)

/-- The partial derivative of the mean in its first argument, at block-diagonal inputs,
preserves the block structure. -/
theorem isBlockDiagonalMap_geomMeanDerivLeft {A₁ B₁ : Matrix n n ℂ} {A₂ B₂ : Matrix m m ℂ}
    (hA₁ : A₁.PosDef) (hA₂ : A₂.PosDef) (hB₁ : B₁.PosDef) (hB₂ : B₂.PosDef) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    IsBlockDiagonalMap (geomMeanDerivLeft p (fromBlocks A₁ 0 0 A₂) (fromBlocks B₁ 0 0 B₂))
      (geomMeanDerivLeft p A₁ B₁) (geomMeanDerivLeft p A₂ B₂) :=
  isBlockDiagonalMap_geomMeanDerivRight hB₁ hB₂ hA₁ hA₂
    ⟨by linarith [hp.2], by linarith [hp.1]⟩

/-- Normalizing a block-preserving derivative map at block-diagonal matrices preserves the
block structure. -/
theorem IsBlockDiagonalMap.normalizedDerivMap {L : Matrix (n ⊕ m) (n ⊕ m) ℂ →L[ℂ] _}
    {L₁ : Matrix n n ℂ →L[ℂ] Matrix n n ℂ} {L₂ : Matrix m m ℂ →L[ℂ] Matrix m m ℂ}
    (hL : IsBlockDiagonalMap L L₁ L₂) (w : ℝ) {M₁ D₁ : Matrix n n ℂ} {M₂ D₂ : Matrix m m ℂ}
    (hM₁ : M₁.PosDef) (hM₂ : M₂.PosDef) (hD₁ : D₁.PosDef) (hD₂ : D₂.PosDef) :
    IsBlockDiagonalMap (Matrix.normalizedDerivMap L w (fromBlocks M₁ 0 0 M₂)
        (fromBlocks D₁ 0 0 D₂))
      (Matrix.normalizedDerivMap L₁ w M₁ D₁) (Matrix.normalizedDerivMap L₂ w M₂ D₂) := by
  simp only [Matrix.normalizedDerivMap]
  rw [rpow_fromBlocks_diag hM₁ hM₂, rpow_fromBlocks_diag hD₁ hD₂]
  have h1 := isBlockDiagonalMap_sandwichL (M₁ ^ (-(1 / 2) : ℝ)) (M₂ ^ (-(1 / 2) : ℝ))
  have h3 := isBlockDiagonalMap_sandwichL (D₁ ^ (1 / 2 : ℝ)) (D₂ ^ (1 / 2 : ℝ))
  exact (IsBlockDiagonalMap.comp h1 (IsBlockDiagonalMap.comp hL h3)).smul w⁻¹

namespace MeanTree

variable {ι : Type*} [DecidableEq ι] {A : ι → Matrix n n ℂ} {B : ι → Matrix m m ℂ}

/-- The derivative of the root of a tree with block-diagonal inputs preserves the block
structure, acting as the derivatives of the two trees of diagonal blocks. -/
theorem isBlockDiagonalMap_derivLabel (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (T : MeanTree ι) (j : ι) :
    IsBlockDiagonalMap (T.derivLabel (fun i ↦ fromBlocks (A i) 0 0 (B i)) j)
      (T.derivLabel A j) (T.derivLabel B j) := by
  induction T with
  | leaf i =>
    unfold derivLabel
    split_ifs
    · exact IsBlockDiagonalMap.id
    · exact IsBlockDiagonalMap.zero
  | node p l r ihl ihr =>
    unfold derivLabel
    rw [eval_fromBlocks_diag hA hB l, eval_fromBlocks_diag hA hB r]
    exact ((isBlockDiagonalMap_geomMeanDerivLeft (posDef_eval hA l) (posDef_eval hB l)
      (posDef_eval hA r) (posDef_eval hB r) p.2).comp ihl).add
      ((isBlockDiagonalMap_geomMeanDerivRight (posDef_eval hA l) (posDef_eval hB l)
        (posDef_eval hA r) (posDef_eval hB r) p.2).comp ihr)

/-- **Block structure of the normalized leaf maps.** If all inputs of a tree are block
diagonal for a fixed orthogonal decomposition, the leaf maps preserve each matrix block,
and on the first (second) diagonal block they are the leaf maps of the tree of first
(second) diagonal blocks; in particular they do not depend on the other diagonal block.

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 151--154 and
173--176. -/
theorem isBlockDiagonalMap_leafMap (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (T : MeanTree ι) (j : ι) :
    IsBlockDiagonalMap (T.leafMap (fun i ↦ fromBlocks (A i) 0 0 (B i)) j)
      (T.leafMap A j) (T.leafMap B j) := by
  unfold leafMap
  rw [eval_fromBlocks_diag hA hB T]
  exact (isBlockDiagonalMap_derivLabel hA hB T j).normalizedDerivMap _ (posDef_eval hA T)
    (posDef_eval hB T) (hA j) (hB j)

end MeanTree

end Matrix
