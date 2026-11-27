/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.ReverseBlockCriterion
import Lean.Elab.Command

/-!
Regression tests and strict transitive axiom guards for
`QICLean.Channel.Entanglement.ReverseBlockCriterion`.

Includes:
* genuinely non-real complex pure inputs `u`,
* genuinely rectangular maps (`Fin 3 → Fin 2`, and heterogeneous `Fin i.val → Fin (i.val + 1)`),
* a one-copy reverse-block test where `C + S` is provably NOT completely positive,
* an `N`-copy tensor-extension test where `S` is provably NOT completely positive,
* `N = 0` and empty-space boundary cases,
* strict transitive axiom checks allowing only `propext`, `Classical.choice`, `Quot.sound`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder
open Matrix

namespace ReverseBlockCriterionTest

/-! ### 1. Non-real pure input and rectangular CP pure-input vanishing (`Fin 3 → Fin 2`) -/

/-- A genuinely non-real complex vector in `ℂ^3`. -/
def uNonReal : Fin 3 → ℂ := ![1, Complex.I, 0]

theorem uNonReal_not_real : (uNonReal 1).im ≠ 0 := by
  simp [uNonReal]

/-- A `2 × 3` Kraus operator annihilating `uNonReal`. -/
def krausAnnih : Matrix (Fin 2) (Fin 3) ℂ :=
  !![Complex.I, -1, 0; 0, 0, 1]

/-- The rectangular CP map `X ↦ krausAnnih * X * krausAnnihᴴ` from `M_3(ℂ)` to `M_2(ℂ)`. -/
noncomputable def mapAnnih :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := krausAnnih * X * krausAnnihᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem mapAnnih_isKrausCP : IsKrausCP mapAnnih := by
  refine ⟨1, fun _ => krausAnnih, fun X => ?_⟩
  simp [mapAnnih]

theorem krausAnnih_mulVec_uNonReal : krausAnnih *ᵥ uNonReal = 0 := by
  ext i
  fin_cases i <;> simp [krausAnnih, uNonReal, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mapAnnih_uNonReal_eq_zero :
    mapAnnih (Matrix.vecMulVec uNonReal (star uNonReal)) = 0 := by
  change krausAnnih * Matrix.vecMulVec uNonReal (star uNonReal) * krausAnnihᴴ = 0
  rw [Matrix.mul_vecMulVec_mul_conjTranspose, krausAnnih_mulVec_uNonReal]
  ext i j
  simp [Matrix.vecMulVec_apply]

theorem rectangular_nonreal_pure_vanishing (z : Fin 3 → ℂ) :
    mapAnnih (Matrix.vecMulVec z (star uNonReal)) = 0 ∧
      mapAnnih (Matrix.vecMulVec uNonReal (star z)) = 0 :=
  ⟨mapAnnih_isKrausCP.map_vecMulVec_right_eq_zero mapAnnih_uNonReal_eq_zero z,
   mapAnnih_isKrausCP.map_vecMulVec_left_eq_zero mapAnnih_uNonReal_eq_zero z⟩

/-! ### 2. One-copy rectangular reverse-block criterion WITHOUT `IsKrausCP (C + S)` -/

/-- Projection `2 × 3` matrix picking out the first two coordinates. -/
def proj23 : Matrix (Fin 2) (Fin 3) ℂ :=
  Matrix.of fun i j => if i.castSucc = j then 1 else 0

@[simp]
private theorem proj23_mul_mul_conjTranspose (M : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 2) :
    (proj23 * M * proj23ᴴ) i j = M i.castSucc j.castSucc := by
  simp [proj23, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Rectangular transpose map `S(X) = proj23 * Xᵀ * proj23ᴴ` from `M_3(ℂ)` to `M_2(ℂ)`. -/
noncomputable def mapRectTranspose :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := proj23 * Xᵀ * proj23ᴴ
  map_add' X Y := by simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem mapRectTranspose_isCompletelyCopositive :
    IsCompletelyCopositiveMap mapRectTranspose := by
  refine ⟨1, fun _ => proj23, fun X => ?_⟩
  change proj23 * (Xᵀ)ᵀ * proj23ᴴ = _
  simp [Matrix.transpose_transpose]

/-- In the one-copy example `C = mapRectTranspose + mapAnnih`, `S = mapRectTranspose`,
`C + S = 2 • mapRectTranspose + mapAnnih` is NOT completely positive. -/
theorem oneCopy_add_not_isKrausCP :
    ¬ IsKrausCP ((mapRectTranspose + mapAnnih) + mapRectTranspose) := by
  intro hcp
  have hJ := (Matrix.isKrausCP_iff_rectangularChoi_posSemidef _).mp hcp
  let x : Fin 3 × Fin 2 → ℂ := fun p =>
    if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0
  have hnonneg : 0 ≤ star x ⬝ᵥ
      Matrix.rectangularChoi ((mapRectTranspose + mapAnnih) + mapRectTranspose) *ᵥ x :=
    hJ.dotProduct_mulVec_nonneg x
  have hval :
      star x ⬝ᵥ Matrix.rectangularChoi ((mapRectTranspose + mapAnnih) + mapRectTranspose) *ᵥ x =
        (-3 : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
      Fin.sum_univ_two, Matrix.rectangularChoi_apply, LinearMap.add_apply, Matrix.add_apply,
      mapRectTranspose, mapAnnih, LinearMap.coe_mk, AddHom.coe_mk, proj23, krausAnnih, x,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, Matrix.single_apply,
      Matrix.of_apply]
    norm_num
  rw [hval] at hnonneg
  have hre := (Complex.nonneg_iff.mp hnonneg).1
  norm_num at hre

/-- One-copy reverse-block positivity holds for `C = mapRectTranspose + mapAnnih` on the
non-real vector `uNonReal`, even though `C + S` is not completely positive. -/
theorem oneCopy_rectangular_nonreal_reverseBlock
    (v w : Fin 3 → ℂ) (hvw : v + w = uNonReal) :
    (Matrix.fromBlocks
      ((mapRectTranspose + mapAnnih) (Matrix.vecMulVec w (star w)))
      ((mapRectTranspose + mapAnnih) (Matrix.vecMulVec v (star w)))
      ((mapRectTranspose + mapAnnih) (Matrix.vecMulVec w (star v)))
      ((mapRectTranspose + mapAnnih) (Matrix.vecMulVec v (star v)))).PosSemidef := by
  have hsub : IsKrausCP ((mapRectTranspose + mapAnnih) - mapRectTranspose) := by
    simpa [add_sub_cancel_left] using mapAnnih_isKrausCP
  have hu :
      (mapRectTranspose + mapAnnih) (Matrix.vecMulVec uNonReal (star uNonReal)) =
        mapRectTranspose (Matrix.vecMulVec uNonReal (star uNonReal)) := by
    simp [LinearMap.add_apply, mapAnnih_uNonReal_eq_zero]
  exact reverseBlock_posSemidef hsub mapRectTranspose_isCompletelyCopositive hvw hu

/-! ### 3. Rectangular `N`-copy tensor extension with non-real `u` and non-CP `S` -/

/-- A non-real vector in `ℂ^3` supported on the third coordinate. -/
def uThird : Fin 3 → ℂ := ![0, 0, 1 + Complex.I]

theorem uThird_not_real : (uThird 2).im ≠ 0 := by
  simp [uThird]

/-- Rectangular map `C_tensor : M_3(ℂ) → M_2(ℂ)`:
`C(X) = (X 0 0 + X 1 1) • I₂ + X 2 2 • E_{0,0}`. -/
noncomputable def mapCTensor :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := (X 0 0 + X 1 1) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    X 2 2 • Matrix.single 0 0 (1 : ℂ)
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.add_apply, Matrix.smul_apply] <;> ring
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply] <;> ring

/-- Rectangular map `S_tensor : M_3(ℂ) → M_2(ℂ)`:
`S(X) = proj23 * Xᵀ * proj23ᴴ + X 2 2 • E_{0,0}`. -/
noncomputable def mapSTensor :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun X := proj23 * Xᵀ * proj23ᴴ + X 2 2 • Matrix.single 0 0 (1 : ℂ)
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    ring
  map_smul' c X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply]
    ring

theorem mapSTensor_isCompletelyCopositive : IsCompletelyCopositiveMap mapSTensor := by
  let K : Fin 2 → Matrix (Fin 2) (Fin 3) ℂ :=
    ![proj23, Matrix.of fun i j => if i = 0 ∧ j = 2 then 1 else 0]
  refine ⟨2, K, fun X => ?_⟩
  ext i j
  change ((proj23 * (Xᵀ)ᵀ * proj23ᴴ + (Xᵀ) 2 2 • Matrix.single 0 0 (1 : ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j =
    (∑ k : Fin 2, K k * X * (K k)ᴴ) i j
  rw [Matrix.transpose_transpose, Matrix.add_apply, proj23_mul_mul_conjTranspose,
    Matrix.sum_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [K, proj23, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.smul_apply]

theorem mapSTensor_not_isKrausCP : ¬ IsKrausCP mapSTensor := by
  intro hcp
  have hJ := (Matrix.isKrausCP_iff_rectangularChoi_posSemidef _).mp hcp
  let x : Fin 3 × Fin 2 → ℂ := fun p =>
    if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0
  have hnonneg : 0 ≤ star x ⬝ᵥ Matrix.rectangularChoi mapSTensor *ᵥ x :=
    hJ.dotProduct_mulVec_nonneg x
  have hval : star x ⬝ᵥ Matrix.rectangularChoi mapSTensor *ᵥ x = (-2 : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Fintype.sum_prod_type, Fin.sum_univ_three,
      Fin.sum_univ_two, Matrix.rectangularChoi_apply, mapSTensor, LinearMap.coe_mk, AddHom.coe_mk,
      proj23_mul_mul_conjTranspose, x, Matrix.transpose_apply, Matrix.single_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Fin.castSucc_zero, Fin.castSucc_one]
    norm_num
  rw [hval] at hnonneg
  have hre := (Complex.nonneg_iff.mp hnonneg).1
  norm_num at hre

theorem mapCTensor_add_mapSTensor_isKrausCP : IsKrausCP (mapCTensor + mapSTensor) := by
  let s : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)
  have hss : s * (starRingEnd ℂ) s = 2 := by
    simp [s, ← Complex.ofReal_mul]
  let K : Fin 4 → Matrix (Fin 2) (Fin 3) ℂ :=
    ![Matrix.of fun i j => if i = 0 ∧ j = 0 then s else 0,
      Matrix.of fun i j => if i = 1 ∧ j = 1 then s else 0,
      Matrix.of fun i j => if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else 0,
      Matrix.of fun i j => if i = 0 ∧ j = 2 then s else 0]
  refine ⟨4, K, fun X => ?_⟩
  ext i j
  rw [LinearMap.add_apply, Matrix.add_apply, Matrix.sum_apply, Fin.sum_univ_four]
  simp only [mapCTensor, mapSTensor, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply,
    proj23_mul_mul_conjTranspose]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, Matrix.single_apply,
      Matrix.one_apply, K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue] <;>
    norm_num
  · linear_combination -X 0 0 * hss - X 2 2 * hss
  · linear_combination -X 1 1 * hss

theorem mapCTensor_sub_mapSTensor_isKrausCP : IsKrausCP (mapCTensor - mapSTensor) := by
  let K : Fin 1 → Matrix (Fin 2) (Fin 3) ℂ :=
    ![Matrix.of fun i j => if i = 0 ∧ j = 1 then 1 else if i = 1 ∧ j = 0 then -1 else 0]
  refine ⟨1, K, fun X => ?_⟩
  ext i j
  rw [LinearMap.sub_apply, Matrix.sub_apply, Matrix.sum_apply, Fin.sum_univ_one]
  simp only [mapCTensor, mapSTensor, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply,
    proj23_mul_mul_conjTranspose]
  fin_cases i <;> fin_cases j <;>
    simp [K, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Fin.sum_univ_three]

theorem mapCTensor_eq_mapSTensor_uThird :
    mapCTensor (Matrix.vecMulVec uThird (star uThird)) =
      mapSTensor (Matrix.vecMulVec uThird (star uThird)) := by
  ext i j
  simp only [mapCTensor, mapSTensor, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply,
    proj23_mul_mul_conjTranspose]
  simp only [Matrix.transpose_apply, Matrix.vecMulVec_apply]
  fin_cases i <;> fin_cases j <;>
    simp [uThird, Matrix.smul_apply]

/-- Homogeneous `N`-copy reverse-block criterion for arbitrary `N : ℕ` on rectangular
`Fin 3 → Fin 2` maps and genuinely non-real `uThird`, with non-CP `S`. -/
theorem nCopy_rectangular_nonreal_reverseBlock
    (N : ℕ) (v w : (Fin N → Fin 3) → ℂ)
    (hvw : v + w = fun x => ∏ i : Fin N, uThird (x i)) :
    (Matrix.fromBlocks
      (Matrix.piTensorMap (fun _ : Fin N => mapCTensor) (Matrix.vecMulVec w (star w)))
      (Matrix.piTensorMap (fun _ : Fin N => mapCTensor) (Matrix.vecMulVec v (star w)))
      (Matrix.piTensorMap (fun _ : Fin N => mapCTensor) (Matrix.vecMulVec w (star v)))
      (Matrix.piTensorMap (fun _ : Fin N => mapCTensor) (Matrix.vecMulVec v (star v)))).PosSemidef :=
  piTensorMap_const_reverseBlock_posSemidef N
    mapCTensor_add_mapSTensor_isKrausCP
    mapCTensor_sub_mapSTensor_isKrausCP
    mapSTensor_isCompletelyCopositive
    mapCTensor_eq_mapSTensor_uThird
    hvw

/-! ### 4. Boundary cases: `N = 0` and empty local spaces -/

theorem zeroCopy_reverseBlock
    {α β : Fin 0 → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    (C S : (i : Fin 0) → Matrix (α i) (α i) ℂ →ₗ[ℂ] Matrix (β i) (β i) ℂ)
    (u : (i : Fin 0) → α i → ℂ)
    (v w : ((i : Fin 0) → α i) → ℂ)
    (hvw : v + w = fun x => ∏ i : Fin 0, u i (x i)) :
    (Matrix.fromBlocks
      (Matrix.piTensorMap C (Matrix.vecMulVec w (star w)))
      (Matrix.piTensorMap C (Matrix.vecMulVec v (star w)))
      (Matrix.piTensorMap C (Matrix.vecMulVec w (star v)))
      (Matrix.piTensorMap C (Matrix.vecMulVec v (star v)))).PosSemidef :=
  piTensorMap_reverseBlock_posSemidef C S
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) hvw

theorem emptyLocalSpace_reverseBlock
    (C S : (i : Fin 2) →
      Matrix (Fin i.val) (Fin i.val) ℂ →ₗ[ℂ] Matrix (Fin (i.val + 1)) (Fin (i.val + 1)) ℂ)
    (hadd : ∀ i, IsKrausCP (C i + S i))
    (hsub : ∀ i, IsKrausCP (C i - S i))
    (hcop : ∀ i, IsCompletelyCopositiveMap (S i))
    (u : (i : Fin 2) → Fin i.val → ℂ)
    (hu : ∀ i, C i (Matrix.vecMulVec (u i) (star (u i))) =
      S i (Matrix.vecMulVec (u i) (star (u i))))
    (v w : ((i : Fin 2) → Fin i.val) → ℂ)
    (hvw : v + w = fun x => ∏ i, u i (x i)) :
    (Matrix.fromBlocks
      (Matrix.piTensorMap C (Matrix.vecMulVec w (star w)))
      (Matrix.piTensorMap C (Matrix.vecMulVec v (star w)))
      (Matrix.piTensorMap C (Matrix.vecMulVec w (star v)))
      (Matrix.piTensorMap C (Matrix.vecMulVec v (star v)))).PosSemidef :=
  piTensorMap_reverseBlock_posSemidef C S hadd hsub hcop hu hvw

end ReverseBlockCriterionTest

-- Strict transitive axiom guard: reject any axiom outside {propext, Classical.choice, Quot.sound}.
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[
      ``Matrix.mul_vecMulVec_mul_conjTranspose,
      ``IsKrausCP.mulVec_eq_zero_of_map_vecMulVec_eq_zero,
      ``IsKrausCP.map_vecMulVec_right_eq_zero,
      ``IsKrausCP.map_vecMulVec_left_eq_zero,
      ``IsKrausCP.map_vecMulVec_eq_of_sub_isKrausCP,
      ``IsKrausCP.fromBlocks_posSemidef,
      ``IsCompletelyCopositiveMap.reverseBlock_vecMulVec_posSemidef,
      ``reverseBlock_vecMulVec_posSemidef,
      ``reverseBlock_posSemidef,
      ``Matrix.isKrausCP_iff_rectangularChoi_posSemidef,
      ``Matrix.piTensorMap_single,
      ``Matrix.piTensorMap_piKronecker,
      ``Matrix.piTensorMap_comp_transpose,
      ``Matrix.rectangularChoi_piTensorMap,
      ``Matrix.isKrausCP_piTensorMap,
      ``Matrix.isCompletelyCopositiveMap_piTensorMap,
      ``Matrix.isKrausCP_piTensorMap_add_sub,
      ``Matrix.vecMulVec_piProd_star,
      ``piTensorMap_reverseBlock_posSemidef,
      ``piTensorMap_const_reverseBlock_posSemidef,
      ``ReverseBlockCriterionTest.uNonReal_not_real,
      ``ReverseBlockCriterionTest.rectangular_nonreal_pure_vanishing,
      ``ReverseBlockCriterionTest.oneCopy_add_not_isKrausCP,
      ``ReverseBlockCriterionTest.oneCopy_rectangular_nonreal_reverseBlock,
      ``ReverseBlockCriterionTest.uThird_not_real,
      ``ReverseBlockCriterionTest.mapSTensor_not_isKrausCP,
      ``ReverseBlockCriterionTest.nCopy_rectangular_nonreal_reverseBlock,
      ``ReverseBlockCriterionTest.zeroCopy_reverseBlock,
      ``ReverseBlockCriterionTest.emptyLocalSpace_reverseBlock] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axs ← Lean.collectAxioms decl
    unless axs.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axs}"
    Lean.logInfo m!"{decl}: {axs}"
