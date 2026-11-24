/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.ThreeRegion.Cut
import QICLean.Analysis.Norm.MatrixToEuclidean
import QICLean.Analysis.Norm.VectorPreparation
import QICLean.Algebra.PartialTrace
import QICLean.Algebra.Unitary.MatrixIsometryEntries

/-!
# Splitting data and the canonical map of a birth

Let `A ⊆ B` be regions of a system of sites, with the three regions `A`, `B \ A` and
`U = Bᶜ`. *Splitting data* are an isometry `V` from the configurations of `U` to `B_A × B_M`,
where `B_A` is the configuration space of `A` and `B_M` that of `B \ A` or of `U`, and unit
vectors `s` on `A × B_A` and `s'` on `(B \ A) × B_M`. Their error on a vector `Ω` is
`‖(1 ⊗ V) Ω - s ⊗ s'‖`, with `Ω` read in the coordinates `ManyBody.threeCutEquiv`. The
splitting lemma provides such data with error at most `√I_Ω(A : B \ A)`; it is a statement
about entropy and is not used here.

With `𝒱 = 1 ⊗ V` the canonical map of a birth is `𝐁 = 𝒱ᴴ (|s⟩⟨s| ⊗ 1) 𝒱`. For abstract
finite systems `T`, `E`, `U`, `B_T`, `B_E`, this file proves that it is a Hermitian contraction
with `‖(𝐁 - 1) ψ‖ ≤ ‖𝒱 ψ - s ⊗ s'‖`, factors it as an effect `Sᴴ 𝒱` followed by its adjoint,
where `S` prepares the single unit vector `s` on `T × B_T` (`Matrix.prepMatrix`), and shows that
it acts as the identity on `E`. On the configurations of the system the canonical map of
splitting data commutes with every operator supported in `B \ A`.

## Main definitions

* `ManyBody.birthKernel`, `ManyBody.birthEffect`: the map `⟨s| (1_T ⊗ V)` on `T × U`, and its
  extension by the identity on `E`.
* `ManyBody.birthOp`: the canonical map `𝐁` (`eq:birth-map`).
* `ManyBody.SplittingData`, `ManyBody.SplittingData.error`: splitting data and their error.
* `ManyBody.configBirthOp`: the canonical map of splitting data on the configurations.

## Main results

* `ManyBody.birthOp_eq`: `𝐁 = 𝒱ᴴ (S Sᴴ) 𝒱`.
* `ManyBody.norm_toLp_tensorPurification`: `s ⊗ s'` is a unit vector.
* `ManyBody.norm_birthOp_le_one`, `ManyBody.birthOp_isHermitian`,
  `ManyBody.norm_toEuclideanLin_birthOp_sub_le`.
* `ManyBody.birthOp_eq_submatrix`, `ManyBody.commute_birthOp`: `𝐁 = 1_E ⊗ Kᴴ K`.
* `ManyBody.norm_birthKernel_le_one`: the kernel `K` is a contraction.
* `ManyBody.norm_toEuclideanLin_configBirthOp_sub_le`, `ManyBody.commute_configBirthOp`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.4 `lem:splitting`,
  `05-frames.tex`, lines 352–365, and Lemma 6.5 `lem:birth` and its proof, lines 396–456.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace ManyBody

/-! ### The canonical map for abstract systems -/

section Abstract

variable {T E U BT BE : Type*} [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
  [Fintype U] [DecidableEq U] [Fintype BT] [DecidableEq BT] [Fintype BE] [DecidableEq BE]

omit [Fintype T] [DecidableEq T] [Fintype BT] [DecidableEq BT] in
/-- The preparation `S` of `s` on `T × B_T`, with its output read as `(T × E) × (B_T × B_E)`,
sends `s'` to `s ⊗ s'`. -/
theorem prepMatrix_prodProdProdComm_mulVec (s : T × BT → ℂ) (s' : E × BE → ℂ) :
    prepMatrix (Equiv.prodProdProdComm T E BT BE) (WithLp.toLp 2 s) *ᵥ s' =
      tensorPurification s s' := by
  ext x
  simp [mulVec, dotProduct, tensorPurification, ite_mul]

omit [DecidableEq T] [DecidableEq BT] in
/-- For a unit vector `s` the preparation `S` is an isometry. -/
private theorem conjTranspose_mul_prepMatrix_eq_one {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) :
    (prepMatrix (Equiv.prodProdProdComm T E BT BE) (WithLp.toLp 2 s))ᴴ *
      prepMatrix (Equiv.prodProdProdComm T E BT BE) (WithLp.toLp 2 s) = 1 := by
  rw [conjTranspose_mul_prepMatrix, EuclideanSpace.norm_toLp_eq_one_of_star_dotProduct hs]
  simp

omit [Fintype U] [DecidableEq U] [DecidableEq T] [DecidableEq BT] [DecidableEq E]
  [DecidableEq BE] in
/-- The product `s ⊗ s'` of two unit vectors is a unit vector. -/
theorem norm_toLp_tensorPurification {s : T × BT → ℂ} {s' : E × BE → ℂ}
    (hs : star s ⬝ᵥ s = 1) (hs' : star s' ⬝ᵥ s' = 1) :
    ‖(WithLp.toLp 2 (tensorPurification s s') : EuclideanSpace ℂ _)‖ = 1 := by
  classical
  have h : star (tensorPurification s s') ⬝ᵥ tensorPurification s s' = 1 := by
    rw [← prepMatrix_prodProdProdComm_mulVec,
      star_mulVec_dotProduct_mulVec_of_conjTranspose_mul_eq_one
        (conjTranspose_mul_prepMatrix_eq_one hs) s', hs']
  exact EuclideanSpace.norm_toLp_eq_one_of_star_dotProduct h

omit [DecidableEq BT] [DecidableEq BE] in
/-- The identity tensored with an isometry is a contraction. -/
private theorem norm_one_kronecker_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry) :
    ‖(1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V‖ ≤ 1 := by
  classical
  exact (l2_opNorm_one_kronecker_le V).trans hV.l2_opNorm_le_one

/-- The map `⟨s|_{T B_T} (1_T ⊗ V)` from `T × U` to `B_E`: apply `V` on `U` and contract `T`
and `B_T` with `⟨s|`.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 416–418. -/
def birthKernel (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) : Matrix BE (T × U) ℂ :=
  of fun b tu ↦ ∑ bt, star (s (tu.1, bt)) * V (bt, b) tu.2

/-- The effect `Sᴴ 𝒱 = (⟨s|_{T B_T} ⊗ 1_{E B_E}) (1_{TE} ⊗ V)`, with `S` the preparation of `s`
on `T × B_T`.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 416–419. -/
def birthEffect (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    Matrix (E × BE) ((T × E) × U) ℂ :=
  (prepMatrix (Equiv.prodProdProdComm T E BT BE) (WithLp.toLp 2 s))ᴴ *
    ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V)

/-- **The canonical map of a birth (`eq:birth-map`).**
`𝐁 = 𝒱ᴴ (|s⟩⟨s|_{T B_T} ⊗ 1_{E B_E}) 𝒱`, written as `(Sᴴ 𝒱)ᴴ (Sᴴ 𝒱)`.

Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 420–426. -/
def birthOp (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    Matrix ((T × E) × U) ((T × E) × U) ℂ :=
  (birthEffect V s)ᴴ * birthEffect V s

omit [Fintype U] [DecidableEq U] [DecidableEq BT] in
/-- **`eq:birth-map`.** `𝐁 = 𝒱ᴴ (S Sᴴ) 𝒱` with `𝒱 = 1_{TE} ⊗ V`. -/
theorem birthOp_eq (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    birthOp V s = ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V)ᴴ *
      (prepMatrix (Equiv.prodProdProdComm T E BT BE) (WithLp.toLp 2 s) *
        (prepMatrix (Equiv.prodProdProdComm T E BT BE) (WithLp.toLp 2 s))ᴴ) *
      ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) := by
  rw [birthOp, birthEffect, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

omit [Fintype U] [DecidableEq U] [DecidableEq BT] in
/-- The canonical map is Hermitian. -/
theorem birthOp_isHermitian (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    (birthOp (E := E) V s).IsHermitian := by
  rw [IsHermitian, birthOp, conjTranspose_mul, conjTranspose_conjTranspose]

omit [DecidableEq BT] in
/-- The effect `Sᴴ 𝒱` of a birth is a contraction. -/
theorem norm_birthEffect_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) : ‖birthEffect (E := E) V s‖ ≤ 1 := by
  classical
  have h : ‖(prepMatrix (Equiv.prodProdProdComm T E BT BE) (WithLp.toLp 2 s))ᴴ‖ ≤ 1 := by
    rw [l2_opNorm_conjTranspose]
    exact (norm_prepMatrix_le _ _).trans
      (EuclideanSpace.norm_toLp_eq_one_of_star_dotProduct hs).le
  exact l2_opNorm_mul_le_one _ _ h (norm_one_kronecker_le_one hV)

omit [DecidableEq BT] in
/-- **The canonical map is a contraction** (`05-frames.tex`, line 427). -/
theorem norm_birthOp_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) : ‖birthOp (E := E) V s‖ ≤ 1 := by
  classical
  have h := norm_birthEffect_le_one (E := E) hV hs
  have h' := h
  rw [← l2_opNorm_conjTranspose] at h'
  exact l2_opNorm_mul_le_one _ _ h' h

omit [DecidableEq BT] in
/-- **Reference error of the canonical map** (`05-frames.tex`, lines 427–433). For an isometry
`V`, a unit vector `s` and any `s'`, `‖(𝐁 - 1) ψ‖ ≤ ‖𝒱 ψ - s ⊗ s'‖`: with `Pr = S Sᴴ`,
`(𝐁 - 1) ψ = 𝒱ᴴ (Pr - 1) (𝒱 ψ - s ⊗ s')` because `Pr (s ⊗ s') = s ⊗ s'`. -/
theorem norm_toEuclideanLin_birthOp_sub_le {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) (s' : E × BE → ℂ)
    (ψ : EuclideanSpace ℂ ((T × E) × U)) :
    ‖toEuclideanLin (birthOp V s) ψ - ψ‖ ≤
      ‖toEuclideanLin ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) ψ -
        WithLp.toLp 2 (tensorPurification s s')‖ := by
  classical
  set 𝒱 := (1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V
  set S := prepMatrix (Equiv.prodProdProdComm T E BT BE) (WithLp.toLp 2 s)
  set Pr := S * Sᴴ
  set ζ : EuclideanSpace ℂ ((T × E) × (BT × BE)) := WithLp.toLp 2 (tensorPurification s s')
  have hS : Sᴴ * S = 1 := conjTranspose_mul_prepMatrix_eq_one hs
  have hiso : 𝒱ᴴ * 𝒱 = 1 :=
    IsIsometry.kronecker (1 : Matrix (T × E) (T × E) ℂ) V (by simp [IsIsometry]) hV
  have hζ : toEuclideanLin Pr ζ = ζ := by
    have h1 : Sᴴ *ᵥ tensorPurification s s' = s' := by
      rw [← prepMatrix_prodProdProdComm_mulVec, mulVec_mulVec, hS, one_mulVec]
    change WithLp.toLp 2 (Pr *ᵥ tensorPurification s s') = ζ
    rw [← mulVec_mulVec, h1, prepMatrix_prodProdProdComm_mulVec]
  have hproj : IsStarProjection Pr := by
    refine ⟨?_, ?_⟩
    · change Pr * Pr = Pr
      simp only [Pr, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Sᴴ, hS, Matrix.one_mul]
    · change star Pr = Pr
      simp only [Pr, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have hnorm : ‖Pr - 1‖ ≤ 1 := by
    rw [← norm_neg, neg_sub]
    exact hproj.one_sub.norm_le
  have hV' : ‖𝒱ᴴ‖ ≤ 1 := by
    rw [l2_opNorm_conjTranspose]
    exact norm_one_kronecker_le_one hV
  have key : toEuclideanLin (birthOp V s) ψ - ψ =
      toEuclideanLin 𝒱ᴴ (toEuclideanLin (Pr - 1) (toEuclideanLin 𝒱 ψ - ζ)) := by
    rw [map_sub (toEuclideanLin (Pr - 1)), map_sub toEuclideanLin Pr 1, LinearMap.sub_apply,
      LinearMap.sub_apply, hζ, toEuclideanLin_one_apply, toEuclideanLin_one_apply, sub_self,
      sub_zero, map_sub, ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply,
      birthOp_eq, ← toEuclideanLin_mul_apply, ← Matrix.mul_assoc, hiso,
      toEuclideanLin_one_apply]
  rw [key]
  refine (Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one hV' _).trans ?_
  exact Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one hnorm _

/-- The coordinates `((t, e), u) ↦ (e, (t, u))`, separating `E` from `T` and `U`. -/
def teuShuffle (T E U : Type*) : (T × E) × U ≃ E × (T × U) where
  toFun x := (x.1.2, (x.1.1, x.2))
  invFun y := ((y.2.1, y.1), y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype U] [DecidableEq U] [DecidableEq BT] in
/-- The effect `Sᴴ 𝒱` is the identity on `E` tensored with the kernel `⟨s| (1_T ⊗ V)` on
`T × U`. -/
theorem birthEffect_eq_submatrix (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    birthEffect (E := E) V s =
      ((1 : Matrix E E ℂ) ⊗ₖ birthKernel V s).submatrix id (teuShuffle T E U) := by
  ext ⟨e₀, b⟩ ⟨⟨t, e⟩, u⟩
  simp only [birthEffect, birthKernel, mul_apply, conjTranspose_apply, prepMatrix_apply,
    Equiv.prodProdProdComm_apply, of_apply, kroneckerMap_apply, one_apply, submatrix_apply, id,
    teuShuffle, Equiv.coe_fn_mk, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [apply_ite (star : ℂ → ℂ), star_zero, ite_mul, zero_mul, one_mul, ite_and]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset E)) (t := (Finset.univ : Finset BT))]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  by_cases he : e = e₀
  · subst he; simp
  · simp [Ne.symm he]

omit [Fintype U] [DecidableEq U] [DecidableEq BT] in
/-- **The canonical map acts as the identity on `E`.** In the coordinates `(e, (t, u))`,
`𝐁 = 1_E ⊗ (Kᴴ K)` with `K = ⟨s| (1_T ⊗ V)` the kernel on `T × U`.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 434–437. -/
theorem birthOp_eq_submatrix (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    birthOp (E := E) V s =
      ((1 : Matrix E E ℂ) ⊗ₖ ((birthKernel V s)ᴴ * birthKernel V s)).submatrix
        (teuShuffle T E U) (teuShuffle T E U) := by
  rw [birthOp, birthEffect_eq_submatrix, conjTranspose_submatrix,
    ← submatrix_mul _ _ _ _ _ Function.bijective_id, conjTranspose_kronecker, conjTranspose_one,
    ← mul_kronecker_mul, Matrix.one_mul]

omit [DecidableEq BT] [DecidableEq BE] in
/-- The kernel `K = ⟨s| (1_T ⊗ V)` of a birth is a contraction.

Polynomial-PEPS manuscript, proof of Lemma 6.5, `05-frames.tex`, lines 416–418. -/
theorem norm_birthKernel_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) : ‖birthKernel V s‖ ≤ 1 := by
  classical
  have h : birthKernel V s = reindex (Equiv.punitProd BE)
      ((Equiv.prodPUnit T).prodCongr (Equiv.refl U)) (birthEffect (E := Unit) V s) := by
    ext b ⟨t, u⟩
    rw [birthEffect_eq_submatrix]
    simp [teuShuffle]
  rw [h]
  exact (l2_opNorm_reindex_le _ _ _).trans (norm_birthEffect_le_one hV hs)

omit [Fintype T] [Fintype E] [DecidableEq E] [Fintype U] in
/-- An operator acting on `E` alone, `(1_T ⊗ R) ⊗ 1_U`, in the coordinates `(e, (t, u))`. -/
theorem one_kronecker_kronecker_one_eq_submatrix (R : Matrix E E ℂ) :
    ((1 : Matrix T T ℂ) ⊗ₖ R) ⊗ₖ (1 : Matrix U U ℂ) =
      (R ⊗ₖ (1 : Matrix (T × U) (T × U) ℂ)).submatrix (teuShuffle T E U) (teuShuffle T E U) := by
  ext ⟨⟨t, e⟩, u⟩ ⟨⟨t', e'⟩, u'⟩
  simp only [kroneckerMap_apply, one_apply, submatrix_apply, teuShuffle, Equiv.coe_fn_mk,
    Prod.mk.injEq]
  by_cases ht : t = t' <;> by_cases hu : u = u' <;> simp [ht, hu]

omit [DecidableEq BT] in
/-- The canonical map commutes with every operator acting on `E` alone. -/
theorem commute_birthOp (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) (R : Matrix E E ℂ) :
    Commute (((1 : Matrix T T ℂ) ⊗ₖ R) ⊗ₖ (1 : Matrix U U ℂ)) (birthOp V s) := by
  classical
  rw [one_kronecker_kronecker_one_eq_submatrix, birthOp_eq_submatrix]
  refine Commute.submatrix_equiv ?_ _
  change _ * _ = _ * _
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one]

end Abstract

/-! ### Splitting data -/

section Splitting

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- **Splitting data** for regions `A ⊆ B`, with the three regions `A`, `B \ A` and `U = Bᶜ`
(Lemma 6.4 `lem:splitting`): an isometry `V` from the configurations of `U` to `B_A × B_M`,
where `B_A` is the configuration space of `A` and `B_M` that of `B \ A` or of `U`, and unit
vectors `s` on `A × B_A` and `s'` on `(B \ A) × B_M`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 352–365. -/
structure SplittingData (X : V → Type*) [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]
    (A B : Finset V) where
  /-- The isometry `V : H_U → B_A ⊗ B_M`. -/
  V : Matrix (RegionConfig X A × (RegionConfig X (B \ A) ⊕ ComplConfig X B))
    (ComplConfig X B) ℂ
  /-- The unit vector `s` on `A × B_A`. -/
  s : RegionConfig X A × RegionConfig X A → ℂ
  /-- The unit vector `s'` on `(B \ A) × B_M`. -/
  s' : RegionConfig X (B \ A) × (RegionConfig X (B \ A) ⊕ ComplConfig X B) → ℂ
  /-- `V` is an isometry. -/
  isIsometry : V.IsIsometry
  /-- `s` is a unit vector. -/
  star_s : star s ⬝ᵥ s = 1
  /-- `s'` is a unit vector. -/
  star_s' : star s' ⬝ᵥ s' = 1

variable {A B : Finset V} (hAB : A ⊆ B)

omit [Fintype V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- A vector on the configurations in the coordinates `ManyBody.threeCutEquiv`. -/
abbrev splitVec (Ω : EuclideanSpace ℂ (Config X)) :
    (RegionConfig X A × RegionConfig X (B \ A)) × ComplConfig X B → ℂ :=
  fun w ↦ Ω ((threeCutEquiv X hAB).symm w)

omit [∀ v, DecidableEq (X v)] in
/-- The coordinates of a unit vector in three-way cut coordinates form a unit vector. -/
theorem star_splitVec_dotProduct_splitVec {Ω : EuclideanSpace ℂ (Config X)} (hΩ : ‖Ω‖ = 1) :
    star (splitVec hAB Ω) ⬝ᵥ splitVec hAB Ω = 1 := by
  rw [← EuclideanSpace.star_dotProduct_self_eq_one_of_norm_eq_one hΩ]
  exact (threeCutEquiv X hAB).symm.sum_comp fun x ↦ star (Ω x) * Ω x

/-- The splitting error `‖(1 ⊗ V) Ω - s ⊗ s'‖` of splitting data on a vector, read in the
coordinates `ManyBody.threeCutEquiv`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 352–365. -/
def SplittingData.error (σ : SplittingData X A B) (Ω : EuclideanSpace ℂ (Config X)) : ℝ :=
  ‖(WithLp.toLp 2 ((((1 : Matrix (RegionConfig X A × RegionConfig X (B \ A))
      (RegionConfig X A × RegionConfig X (B \ A)) ℂ) ⊗ₖ σ.V) *ᵥ splitVec hAB Ω) -
      tensorPurification σ.s σ.s') : EuclideanSpace ℂ _)‖

/-! ### The canonical map on the configurations -/

/-- The canonical map `𝐁 = 𝒱ᴴ (|s⟩⟨s|_{A B_A} ⊗ 1_{(B \ A) B_M}) 𝒱` of splitting data, on the
configurations of the system (`eq:birth-map`).

Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 414–426. -/
def configBirthOp (σ : SplittingData X A B) : Matrix (Config X) (Config X) ℂ :=
  (birthOp (E := RegionConfig X (B \ A)) σ.V σ.s).submatrix (threeCutEquiv X hAB)
    (threeCutEquiv X hAB)

/-- The canonical map of splitting data is supported outside the middle region.
In the coordinates `(e, (t, u))` it acts as the identity on `e`.
Source: polynomial-PEPS, proof of Lemma 6.5, `05-frames.tex`, lines 434–437. -/
theorem isSupportedOn_configBirthOp (σ : SplittingData X A B) :
    IsSupportedOn (configBirthOp hAB σ) (B \ A)ᶜ := by
  classical
  constructor
  · intro x y h
    obtain ⟨v, hv, hxy⟩ := h
    have hm : v ∈ B \ A := by simpa using hv
    have hne : (threeCutEquiv X hAB x).1.2 ≠ (threeCutEquiv X hAB y).1.2 :=
      fun he ↦ hxy (congrFun he ⟨v, hm⟩)
    simp only [configBirthOp, birthOp_eq_submatrix, submatrix_apply, kroneckerMap_apply]
    change (1 : Matrix (RegionConfig X (B \ A)) (RegionConfig X (B \ A)) ℂ)
      (threeCutEquiv X hAB x).1.2 (threeCutEquiv X hAB y).1.2 * _ = 0
    rw [one_apply_ne hne, zero_mul]
  · intro x y x' y' hx hy hxy hxy'
    have hmid {a b : Config X} (h : ∀ v ∉ (B \ A)ᶜ, a v = b v) :
        (threeCutEquiv X hAB a).1.2 = (threeCutEquiv X hAB b).1.2 :=
      funext fun v ↦ h v (fun hv ↦ (Finset.mem_compl.mp hv) v.2)
    have hout {a b : Config X} (h : ∀ v ∈ (B \ A)ᶜ, a v = b v) :
        (teuShuffle _ _ _ (threeCutEquiv X hAB a)).2 =
          (teuShuffle _ _ _ (threeCutEquiv X hAB b)).2 :=
      Prod.ext (funext fun v ↦ h v (by simp [v.2]))
        (funext fun v ↦ h v (by simp [v.2]))
    simp only [configBirthOp, birthOp_eq_submatrix, submatrix_apply, kroneckerMap_apply]
    rw [show (teuShuffle _ _ _ (threeCutEquiv X hAB x)).1 =
        (teuShuffle _ _ _ (threeCutEquiv X hAB y)).1 from hmid hxy,
      show (teuShuffle _ _ _ (threeCutEquiv X hAB x')).1 =
        (teuShuffle _ _ _ (threeCutEquiv X hAB y')).1 from hmid hxy',
      one_apply_eq, one_apply_eq, one_mul, one_mul, hout hx, hout hy]

/-- The canonical map of splitting data is Hermitian. -/
theorem configBirthOp_isHermitian (σ : SplittingData X A B) :
    (configBirthOp hAB σ).IsHermitian :=
  (birthOp_isHermitian σ.V σ.s).submatrix _

/-- The canonical map of splitting data is a contraction. -/
theorem norm_configBirthOp_le_one (σ : SplittingData X A B) : ‖configBirthOp hAB σ‖ ≤ 1 :=
  (norm_submatrix_equiv_le _ _).trans (norm_birthOp_le_one σ.isIsometry σ.star_s)

/-- `‖(𝐁 - 1) Ω‖` is at most the splitting error `‖𝒱 Ω - s ⊗ s'‖`
(`05-frames.tex`, lines 427–433). -/
theorem norm_toEuclideanLin_configBirthOp_sub_le (σ : SplittingData X A B)
    (Ω : EuclideanSpace ℂ (Config X)) :
    ‖toEuclideanLin (configBirthOp hAB σ) Ω - Ω‖ ≤ σ.error hAB Ω := by
  rw [configBirthOp, norm_toEuclideanLin_submatrix_apply_sub]
  exact norm_toEuclideanLin_birthOp_sub_le σ.isIsometry σ.star_s σ.s' _

/-- The canonical map of splitting data commutes with every operator supported in `B \ A`
(`05-frames.tex`, lines 434–437). -/
theorem commute_configBirthOp (σ : SplittingData X A B) {D : Finset V} (hD : D ⊆ B \ A)
    {R : Matrix (Config X) (Config X) ℂ} (hR : R ∈ supportedOperators X D) :
    Commute (configBirthOp hAB σ) R := by
  obtain ⟨R', hR'⟩ := exists_reindex_threeCutEquiv_eq_one_kronecker_kronecker_one hAB hD hR
  have hR₀ : R = (reindex (threeCutEquiv X hAB) (threeCutEquiv X hAB) R).submatrix
      (threeCutEquiv X hAB) (threeCutEquiv X hAB) := by
    simp [reindex_apply]
  rw [hR₀, hR']
  exact Commute.submatrix_equiv (Commute.symm (commute_birthOp σ.V σ.s R')) _

end Splitting

end ManyBody
