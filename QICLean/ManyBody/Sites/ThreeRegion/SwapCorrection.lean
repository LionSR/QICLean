/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.ThreeRegion.Birth
import QICLean.ManyBody.Sites.PairSwapPermutation

/-!
# Exchanging two copies of a system and the buffer correction

The exchange of Lemma 6.6 of the polynomial-PEPS manuscript works on two copies of a system of
sites. With splitting data for regions `A ⊆ B` (Lemma 6.4), an isometry `V` from the
configurations of `U = Bᶜ` to `B_A ⊗ B_M` and unit vectors `s`, `s'`, the *buffer correction*
`D_U = (V^{⊗2})ᴴ F_{B_A} V^{⊗2}` acts on the two copies of `U`, where `F_{B_A}` exchanges the
two copies of `B_A`. Composed with the exchange `F_A` of the two copies at `A`, it is
`D_U F_A = (𝒱^{⊗2})ᴴ F_{A B_A} 𝒱^{⊗2}` with `𝒱 = 1 ⊗ V`, and on the square `ω^{⊗2}` of a unit
vector it moves by at most `4 ‖𝒱 ω - s ⊗ s'‖`, since `F_{A B_A}` fixes `(s ⊗ s')^{⊗2}`. The
buffer correction composed with an exchange at a set `R ⊆ U` acts on the two copies of `U`
alone, by the matrix `(V^{⊗2})ᴴ F_{B_A} V^{⊗2} F_R`.

The exchange `F_S` of the two copies at the sites of `S` is `ManyBody.pairSwapOp S`, read on
pairs of configurations along `Equiv.arrowProdEquivProdArrow`; its algebra
(`ManyBody.pairSwapOp_mul_of_subset`: `F_R F_Y = F_{Y \ R}` for `R ⊆ Y`;
`ManyBody.reindex_pairSwapOp`: the exchange is the permutation matrix of `ManyBody.pairSwap`)
does not depend on a geometry of the sites.

## Main definitions

* `ManyBody.tSwap`, `ManyBody.tSwapW`, `ManyBody.bufferSwap`, `ManyBody.tbSwap`: the exchanges
  of components of two copies.
* `ManyBody.bufferCorrection`: `D_U` for abstract finite systems.
* `ManyBody.configBufferCorrection`: `D_U` of splitting data on two copies of the system.
* `ManyBody.partSwap`, `ManyBody.correctionMatrix`: the exchange at `R` of two configurations
  outside `B`, and the matrix of `D_U F_R` on the two copies of `U`.

## Main results

* `ManyBody.bufferCorrection_mul_tSwap`: `D_U F_A = (𝒱^{⊗2})ᴴ F_{A B_A} 𝒱^{⊗2}`
  (`eq:exchange-net-map`).
* `ManyBody.norm_toEuclideanLin_bufferCorrection_mul_tSwap_sub_le`:
  `‖D_U F_A ω^{⊗2} - ω^{⊗2}‖ ≤ 4δ`.
* `ManyBody.norm_toEuclideanLin_configBufferCorrection_mul_pairSwapOp_sub_le`: the same for
  splitting data and the exchange `F_A` on two copies of the system.
* `ManyBody.commute_configBufferCorrection`: the buffer correction commutes with products of
  operators supported in `B`.
* `ManyBody.configBufferCorrection_mul_pairSwapOp_eq`: for `R ⊆ U`, `D_U F_R = 1 ⊗ W`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.6 `lem:exchange`,
  `05-frames.tex`, lines 481–561.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix
open EuclideanSpace (vecKron)
open scoped Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace ManyBody

/-! ### The buffer correction for abstract systems -/

section Buffer

/-- The bijection of two copies of `T × E` exchanging their `T`-components. -/
def tSwap (T E : Type*) : Equiv.Perm ((T × E) × (T × E)) where
  toFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  invFun x := ((x.2.1, x.1.2), (x.1.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bijection of two copies of `(T × E) × U` exchanging their `T`-components: the exchange
`F_T` of the two copies at `T`, in the coordinates `((t, e), u)`. -/
def tSwapW (T E U : Type*) : Equiv.Perm (((T × E) × U) × ((T × E) × U)) where
  toFun x := (((x.2.1.1, x.1.1.2), x.1.2), ((x.1.1.1, x.2.1.2), x.2.2))
  invFun x := (((x.2.1.1, x.1.1.2), x.1.2), ((x.1.1.1, x.2.1.2), x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bijection of two copies of `B_T × B_E` exchanging their `B_T`-components. -/
def bufferSwap (BT BE : Type*) : Equiv.Perm ((BT × BE) × (BT × BE)) := tSwap BT BE

/-- The bijection of two copies of `(T × E) × (B_T × B_E)` exchanging their `T`- and
`B_T`-components: the exchange `F_{T B_T}`. -/
def tbSwap (T E BT BE : Type*) :
    Equiv.Perm (((T × E) × (BT × BE)) × ((T × E) × (BT × BE))) where
  toFun x := (((x.2.1.1, x.1.1.2), (x.2.2.1, x.1.2.2)), ((x.1.1.1, x.2.1.2), (x.1.2.1, x.2.2.2)))
  invFun x := (((x.2.1.1, x.1.1.2), (x.2.2.1, x.1.2.2)), ((x.1.1.1, x.2.1.2), (x.1.2.1, x.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

variable {T E U BT BE : Type*} [Fintype T] [DecidableEq T] [Fintype E] [DecidableEq E]
  [Fintype U] [DecidableEq U] [Fintype BT] [DecidableEq BT] [Fintype BE] [DecidableEq BE]

/-- **The buffer correction `D_U = (V^{⊗2})ᴴ F_{B_T} V^{⊗2}`** on the two copies of `U`
(`eq:exchange-buffer-correction`), as an operator on two copies of `(T × E) × U` acting as the
identity on the copies of `T × E`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 503–510. -/
def bufferCorrection (V : Matrix (BT × BE) U ℂ) :
    Matrix (((T × E) × U) × ((T × E) × U)) (((T × E) × U) × ((T × E) × U)) ℂ :=
  ((1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) ⊗ₖ
      ((V ⊗ₖ V)ᴴ * ((bufferSwap BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ) * (V ⊗ₖ V))).submatrix
    (Equiv.prodProdProdComm (T × E) U (T × E) U) (Equiv.prodProdProdComm (T × E) U (T × E) U)

omit [Fintype T] [Fintype E] [Fintype U] [Fintype BT] [DecidableEq BT] [Fintype BE]
  [DecidableEq BE] in
/-- The exchange `F_T` of the two copies is `F_{T}^{(T × E)} ⊗ 1` after regrouping. -/
theorem tSwapW_toMatrix :
    ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ) =
      (((tSwap T E).toPEquiv.toMatrix : Matrix _ _ ℂ) ⊗ₖ
          (1 : Matrix (U × U) (U × U) ℂ)).submatrix
        (Equiv.prodProdProdComm (T × E) U (T × E) U)
        (Equiv.prodProdProdComm (T × E) U (T × E) U) := by
  rw [← PEquiv.toMatrix_refl, ← Equiv.toPEquiv_refl, ← toMatrix_toPEquiv_prodCongr,
    toMatrix_toPEquiv_submatrix]
  rfl

omit [Fintype T] [Fintype E] [Fintype U] [DecidableEq U] [Fintype BT] [Fintype BE] in
/-- The exchange `F_{T B_T}` is `F_T ⊗ F_{B_T}` after regrouping. -/
theorem tbSwap_toMatrix :
    ((tbSwap T E BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ) =
      (((tSwap T E).toPEquiv.toMatrix : Matrix _ _ ℂ) ⊗ₖ
          ((bufferSwap BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ)).submatrix
        (Equiv.prodProdProdComm (T × E) (BT × BE) (T × E) (BT × BE))
        (Equiv.prodProdProdComm (T × E) (BT × BE) (T × E) (BT × BE)) := by
  rw [← toMatrix_toPEquiv_prodCongr, toMatrix_toPEquiv_submatrix]
  rfl

/-- **The net map (`eq:exchange-net-map`).** `D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T} 𝒱^{⊗2}` with
`𝒱 = 1_{TE} ⊗ V`: `F_T` acts outside `U` and commutes through the isometries.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 516–526. -/
theorem bufferCorrection_mul_tSwap (V : Matrix (BT × BE) U ℂ) :
    bufferCorrection (T := T) (E := E) V * ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ) =
      (((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) ⊗ₖ ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V))ᴴ *
        ((tbSwap T E BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ) *
        (((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) ⊗ₖ ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V)) := by
  set F₀ : Matrix ((BT × BE) × (BT × BE)) ((BT × BE) × (BT × BE)) ℂ :=
    (bufferSwap BT BE).toPEquiv.toMatrix
  set G : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ := (tSwap T E).toPEquiv.toMatrix
  have hin : ((1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) ⊗ₖ
        ((V ⊗ₖ V)ᴴ * F₀ * (V ⊗ₖ V))) * (G ⊗ₖ (1 : Matrix (U × U) (U × U) ℂ)) =
      ((1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) ⊗ₖ (V ⊗ₖ V))ᴴ * (G ⊗ₖ F₀) *
        ((1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) ⊗ₖ (V ⊗ₖ V)) := by
    rw [conjTranspose_kronecker (1 : Matrix ((T × E) × (T × E)) ((T × E) × (T × E)) ℂ) (V ⊗ₖ V),
      conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
    simp only [Matrix.one_mul, Matrix.mul_one]
  rw [bufferCorrection, tSwapW_toMatrix, tbSwap_toMatrix, kronecker_kronecker_eq_submatrix,
    conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_mul_equiv,
    one_kronecker_one, hin]

/-- The buffer correction of an isometry is a contraction. -/
theorem norm_bufferCorrection_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry) :
    ‖bufferCorrection (T := T) (E := E) V‖ ≤ 1 := by
  refine (norm_submatrix_equiv_le _ _).trans ((l2_opNorm_one_kronecker_le _).trans ?_)
  exact l2_opNorm_conjTranspose_mul_mul_le_one (IsIsometry.kronecker V V hV hV).l2_opNorm_le_one
    (l2_opNorm_toMatrix_toPEquiv_le _)

omit [Fintype U] [DecidableEq U] in
/-- `F_{T B_T}` fixes `(s ⊗ s')^{⊗2}`: it exchanges the two identical factors `s`. -/
theorem toEuclideanLin_tbSwap_vecKron_tensorPurification (s : T × BT → ℂ) (s' : E × BE → ℂ) :
    toEuclideanLin ((tbSwap T E BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ)
        (vecKron (WithLp.toLp 2 (tensorPurification s s'))
          (WithLp.toLp 2 (tensorPurification s s'))) =
      vecKron (WithLp.toLp 2 (tensorPurification s s'))
        (WithLp.toLp 2 (tensorPurification s s')) := by
  ext x
  simp only [toLpLin_apply, PiLp.toLp_apply, PEquiv.toMatrix_toPEquiv_mulVec, Function.comp_apply,
    vecKron, tensorPurification]
  change s (x.2.1.1, x.2.2.1) * s' (x.1.1.2, x.1.2.2) * (s (x.1.1.1, x.1.2.1) *
    s' (x.2.1.2, x.2.2.2)) = _
  ring

/-- **The exchange error on the reference (`05-frames.tex`, lines 534–553).** For an isometry
`V`, unit vectors `s`, `s'` and a unit vector `ω` on `(T × E) × U`, with
`δ = ‖𝒱 ω - s ⊗ s'‖`, `‖D_U F_T ω^{⊗2} - ω^{⊗2}‖ ≤ 4δ`: the squares differ by at most `2δ`,
the exchange `F_{T B_T}` fixes `(s ⊗ s')^{⊗2}`, and `‖F_{T B_T} - 1‖ ≤ 2`. -/
theorem norm_toEuclideanLin_bufferCorrection_mul_tSwap_sub_le {V : Matrix (BT × BE) U ℂ}
    (hV : V.IsIsometry) {s : T × BT → ℂ} {s' : E × BE → ℂ} (hs : star s ⬝ᵥ s = 1)
    (hs' : star s' ⬝ᵥ s' = 1) {ω : EuclideanSpace ℂ ((T × E) × U)} (hω : ‖ω‖ = 1) :
    ‖toEuclideanLin (bufferCorrection (T := T) (E := E) V *
          ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ)) (vecKron ω ω) - vecKron ω ω‖ ≤
      4 * ‖toEuclideanLin ((1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V) ω -
        WithLp.toLp 2 (tensorPurification s s')‖ := by
  set 𝒱 := (1 : Matrix (T × E) (T × E) ℂ) ⊗ₖ V
  set ζ : EuclideanSpace ℂ ((T × E) × (BT × BE)) := WithLp.toLp 2 (tensorPurification s s')
  set F : Matrix _ _ ℂ := ((tbSwap T E BT BE).toPEquiv.toMatrix : Matrix _ _ ℂ)
  have hiso : 𝒱ᴴ * 𝒱 = 1 :=
    IsIsometry.kronecker (1 : Matrix (T × E) (T × E) ℂ) V (by simp [IsIsometry]) hV
  have hiso2 : (𝒱 ⊗ₖ 𝒱)ᴴ * (𝒱 ⊗ₖ 𝒱) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, hiso, one_kronecker_one]
  have hw : ‖toEuclideanLin 𝒱 ω‖ = 1 := by
    rw [norm_toEuclideanLin_apply_eq_of_conjTranspose_mul_eq
      (B := (1 : Matrix ((T × E) × U) ((T × E) × U) ℂ))
      (by rw [hiso, conjTranspose_one, Matrix.mul_one]), toEuclideanLin_one_apply, hω]
  have hζ : ‖ζ‖ = 1 := norm_toLp_tensorPurification hs hs'
  have hF : toEuclideanLin F (vecKron ζ ζ) = vecKron ζ ζ :=
    toEuclideanLin_tbSwap_vecKron_tensorPurification s s'
  have hFn : ‖F - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(1 : Matrix (((T × E) × (BT × BE)) × ((T × E) × (BT × BE)))
        (((T × E) × (BT × BE)) × ((T × E) × (BT × BE))) ℂ)‖ ≤ 1 :=
      (IsStarProjection.one _).norm_le
    linarith [l2_opNorm_toMatrix_toPEquiv_le (tbSwap T E BT BE)]
  have hV2 : ‖(𝒱 ⊗ₖ 𝒱)ᴴ‖ ≤ 1 := by
    rw [l2_opNorm_conjTranspose]
    have h1 : ‖𝒱‖ ≤ 1 := (l2_opNorm_one_kronecker_le V).trans hV.l2_opNorm_le_one
    exact l2_opNorm_kronecker_le_one h1 h1
  have hmat : bufferCorrection (T := T) (E := E) V *
        ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ) = (𝒱 ⊗ₖ 𝒱)ᴴ * (F - 1) * (𝒱 ⊗ₖ 𝒱) + 1 := by
    rw [bufferCorrection_mul_tSwap, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hiso2,
      sub_add_cancel]
  have hz : toEuclideanLin (F - 1) (vecKron ζ ζ) = 0 := by
    rw [map_sub, LinearMap.sub_apply, hF, toEuclideanLin_one_apply, sub_self]
  have key : toEuclideanLin (bufferCorrection (T := T) (E := E) V *
        ((tSwapW T E U).toPEquiv.toMatrix : Matrix _ _ ℂ)) (vecKron ω ω) - vecKron ω ω =
      toEuclideanLin (𝒱 ⊗ₖ 𝒱)ᴴ (toEuclideanLin (F - 1)
        (vecKron (toEuclideanLin 𝒱 ω) (toEuclideanLin 𝒱 ω) - vecKron ζ ζ)) := by
    rw [hmat, map_add, LinearMap.add_apply, toEuclideanLin_one_apply, add_sub_cancel_right,
      map_sub (toEuclideanLin (F - 1)), hz, sub_zero, ← toEuclideanLin_kronecker_vecKron,
      ← toEuclideanLin_mul_apply, ← toEuclideanLin_mul_apply]
  rw [key]
  refine (norm_toEuclideanLin_apply_le_of_norm_le_one hV2 _).trans ?_
  refine (norm_toEuclideanLin_apply_le _ _).trans ?_
  have h2 := EuclideanSpace.norm_vecKron_self_sub_le (toEuclideanLin 𝒱 ω) ζ
  rw [hw, hζ] at h2
  nlinarith [norm_nonneg (F - 1), norm_nonneg (toEuclideanLin 𝒱 ω - ζ),
    norm_nonneg (vecKron (toEuclideanLin 𝒱 ω) (toEuclideanLin 𝒱 ω) - vecKron ζ ζ)]

end Buffer

/-! ### The buffer correction and the exchange at `A` on two copies -/

section ConfigBuffer

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {A B : Finset V} (hAB : A ⊆ B)

omit [Fintype V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] in
/-- The coordinates `ManyBody.threeCutEquiv` on both copies. -/
abbrev threeCutEquiv₂ : Config X × Config X ≃
    ((RegionConfig X A × RegionConfig X (B \ A)) × ComplConfig X B) ×
      ((RegionConfig X A × RegionConfig X (B \ A)) × ComplConfig X B) :=
  (threeCutEquiv X hAB).prodCongr (threeCutEquiv X hAB)

-- Two copies of the configurations `((x, y), z)` of three regions form a fourfold product of
-- function types; synthesizing their decidable equality exceeds the default instance size.
set_option synthInstance.maxSize 512 in
/-- The buffer correction `D_U` of splitting data on two copies of the system
(`eq:exchange-buffer-correction`). It acts on the two copies of `U = Bᶜ` alone.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 503–510. -/
def configBufferCorrection (σ : SplittingData X A B) :
    Matrix (Config X × Config X) (Config X × Config X) ℂ :=
  (bufferCorrection (T := RegionConfig X A) (E := RegionConfig X (B \ A)) σ.V).submatrix
    (threeCutEquiv₂ hAB) (threeCutEquiv₂ hAB)

set_option synthInstance.maxSize 512 in
/-- The buffer correction of splitting data is a contraction. -/
theorem norm_configBufferCorrection_le_one (σ : SplittingData X A B) :
    ‖configBufferCorrection hAB σ‖ ≤ 1 :=
  (norm_submatrix_equiv_le _ _).trans (norm_bufferCorrection_le_one σ.isIsometry)

omit [∀ v, Fintype (X v)] in
set_option synthInstance.maxSize 512 in
/-- In the coordinates `ManyBody.threeCutEquiv` of both copies, exchanging the copies at `A`
exchanges the `A`-components. -/
theorem reindex_pairSwapOp_eq_submatrix :
    reindex (Equiv.arrowProdEquivProdArrow V X X) (Equiv.arrowProdEquivProdArrow V X X)
        (pairSwapOp A) =
      ((tSwapW (RegionConfig X A) (RegionConfig X (B \ A)) (ComplConfig X B)).toPEquiv.toMatrix :
        Matrix _ _ ℂ).submatrix (threeCutEquiv₂ hAB) (threeCutEquiv₂ hAB) := by
  have he : (threeCutEquiv₂ hAB).symm.trans
      (((Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap A)).trans
        (threeCutEquiv₂ hAB)) =
      tSwapW (RegionConfig X A) (RegionConfig X (B \ A)) (ComplConfig X B) := by
    refine Equiv.ext fun w ↦ ?_
    obtain ⟨⟨⟨x₁, y₁⟩, z₁⟩, ⟨⟨x₂, y₂⟩, z₂⟩⟩ := w
    have hM : ∀ v : {v // v ∈ B \ A}, (v : V) ∉ A := fun v ↦ (Finset.mem_sdiff.1 v.2).2
    have hU : ∀ v : {v // v ∉ B}, (v : V) ∉ A := fun v hv ↦ v.2 (hAB hv)
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
      funext v <;> simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
        Prod.map_fst, Prod.map_snd, threeCutEquiv_apply_fst_fst, threeCutEquiv_apply_fst_snd,
        threeCutEquiv_apply_snd, permCongr_pairSwap_apply, tSwapW]
    · simp only [v.2, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_mem hAB v.2
    · simp only [hM v, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_mem_sdiff hAB v.2
    · simp only [hU v, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_not_mem hAB v.2
    · simp only [v.2, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_mem hAB v.2
    · simp only [hM v, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_mem_sdiff hAB v.2
    · simp only [hU v, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_not_mem hAB v.2
  have hsub := toMatrix_toPEquiv_submatrix
    ((Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap A)) (threeCutEquiv₂ hAB).symm
      (threeCutEquiv₂ hAB).symm
  rw [Equiv.symm_symm, he] at hsub
  rw [← hsub, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  exact reindex_pairSwapOp A

set_option synthInstance.maxSize 512 in
/-- **The net map of an exchange on two copies of a unit vector.** For splitting data `σ`, the
net map `D_U F_A = (𝒱^{⊗2})ᴴ F_{A B_A} 𝒱^{⊗2}` of the exchange moves `Ω ⊗ Ω` by at most
`4 ‖𝒱 Ω - s ⊗ s'‖`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 516–561. -/
theorem norm_toEuclideanLin_configBufferCorrection_mul_pairSwapOp_sub_le
    (σ : SplittingData X A B) {Ω : EuclideanSpace ℂ (Config X)} (hΩ : ‖Ω‖ = 1) :
    ‖toEuclideanLin (configBufferCorrection hAB σ * reindex
        (Equiv.arrowProdEquivProdArrow V X X) (Equiv.arrowProdEquivProdArrow V X X)
        (pairSwapOp A)) (vecKron Ω Ω) - vecKron Ω Ω‖ ≤ 4 * σ.error hAB Ω := by
  rw [reindex_pairSwapOp_eq_submatrix hAB, configBufferCorrection, submatrix_mul_equiv,
    norm_toEuclideanLin_submatrix_apply_sub]
  set ω : EuclideanSpace ℂ _ := WithLp.toLp 2 (splitVec hAB Ω)
  have hω : (WithLp.toLp 2 ((vecKron Ω Ω).ofLp ∘ (threeCutEquiv₂ hAB).symm) :
      EuclideanSpace ℂ _) = vecKron ω ω := rfl
  have hω1 : ‖ω‖ = 1 :=
    EuclideanSpace.norm_toLp_eq_one_of_star_dotProduct (star_splitVec_dotProduct_splitVec hAB hΩ)
  rw [hω]
  exact norm_toEuclideanLin_bufferCorrection_mul_tSwap_sub_le σ.isIsometry σ.star_s σ.star_s' hω1

/-- The buffer correction commutes with every product `R₁ ⊗ R₂` of operators supported in `B`
(`05-frames.tex`, lines 514–515). -/
theorem commute_configBufferCorrection (σ : SplittingData X A B)
    {R₁ R₂ : Matrix (Config X) (Config X) ℂ} (hR₁ : R₁ ∈ supportedOperators X B)
    (hR₂ : R₂ ∈ supportedOperators X B) :
    Commute (configBufferCorrection hAB σ) (R₁ ⊗ₖ R₂) := by
  obtain ⟨R₁', hR₁'⟩ := exists_reindex_threeCutEquiv_eq_kronecker_one hAB hR₁
  obtain ⟨R₂', hR₂'⟩ := exists_reindex_threeCutEquiv_eq_kronecker_one hAB hR₂
  have hR := submatrix_symm_submatrix (R₁ ⊗ₖ R₂) (threeCutEquiv₂ hAB).symm
  rw [Equiv.symm_symm] at hR
  have hform : (R₁ ⊗ₖ R₂).submatrix (threeCutEquiv₂ hAB).symm (threeCutEquiv₂ hAB).symm =
      ((R₁' ⊗ₖ R₂') ⊗ₖ
        (1 : Matrix (ComplConfig X B × ComplConfig X B)
          (ComplConfig X B × ComplConfig X B) ℂ)).submatrix
        (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _) := by
    have h₁ : R₁.submatrix (threeCutEquiv X hAB).symm (threeCutEquiv X hAB).symm =
        R₁' ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ) := hR₁'
    have h₂ : R₂.submatrix (threeCutEquiv X hAB).symm (threeCutEquiv X hAB).symm =
        R₂' ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ) := hR₂'
    rw [← one_kronecker_one, ← kronecker_kronecker_eq_submatrix, ← h₁, ← h₂]
    rfl
  rw [← hR, hform, configBufferCorrection, bufferCorrection]
  refine Commute.submatrix_equiv (Commute.submatrix_equiv ?_ _) _
  change _ * _ = _ * _
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.one_mul]

/-! ### The corrections of an exchange on the two copies of `U` -/

variable (X) in
/-- The bijection of two copies of the configurations outside `B` exchanging them at the sites
of `R`. -/
def partSwap (B R : Finset V) : Equiv.Perm (ComplConfig X B × ComplConfig X B) where
  toFun r := (fun v ↦ if (v : V) ∈ R then r.2 v else r.1 v,
    fun v ↦ if (v : V) ∈ R then r.1 v else r.2 v)
  invFun r := (fun v ↦ if (v : V) ∈ R then r.2 v else r.1 v,
    fun v ↦ if (v : V) ∈ R then r.1 v else r.2 v)
  left_inv r := by
    ext v <;> by_cases hv : (v : V) ∈ R <;> simp [hv]
  right_inv r := by
    ext v <;> by_cases hv : (v : V) ∈ R <;> simp [hv]

set_option synthInstance.maxSize 512 in
/-- **The corrections of an exchange on the two copies of `U`.** The matrix
`W = (V^{⊗2})ᴴ F_{B_A} V^{⊗2} F_R` of `D_U F_R` on the two copies of `U = Bᶜ`, for `R ⊆ U`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 503–515. -/
def correctionMatrix (σ : SplittingData X A B) (R : Finset V) :
    Matrix (ComplConfig X B × ComplConfig X B) (ComplConfig X B × ComplConfig X B) ℂ :=
  (σ.V ⊗ₖ σ.V)ᴴ *
      ((bufferSwap (RegionConfig X A)
        (RegionConfig X (B \ A) ⊕ ComplConfig X B)).toPEquiv.toMatrix : Matrix _ _ ℂ) *
      (σ.V ⊗ₖ σ.V) *
    ((partSwap X B R).toPEquiv.toMatrix : Matrix _ _ ℂ)

set_option synthInstance.maxSize 512 in
/-- The corrections `W` of an exchange form a contraction. -/
theorem norm_correctionMatrix_le_one (σ : SplittingData X A B) (R : Finset V) :
    ‖correctionMatrix σ R‖ ≤ 1 :=
  l2_opNorm_mul_le_one _ _ (l2_opNorm_conjTranspose_mul_mul_le_one
    (IsIsometry.kronecker σ.V σ.V σ.isIsometry σ.isIsometry).l2_opNorm_le_one
    (l2_opNorm_toMatrix_toPEquiv_le _)) (l2_opNorm_toMatrix_toPEquiv_le _)

omit [∀ v, Fintype (X v)] in
set_option synthInstance.maxSize 512 in
/-- In the coordinates `ManyBody.threeCutEquiv` of both copies, exchanging the copies at
`R ⊆ U` exchanges the `R`-parts of the two copies of `U`. -/
theorem reindex_pairSwapOp_eq_submatrix_of_subset {R : Finset V} (hR : R ⊆ Bᶜ) :
    reindex (Equiv.arrowProdEquivProdArrow V X X) (Equiv.arrowProdEquivProdArrow V X X)
        (pairSwapOp R) =
      (((1 : Matrix ((RegionConfig X A × RegionConfig X (B \ A)) ×
            (RegionConfig X A × RegionConfig X (B \ A)))
          ((RegionConfig X A × RegionConfig X (B \ A)) ×
            (RegionConfig X A × RegionConfig X (B \ A))) ℂ) ⊗ₖ
        ((partSwap X B R).toPEquiv.toMatrix : Matrix _ _ ℂ)).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)).submatrix
        (threeCutEquiv₂ hAB) (threeCutEquiv₂ hAB) := by
  have hRA : ∀ v : {v // v ∈ A}, (v : V) ∉ R := fun v hv ↦
    Finset.mem_compl.mp (hR hv) (hAB v.2)
  have hRM : ∀ v : {v // v ∈ B \ A}, (v : V) ∉ R := fun v hv ↦
    Finset.mem_compl.mp (hR hv) (Finset.mem_sdiff.1 v.2).1
  have he : (threeCutEquiv₂ hAB).symm.trans
      (((Equiv.arrowProdEquivProdArrow V X X).permCongr (pairSwap R)).trans
        (threeCutEquiv₂ hAB)) =
      (Equiv.prodProdProdComm _ _ _ _).trans
        (((Equiv.refl _).prodCongr (partSwap X B R)).trans
          (Equiv.prodProdProdComm _ _ _ _).symm) := by
    refine Equiv.ext fun w ↦ ?_
    obtain ⟨⟨⟨x₁, y₁⟩, z₁⟩, ⟨⟨x₂, y₂⟩, z₂⟩⟩ := w
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) ?_) (Prod.ext (Prod.ext ?_ ?_) ?_) <;>
      funext v <;> simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodCongr_symm,
        Prod.map_fst, Prod.map_snd, threeCutEquiv_apply_fst_fst, threeCutEquiv_apply_fst_snd,
        threeCutEquiv_apply_snd, permCongr_pairSwap_apply, Equiv.coe_fn_mk, partSwap,
        Equiv.prodProdProdComm, Equiv.coe_fn_symm_mk, Equiv.refl_apply]
    · simp only [hRA v, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_mem hAB v.2
    · simp only [hRM v, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_mem_sdiff hAB v.2
    · by_cases hv : (v : V) ∈ R <;> simp only [hv, ↓reduceIte] <;>
        exact threeCutEquiv_symm_apply_of_not_mem hAB v.2
    · simp only [hRA v, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_mem hAB v.2
    · simp only [hRM v, ↓reduceIte]; exact threeCutEquiv_symm_apply_of_mem_sdiff hAB v.2
    · by_cases hv : (v : V) ∈ R <;> simp only [hv, ↓reduceIte] <;>
        exact threeCutEquiv_symm_apply_of_not_mem hAB v.2
  have key : ((((Equiv.arrowProdEquivProdArrow V X X).permCongr
      (pairSwap R)).toPEquiv.toMatrix : Matrix _ _ ℂ)).submatrix (threeCutEquiv₂ hAB).symm
      (threeCutEquiv₂ hAB).symm =
      ((1 : Matrix ((RegionConfig X A × RegionConfig X (B \ A)) ×
            (RegionConfig X A × RegionConfig X (B \ A)))
          ((RegionConfig X A × RegionConfig X (B \ A)) ×
            (RegionConfig X A × RegionConfig X (B \ A))) ℂ) ⊗ₖ
        ((partSwap X B R).toPEquiv.toMatrix : Matrix _ _ ℂ)).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _) := by
    rw [toMatrix_toPEquiv_submatrix, Equiv.symm_symm, he, ← PEquiv.toMatrix_refl,
      ← Equiv.toPEquiv_refl, ← toMatrix_toPEquiv_prodCongr, toMatrix_toPEquiv_submatrix]
  rw [← key, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  exact reindex_pairSwapOp R

set_option synthInstance.maxSize 512 in
/-- **The corrections of an exchange act on the two copies of `U` alone.** For `R ⊆ U`,
`D_U F_R = 1 ⊗ W` with `W = correctionMatrix σ R`, in the coordinates in which the two copies
of `A × (B \ A)` come first.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 503–515. -/
theorem configBufferCorrection_mul_pairSwapOp_eq (σ : SplittingData X A B) {R : Finset V}
    (hR : R ⊆ Bᶜ) :
    configBufferCorrection hAB σ *
        reindex (Equiv.arrowProdEquivProdArrow V X X) (Equiv.arrowProdEquivProdArrow V X X)
          (pairSwapOp R) =
      (((1 : Matrix ((RegionConfig X A × RegionConfig X (B \ A)) ×
            (RegionConfig X A × RegionConfig X (B \ A)))
          ((RegionConfig X A × RegionConfig X (B \ A)) ×
            (RegionConfig X A × RegionConfig X (B \ A))) ℂ) ⊗ₖ
        correctionMatrix σ R).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)).submatrix
        (threeCutEquiv₂ hAB) (threeCutEquiv₂ hAB) := by
  rw [reindex_pairSwapOp_eq_submatrix_of_subset hAB hR, configBufferCorrection,
    bufferCorrection, submatrix_mul_equiv, submatrix_mul_equiv, ← mul_kronecker_mul,
    Matrix.one_mul]
  rfl

end ConfigBuffer

end ManyBody
