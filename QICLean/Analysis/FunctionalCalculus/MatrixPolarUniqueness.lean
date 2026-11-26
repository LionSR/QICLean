/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Hermitian.ProjectionMatrixRange
import QICLean.Analysis.FunctionalCalculus.MatrixPolar

/-!
# Uniqueness of the polar decomposition

The polar decomposition `M = V P` of `Matrix.polarIso` and `Matrix.polarPos` is unique in the
following sense: if `M = W Q` with `Q` positive semidefinite and `Wᴴ W = E`, where `E` is an
orthogonal projector with the same range as `Q`, then `Q = polarPos M`, `E = polarSupport M`,
and `W = polarIso M`. This identifies the polar factors of an orthogonal sum
(`Matrix.polarIso_sum_of_orthogonal`); the other results here serve the diagonal, supported and
block-sum cases.

## Main declarations

* `Matrix.mul_eq_self_of_conjTranspose_mul_self_eq` — a partial isometry is fixed by its
  initial projector: `Wᴴ W = E` gives `W E = W`.
* `Matrix.polarPos_eq_of_eq_mul`, `Matrix.polarSupport_eq_of_eq_mul`,
  `Matrix.polarIso_eq_of_eq_mul` — uniqueness of the three polar factors.
* `Matrix.conjTranspose_polarIso_mul_self` — `V† M = P`.
* `Matrix.polarPos_eq_of_mul_self_eq`, `Matrix.polarSupport_eq_of_range_eq` — the positive part
  and the support projector are determined by a positive square root of `Mᴴ M` and by its range.
* `Matrix.exists_polarIso_eq_mul` — the partial isometry is `V = M R` for some `R`.
* `Matrix.polarIso_mul_eq_zero` — the partial isometry of `M` vanishes on the kernel of `M`.
* `Matrix.conjTranspose_polarIso_mul_eq_zero`,
  `Matrix.conjTranspose_polarIso_mul_polarIso_eq_zero` — orthogonality `Mᴴ M' = 0` passes to
  the partial isometries.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (8) and its Supplemental Material: the
  polar decomposition `B = V P`. The source does not state its uniqueness; it is supplied here
  for the identifications of polar factors listed above.

Moved from TNLean, `TNLean/MPS/Tensor/Physical/PolarUniqueness.lean`,
`TNLean/MPS/Preparation/Polar/OrthogonalSumPolar.lean`,
`TNLean/MPS/Tensor/Physical/SupportedPolar.lean` at commit `021ba0bd19` (Apache-2.0).
-/

section

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- **A partial isometry is fixed by its initial projector**: if `Wᴴ W = E` for an orthogonal
projector `E`, then `W E = W`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal
tensors" (the paragraph containing eq. (S7)): `V†V = Π` for `Π` the projector onto the image
of `P`. -/
theorem mul_eq_self_of_conjTranspose_mul_self_eq {W : Matrix ι κ ℂ} {E : Matrix κ κ ℂ}
    (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEE : E * E = E) : W * E = W := by
  have h : (W * E - W)ᴴ * (W * E - W) = 0 := by
    have hexp : (W * E - W)ᴴ * (W * E - W) =
        E * (Wᴴ * W) * E - E * (Wᴴ * W) - (Wᴴ * W) * E + Wᴴ * W := by
      rw [conjTranspose_sub, conjTranspose_mul, hE.eq]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [hexp, hW, hEE, hEE, sub_self, zero_sub, neg_add_cancel]
  exact sub_eq_zero.mp (conjTranspose_mul_self_eq_zero.mp h)

omit [Fintype ι] [DecidableEq κ] in
/-- An idempotent `E` fixes every matrix `Q` whose range lies in the range of `E`. -/
theorem mul_eq_self_of_range_le {ρ : Type*} {E : Matrix κ κ ℂ} {Q : Matrix κ ρ ℂ}
    [Fintype ρ] (hEE : E * E = E)
    (hran : LinearMap.range Q.mulVecLin ≤ LinearMap.range E.mulVecLin) : E * Q = Q := by
  refine ext_iff_mulVec.mpr fun v => ?_
  obtain ⟨u, hu⟩ := hran ⟨v, rfl⟩
  change E *ᵥ u = Q *ᵥ v at hu
  rw [← mulVec_mulVec, ← hu, mulVec_mulVec, hEE]

omit [Fintype ι] [DecidableEq κ] in
/-- If `Y Q = 0` and the range of `E` lies in the range of `Q`, then `Y E = 0`. -/
theorem mul_eq_zero_of_mul_eq_zero_of_range_le {ρ : Type*} [Fintype ρ] {Y : Matrix ι κ ℂ}
    {E : Matrix κ κ ℂ} {Q : Matrix κ ρ ℂ} (hY : Y * Q = 0)
    (hran : LinearMap.range E.mulVecLin ≤ LinearMap.range Q.mulVecLin) : Y * E = 0 := by
  refine ext_iff_mulVec.mpr fun v => ?_
  obtain ⟨u, hu⟩ := hran ⟨v, rfl⟩
  change Q *ᵥ u = E *ᵥ v at hu
  rw [← mulVec_mulVec, ← hu, mulVec_mulVec, hY, zero_mulVec, zero_mulVec]

omit [DecidableEq κ] in
/-- The Gram matrix of a product `W Q` with `Wᴴ W = E`, `E Q = Q`, and `Q` Hermitian is
`Q Q`. -/
private lemma gram_eq_of_eq_mul {M W : Matrix ι κ ℂ} {Q E : Matrix κ κ ℂ} (hM : M = W * Q)
    (hQ : Q.IsHermitian) (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEQ : E * Q = Q) :
    Mᴴ * M = Q * Q := by
  have hQE : Q * E = Q := by
    rw [← hQ.eq, ← hE.eq, ← conjTranspose_mul, hEQ]
  rw [hM, conjTranspose_mul, hQ.eq, Matrix.mul_assoc, ← Matrix.mul_assoc Wᴴ, hW,
    ← Matrix.mul_assoc, hQE]

/-- **Uniqueness of the positive part of the polar decomposition**: if `M = W Q` with `Q`
positive semidefinite and `Wᴴ W = E` for an orthogonal projector `E` with the same range as
`Q`, then `Q = polarPos M`.

Supplied step for arXiv:2307.01696, eq. (8): uniqueness of the polar decomposition, which the
source does not state, identifies the positive part of an orthogonal sum. -/
theorem polarPos_eq_of_eq_mul {M W : Matrix ι κ ℂ} {Q E : Matrix κ κ ℂ} (hM : M = W * Q)
    (hQ : Q.PosSemidef) (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEE : E * E = E)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range Q.mulVecLin) :
    polarPos M = Q := by
  have hEQ : E * Q = Q := mul_eq_self_of_range_le hEE hran.ge
  rw [polarPos, gram_eq_of_eq_mul hM hQ.isHermitian hW hE hEQ]
  exact CFC.sqrt_mul_self Q (nonneg_iff_posSemidef.mpr hQ)

/-- **Uniqueness of the support projector of the polar decomposition**: under the hypotheses of
`Matrix.polarPos_eq_of_eq_mul`, `E = polarSupport M`. -/
theorem polarSupport_eq_of_eq_mul {M W : Matrix ι κ ℂ} {Q E : Matrix κ κ ℂ} (hM : M = W * Q)
    (hQ : Q.PosSemidef) (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEE : E * E = E)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range Q.mulVecLin) :
    polarSupport M = E := by
  refine Matrix.hermitian_idempotent_eq_of_range_eq _ _
    (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M) hE hEE ?_
  simp only [Matrix.toLin'_apply']
  rw [range_polarSupport, polarPos_eq_of_eq_mul hM hQ hW hE hEE hran, hran]

/-- **Uniqueness of the partial isometry of the polar decomposition**: if `M = W Q` with `Q`
positive semidefinite and `Wᴴ W = E` for an orthogonal projector `E` with the same range as
`Q`, then `W = polarIso M`.

Supplied step for arXiv:2307.01696, eq. (8): uniqueness of the polar decomposition, which the
source does not state, identifies the partial isometry of an orthogonal sum. -/
theorem polarIso_eq_of_eq_mul {M W : Matrix ι κ ℂ} {Q E : Matrix κ κ ℂ} (hM : M = W * Q)
    (hQ : Q.PosSemidef) (hW : Wᴴ * W = E) (hE : E.IsHermitian) (hEE : E * E = E)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range Q.mulVecLin) :
    polarIso M = W := by
  have hPos := polarPos_eq_of_eq_mul hM hQ hW hE hEE hran
  have hSupp := polarSupport_eq_of_eq_mul hM hQ hW hE hEE hran
  have hV : polarIso M * E = polarIso M := by
    rw [← hSupp]
    exact mul_eq_self_of_conjTranspose_mul_self_eq (conjTranspose_polarIso_mul_polarIso M)
      (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M)
  have hWE : W * E = W := mul_eq_self_of_conjTranspose_mul_self_eq hW hE hEE
  have hdiff : (polarIso M - W) * Q = 0 := by
    rw [Matrix.sub_mul, ← hPos, polarIso_mul_polarPos, hPos, ← hM, sub_self]
  have hdiffE := mul_eq_zero_of_mul_eq_zero_of_range_le hdiff hran.le
  rw [Matrix.sub_mul, hV, hWE, sub_eq_zero] at hdiffE
  exact hdiffE

/-- The partial isometry of the polar decomposition pulls a matrix back to its positive part:
`V† M = P`. This is `V†V = Π` and `Π P = P` (arXiv:2307.01696, Supplemental Material, "Proof of
Lemma 1 and extension to non-normal tensors") applied to `M = V P`. -/
theorem conjTranspose_polarIso_mul_self (M : Matrix ι κ ℂ) :
    (polarIso M)ᴴ * M = polarPos M := by
  calc (polarIso M)ᴴ * M = (polarIso M)ᴴ * (polarIso M * polarPos M) := by
        rw [polarIso_mul_polarPos]
    _ = polarPos M := by
        rw [← Matrix.mul_assoc, conjTranspose_polarIso_mul_polarIso, polarSupport_mul_polarPos]

/-- The positive part of the polar decomposition is the positive semidefinite square root of
`Mᴴ M`: any positive semidefinite `Q` with `Q Q = Mᴴ M` is `polarPos M`. -/
theorem polarPos_eq_of_mul_self_eq {M : Matrix ι κ ℂ} {Q : Matrix κ κ ℂ} (hQ : Q.PosSemidef)
    (h : Q * Q = Mᴴ * M) : polarPos M = Q := by
  rw [polarPos, ← h]
  exact CFC.sqrt_mul_self Q (nonneg_iff_posSemidef.mpr hQ)

omit [Fintype ι] [DecidableEq κ] in
/-- Two square matrices with `E Q = Q` and `Q R = E` have the same range. -/
theorem range_mulVecLin_eq_of_mul_eq {E Q R : Matrix κ κ ℂ} (h₁ : E * Q = Q) (h₂ : Q * R = E) :
    LinearMap.range E.mulVecLin = LinearMap.range Q.mulVecLin := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨R *ᵥ v, by simp [mulVec_mulVec, h₂]⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨Q *ᵥ v, by simp [mulVec_mulVec, h₁]⟩

/-- The support projector of the polar decomposition is the orthogonal projector onto the range
of the positive part: any Hermitian idempotent `E` with that range is `polarSupport M`. -/
theorem polarSupport_eq_of_range_eq {M : Matrix ι κ ℂ} {E : Matrix κ κ ℂ} (hE : E.IsHermitian)
    (hEE : E * E = E)
    (hran : LinearMap.range E.mulVecLin = LinearMap.range (polarPos M).mulVecLin) :
    polarSupport M = E := by
  refine Matrix.hermitian_idempotent_eq_of_range_eq _ _
    (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M) hE hEE ?_
  simp only [Matrix.toLin'_apply']
  rw [range_polarSupport, hran]

section Orthogonal

omit [Fintype κ] [DecidableEq κ] in
/-- If the range of `X` lies in the range of `Y`, then `X = Y R` for some `R`. -/
theorem exists_mul_eq_of_range_le {ρ ρ' : Type*} [Fintype ρ] [Fintype ρ']
    {X : Matrix κ ρ' ℂ} {Y : Matrix κ ρ ℂ}
    (h : LinearMap.range X.mulVecLin ≤ LinearMap.range Y.mulVecLin) :
    ∃ R : Matrix ρ ρ' ℂ, Y * R = X := by
  classical
  choose u hu using fun c : ρ' => h ⟨Pi.single c 1, rfl⟩
  refine ⟨of fun a c => u c a, ?_⟩
  ext a c
  have h1 := congrFun (hu c) a
  simp only [mulVecLin_apply, mulVec, dotProduct] at h1
  rw [mul_apply]
  simpa [Pi.single_apply] using h1

/-- The positive part has a right factor onto the support projector: `P R = Π` for some `R`. -/
theorem exists_polarPos_mul_eq_polarSupport (M : Matrix ι κ ℂ) :
    ∃ R : Matrix κ κ ℂ, polarPos M * R = polarSupport M :=
  exists_mul_eq_of_range_le (range_polarSupport M).le

/-- The partial isometry of the polar decomposition factors through the matrix: `V = M R` for
some `R` (arXiv:2307.01696, Supplemental Material, the polar decomposition `B = V P` with
`V†V = Π`). -/
theorem exists_polarIso_eq_mul (M : Matrix ι κ ℂ) : ∃ R : Matrix κ κ ℂ, polarIso M = M * R := by
  obtain ⟨R, hR⟩ := exists_polarPos_mul_eq_polarSupport M
  refine ⟨R, ?_⟩
  have hV : polarIso M * polarSupport M = polarIso M :=
    mul_eq_self_of_conjTranspose_mul_self_eq (conjTranspose_polarIso_mul_polarIso M)
      (isHermitian_polarSupport M) (polarSupport_mul_polarSupport M)
  rw [← hV, ← hR, ← Matrix.mul_assoc, polarIso_mul_polarPos]

/-- **The partial isometry vanishes on the kernel.** If `M Y = 0`, then `V Y = 0` for the partial
isometry `V` of the polar decomposition `M = V P`: then `P Y = 0`, so `Π Y = 0` for the support
projector `Π = V†V` of `P`. -/
theorem polarIso_mul_eq_zero {ρ : Type*} {M : Matrix ι κ ℂ} {Y : Matrix κ ρ ℂ} (h : M * Y = 0) :
    polarIso M * Y = 0 := by
  have hH : (polarPos M)ᴴ = polarPos M := (posSemidef_polarPos M).isHermitian.eq
  have hP : polarPos M * Y = 0 := by
    rw [← conjTranspose_mul_self_eq_zero]
    have : (polarPos M * Y)ᴴ * (polarPos M * Y) = (M * Y)ᴴ * (M * Y) := by
      simp only [conjTranspose_mul, hH, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (polarPos M) (polarPos M) Y, polarPos_mul_polarPos,
        Matrix.mul_assoc]
    rw [this, h, Matrix.mul_zero]
  have hS : polarSupport M * Y = 0 := by
    obtain ⟨R, hR⟩ := exists_polarPos_mul_eq_polarSupport M
    rw [← (isHermitian_polarSupport M).eq, ← hR, conjTranspose_mul, hH, Matrix.mul_assoc, hP,
      Matrix.mul_zero]
  rw [← conjTranspose_mul_self_eq_zero, conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (polarIso M)ᴴ, conjTranspose_polarIso_mul_polarIso, hS, Matrix.mul_zero]

variable {κ' : Type*} [Fintype κ'] [DecidableEq κ']

omit [Fintype κ'] [DecidableEq κ'] in
/-- If `Mᴴ M' = 0`, then `Vᴴ M' = 0` for the partial isometry `V` of `M`. -/
theorem conjTranspose_polarIso_mul_eq_zero {M : Matrix ι κ ℂ} {M' : Matrix ι κ' ℂ}
    (h : Mᴴ * M' = 0) : (polarIso M)ᴴ * M' = 0 := by
  obtain ⟨R, hR⟩ := exists_polarIso_eq_mul M
  rw [hR, conjTranspose_mul, Matrix.mul_assoc, h, Matrix.mul_zero]

/-- If `Mᴴ M' = 0`, the partial isometries of `M` and `M'` have orthogonal ranges:
`Vᴴ V' = 0`. -/
theorem conjTranspose_polarIso_mul_polarIso_eq_zero {M : Matrix ι κ ℂ} {M' : Matrix ι κ' ℂ}
    (h : Mᴴ * M' = 0) : (polarIso M)ᴴ * polarIso M' = 0 := by
  obtain ⟨R', hR'⟩ := exists_polarIso_eq_mul M'
  rw [hR', ← Matrix.mul_assoc, conjTranspose_polarIso_mul_eq_zero h, Matrix.zero_mul]

end Orthogonal

end Matrix

end

section

open scoped BigOperators Matrix ComplexOrder MatrixOrder

open Matrix

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
/-- A product of two finite sums whose cross terms vanish is the sum of the diagonal
products. -/
theorem sum_mul_sum_of_mul_eq_zero {β α γ : Type*} [Fintype β] [Fintype κ]
    {X : β → Matrix α κ ℂ} {Y : β → Matrix κ γ ℂ} (h : ∀ j j', j ≠ j' → X j * Y j' = 0) :
    (∑ j, X j) * (∑ j, Y j) = ∑ j, X j * Y j := by
  classical
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_sum, Finset.sum_eq_single j (fun j' _ hj' => h j j' (Ne.symm hj'))
    (fun hj => absurd (Finset.mem_univ j) hj)]

variable {β : Type*} [Fintype β] {κj : β → Type*} [∀ j, Fintype (κj j)]
  [∀ j, DecidableEq (κj j)]

/-- **The polar decomposition of an orthogonal sum.** Let `B = ∑ⱼ cⱼ Bⱼ Kⱼᴴ` with `cⱼ > 0`,
isometries `Kⱼ` with orthogonal ranges (`Kⱼᴴ Kⱼ = 1`, `Kⱼᴴ Kⱼ' = 0` for `j ≠ j'`), and
`Bⱼᴴ Bⱼ' = 0` for `j ≠ j'`. Then the partial isometry of `B` is `∑ⱼ Vⱼ Kⱼᴴ` and its positive part
is `∑ⱼ cⱼ Kⱼ Pⱼ Kⱼᴴ`, with `Bⱼ = Vⱼ Pⱼ`.

This is the block form of the positive part asserted in arXiv:2307.01696, Supplemental Material,
eq. (S5), for blocks of multiplicity one whose states are orthogonal; the source does not state
the orthogonality, without which the block form fails. -/
theorem polarIso_sum_of_orthogonal {B : (j : β) → Matrix ι (κj j) ℂ}
    (hB : ∀ j j', j ≠ j' → (B j)ᴴ * B j' = 0) {c : β → ℝ} (hc : ∀ j, 0 < c j)
    {K : (j : β) → Matrix κ (κj j) ℂ} (hK : ∀ j, (K j)ᴴ * K j = 1)
    (hK' : ∀ j j', j ≠ j' → (K j)ᴴ * K j' = 0) :
    polarIso (∑ j, (c j : ℂ) • (B j * (K j)ᴴ)) = ∑ j, polarIso (B j) * (K j)ᴴ ∧
      polarPos (∑ j, (c j : ℂ) • (B j * (K j)ᴴ)) =
        ∑ j, (c j : ℂ) • (K j * polarPos (B j) * (K j)ᴴ) := by
  set W := ∑ j, polarIso (B j) * (K j)ᴴ
  set Q := ∑ j, (c j : ℂ) • (K j * polarPos (B j) * (K j)ᴴ)
  set E := ∑ j, K j * polarSupport (B j) * (K j)ᴴ
  choose R hR using fun j => exists_polarPos_mul_eq_polarSupport (B j)
  set R' := ∑ j, ((c j : ℂ)⁻¹) • (K j * R j * (K j)ᴴ)
  -- Products are normalized to right-associated form; every cross term contains `Kⱼᴴ Kⱼ'`.
  have hKr : ∀ j j' (Y : Matrix (κj j') κ ℂ), j ≠ j' →
      (K j)ᴴ * (K j' * Y) = 0 := fun j j' Y h => by
    rw [← Matrix.mul_assoc, hK' j j' h, Matrix.zero_mul]
  have hKd : ∀ j (Y : Matrix (κj j) κ ℂ), (K j)ᴴ * (K j * Y) = Y :=
    fun j Y => by rw [← Matrix.mul_assoc, hK j, Matrix.one_mul]
  have hVr : ∀ j j' (Y : Matrix (κj j') κ ℂ), j ≠ j' →
      (polarIso (B j))ᴴ * (polarIso (B j') * Y) = 0 := fun j j' Y h => by
    rw [← Matrix.mul_assoc, conjTranspose_polarIso_mul_polarIso_eq_zero (hB j j' h),
      Matrix.zero_mul]
  have hVd : ∀ j (Y : Matrix (κj j) κ ℂ),
      (polarIso (B j))ᴴ * (polarIso (B j) * Y) = polarSupport (B j) * Y := fun j Y => by
    rw [← Matrix.mul_assoc, conjTranspose_polarIso_mul_polarIso]
  have hVP : ∀ j (Y : Matrix (κj j) κ ℂ),
      polarIso (B j) * (polarPos (B j) * Y) = B j * Y := fun j Y => by
    rw [← Matrix.mul_assoc, polarIso_mul_polarPos]
  have hSS : ∀ j (Y : Matrix (κj j) κ ℂ),
      polarSupport (B j) * (polarSupport (B j) * Y) = polarSupport (B j) * Y := fun j Y => by
    rw [← Matrix.mul_assoc, polarSupport_mul_polarSupport]
  have hSP : ∀ j (Y : Matrix (κj j) κ ℂ),
      polarSupport (B j) * (polarPos (B j) * Y) = polarPos (B j) * Y := fun j Y => by
    rw [← Matrix.mul_assoc, polarSupport_mul_polarPos]
  have hPR : ∀ j (Y : Matrix (κj j) κ ℂ),
      polarPos (B j) * (R j * Y) = polarSupport (B j) * Y := fun j Y => by
    rw [← Matrix.mul_assoc, hR j]
  -- `B = W Q`.
  have hWQ : ∑ j, (c j : ℂ) • (B j * (K j)ᴴ) = W * Q := by
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.mul_smul, Matrix.mul_assoc, hKr j j' _ h, Matrix.mul_zero, smul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_smul, Matrix.mul_assoc, hKd, hVP]
  -- `Q ≥ 0`.
  have hQ : Q.PosSemidef := posSemidef_sum _ fun j _ =>
    ((posSemidef_polarPos (B j)).mul_mul_conjTranspose_same (K j)).smul
      (Complex.zero_le_real.mpr (hc j).le)
  -- `Wᴴ W = E`.
  have hWW : Wᴴ * W = E := by
    rw [conjTranspose_sum]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.mul_assoc, hVr j j' _ h, Matrix.mul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_assoc, hVd]
  -- `E` is a Hermitian idempotent.
  have hE : E.IsHermitian := by
    rw [IsHermitian, conjTranspose_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      (isHermitian_polarSupport (B j)).eq, Matrix.mul_assoc]
  have hEE : E * E = E := by
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.mul_assoc, hKr j j' _ h, Matrix.mul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_assoc, hKd, hSS]
  -- `E` and `Q` have the same range.
  have hEQ : E * Q = Q := by
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.mul_smul, Matrix.mul_assoc, hKr j j' _ h, Matrix.mul_zero, smul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mul_smul, Matrix.mul_assoc, hKd, hSP]
  have hQR : Q * R' = E := by
    rw [sum_mul_sum_of_mul_eq_zero fun j j' h => by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hKr j j' _ h,
        Matrix.mul_zero, smul_zero]]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcj : (c j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hc j).ne'
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, hKd, hPR, smul_smul,
      inv_mul_cancel₀ hcj, one_smul]
  have hran := range_mulVecLin_eq_of_mul_eq hEQ hQR
  exact ⟨polarIso_eq_of_eq_mul hWQ hQ hWW hE hEE hran,
    polarPos_eq_of_eq_mul hWQ hQ hWW hE hEE hran⟩

end Matrix

end

section

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **The support projector of a matrix supported on a set of columns.** If the columns of `M`
outside `S` vanish and `M` is injective on the vectors supported on `S`, then the support
projector `Π` of the polar decomposition of `M` is the coordinate projector onto `S`.

arXiv:2307.01696, Supplemental Material, "Proof of Lemma 1 and extension to non-normal tensors":
`V†V = Π` with `Π` the projector onto the range of `P`. -/
theorem polarSupport_eq_diagonal_of_support {M : Matrix ι κ ℂ} {S : Set κ}
    [DecidablePred (· ∈ S)] (h0 : ∀ i p, p ∉ S → M i p = 0)
    (hinj : ∀ x : κ → ℂ, (∀ p, p ∉ S → x p = 0) → M *ᵥ x = 0 → x = 0) :
    polarSupport M = diagonal fun p => if p ∈ S then 1 else 0 := by
  set E : Matrix κ κ ℂ := diagonal fun p => if p ∈ S then 1 else 0 with hEdef
  have hEh : Eᴴ = E := by
    rw [hEdef, diagonal_conjTranspose]
    congr 1
    funext p
    split_ifs <;> simp_all
  have hME : M * E = M := by
    ext i p
    rw [hEdef, mul_diagonal]
    by_cases hp : p ∈ S
    · simp [hp]
    · simp [hp, h0 i p hp]
  have hPh : (polarPos M)ᴴ = polarPos M := (posSemidef_polarPos M).isHermitian
  have hSh : (polarSupport M)ᴴ = polarSupport M := isHermitian_polarSupport M
  have h1 : M * (1 - E) = 0 := by rw [Matrix.mul_sub, Matrix.mul_one, hME, sub_self]
  have h2 : polarPos M * (1 - E) = 0 := by
    refine conjTranspose_mul_self_eq_zero.mp ?_
    rw [conjTranspose_mul, hPh, Matrix.mul_assoc, ← Matrix.mul_assoc (polarPos M),
      polarPos_mul_polarPos, Matrix.mul_assoc, h1, Matrix.mul_zero, Matrix.mul_zero]
  obtain ⟨R, hR⟩ := exists_polarPos_mul_eq_polarSupport M
  have h3 : polarSupport M = polarSupport M * E := by
    have h : polarSupport M * (1 - E) = 0 := by
      rw [← hSh, ← hR, conjTranspose_mul, hPh, Matrix.mul_assoc, h2, Matrix.mul_zero]
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h
  have h4 : E = E * polarSupport M := by
    have hX : M * (E * (1 - polarSupport M)) = 0 := by
      rw [← Matrix.mul_assoc, hME, Matrix.mul_sub, Matrix.mul_one, mul_polarSupport, sub_self]
    have h : E * (1 - polarSupport M) = 0 := by
      ext p c
      have hx := hinj (fun p => (E * (1 - polarSupport M)) p c)
        (fun p hp => by simp [hEdef, diagonal_mul, hp]) (funext fun i => by
          have := congrFun (congrFun hX i) c
          simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
      simpa using congrFun hx p
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h
  calc polarSupport M = (polarSupport M)ᴴ := hSh.symm
    _ = (polarSupport M * E)ᴴ := by rw [← h3]
    _ = E * polarSupport M := by rw [conjTranspose_mul, hEh, hSh]
    _ = E := h4.symm

end Matrix

end
