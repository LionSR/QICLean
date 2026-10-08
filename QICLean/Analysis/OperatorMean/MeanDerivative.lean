/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.PowerDerivative
import QICLean.Analysis.OperatorMean.WeightedGeometricMean

/-!
# Derivatives of the weighted geometric mean and normalized derivative maps

For positive definite `A`, `B` and `0 ≤ p ≤ 1`, the mean `M = A #_p B` is
differentiable in each argument along Hermitian matrices. Differentiating
`M = A^{1/2} (A^{-1/2} B A^{-1/2})^p A^{1/2}` in `B` gives
\[
  \partial_B M[H] = A^{1/2}\, D\bigl(C^p\bigr)\bigl[A^{-1/2} H A^{-1/2}\bigr]\, A^{1/2},
  \qquad C = A^{-1/2} B A^{-1/2},
\]
and exchange symmetry `A #_p B = B #_{1-p} A` gives the derivative in `A`. Both
are completely positive, and the homogeneity of the mean gives the Euler
identities `∂_B M[B] = p M` and `∂_A M[A] = (1 - p) M`.

At a child `D` of positive edge weight `w`, the normalized derivative map is
\[
  \Phi_D(Z) = \frac1w\, M^{-1/2}\, \partial_D M\bigl[D^{1/2} Z D^{1/2}\bigr]\, M^{-1/2}.
\]
It is completely positive and unital.

## Main definitions

* `Matrix.rpowDeriv p C` — the derivative of `X ↦ X ^ p` at `C`, for `0 ≤ p ≤ 1`,
  including the endpoints `p = 0` (zero map) and `p = 1` (identity).
* `Matrix.geomMeanDerivRight p A B`, `Matrix.geomMeanDerivLeft p A B` — the partial
  derivatives of `A #_p B` in `B` and in `A`.
* `Matrix.normalizedDerivMap L w M D` — the normalization
  `Z ↦ w⁻¹ M^{-1/2} L[D^{1/2} Z D^{1/2}] M^{-1/2}`.

## Main results

* `Matrix.hasFDerivWithinAt_geomMean_right`, `Matrix.hasFDerivWithinAt_geomMean_left` —
  the partial derivatives, within the Hermitian matrices.
* `Matrix.geomMeanDerivRight_self`, `Matrix.geomMeanDerivLeft_self` — the Euler
  identities.
* `Matrix.isNPositiveMap_normalizedDerivMap_right`, `Matrix.normalizedDerivMap_right_one`
  and their left versions — the normalized derivative maps are `k`-positive for every
  `k` and unital (area-law Lemma 7.2, first part).

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, Lemma 7.2 (`transport:cp`), statement lines
  136--144 and proof lines 157--169. The proofs are written independently from the
  paper.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Set Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian matrices, the domain along which matrix means are differentiated. -/
def hermitianSet (n : Type*) [Fintype n] : Set (Matrix n n ℂ) := {X | X.IsHermitian}

/-! ### Real powers with endpoint exponents -/

/-- The derivative of `X ↦ X ^ p` at `C` for `0 ≤ p ≤ 1`: the zero map at `p = 0`,
the identity at `p = 1`, and the Löwner integral `rpowFDeriv p C` in between. -/
noncomputable def rpowDeriv (p : ℝ) (C : Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  if p = 0 then 0 else if p = 1 then ContinuousLinearMap.id ℂ _ else rpowFDeriv p C

/-- A Hermitian matrix within distance `c` of a matrix dominating `c • 1`, `c > 0`, is
positive definite. -/
theorem posDef_of_norm_sub_lt {C X : Matrix n n ℂ} {c : ℝ}
    (hcC : c • (1 : Matrix n n ℂ) ≤ C) (hCh : C.IsHermitian) (hXh : X.IsHermitian)
    (hXC : ‖X - C‖ < c) : X.PosDef := by
  set r := (c - ‖X - C‖) / 2
  have hr : 0 < r := by simp only [r]; linarith
  have hsub : (r • (1 : Matrix n n ℂ) - r • 1 + (X - r • 1)) = X - r • 1 := by abel
  have hXr : (X - r • (1 : Matrix n n ℂ)).PosSemidef := by
    have hcC' : (c - r) • (1 : Matrix n n ℂ) ≤ C - r • 1 := by
      rw [sub_smul]; exact sub_le_sub_right hcC _
    refine posSemidef_of_norm_sub_lt hcC' (hCh.sub (by simp [IsHermitian]))
      (hXh.sub (by simp [IsHermitian])) ?_
    rw [sub_sub_sub_cancel_right]; simp only [r]; linarith
  simpa using (PosDef.one.smul hr).add_posSemidef hXr

set_option linter.unusedDecidableInType false in
/-- Hermitian matrices near a positive definite matrix are positive definite. -/
theorem eventually_posDef_nhdsWithin {C : Matrix n n ℂ} (hC : C.PosDef) :
    ∀ᶠ X in 𝓝[hermitianSet n] C, X.PosDef := by
  obtain ⟨c, hc, hcC⟩ := hC.exists_pos_smul_one_le
  filter_upwards [inter_mem_nhdsWithin (hermitianSet n) (Metric.ball_mem_nhds C hc)]
    with X hX
  obtain ⟨hXh, hXb⟩ := hX
  rw [Metric.mem_ball, dist_eq_norm] at hXb
  exact posDef_of_norm_sub_lt hcC hC.isHermitian hXh hXb

/-- The derivative of `X ↦ X ^ p` at a positive definite `C`, within the Hermitian
matrices, for `0 ≤ p ≤ 1`. -/
theorem hasFDerivWithinAt_rpow_Icc {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    HasFDerivWithinAt (fun X : Matrix n n ℂ ↦ X ^ p) (rpowDeriv p C) (hermitianSet n) C := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [rpowDeriv, ↓reduceIte]
    refine (hasFDerivWithinAt_const (1 : Matrix n n ℂ) C _).congr_of_eventuallyEq ?_
      hC.rpow_zero
    filter_upwards [eventually_posDef_nhdsWithin hC] with X hX
    exact hX.rpow_zero
  rcases eq_or_ne p 1 with rfl | hp1
  · simp only [rpowDeriv, one_ne_zero, ↓reduceIte]
    refine (hasFDerivWithinAt_id C _).congr_of_eventuallyEq ?_ hC.rpow_one
    filter_upwards [eventually_posDef_nhdsWithin hC] with X hX
    exact hX.rpow_one
  simp only [rpowDeriv, hp0, hp1, ↓reduceIte]
  exact hasFDerivWithinAt_rpow hC ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩

omit [Fintype n] [DecidableEq n] in
/-- The identity map is `k`-positive. -/
theorem isNPositiveMap_id (k : ℕ) :
    IsNPositiveMap k (LinearMap.id : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) := fun X hX ↦ by
  convert hX using 1
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

/-- The derivative of a real power `0 ≤ p ≤ 1` is `k`-positive for every `k`. -/
theorem isNPositiveMap_rpowDeriv {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (k : ℕ) : IsNPositiveMap k (rpowDeriv p C).toLinearMap := by
  unfold rpowDeriv
  split_ifs with hp0 hp1
  · simpa using IsNPositiveMap.zero (n := n) k
  · exact isNPositiveMap_id k
  · exact isNPositiveMap_rpowFDeriv hC
      ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩ k

/-- The Euler identity `D(C ^ p)[C] = p C ^ p` for `0 ≤ p ≤ 1`. -/
theorem rpowDeriv_self {C : Matrix n n ℂ} (hC : C.PosDef) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    rpowDeriv p C C = p • C ^ p := by
  unfold rpowDeriv
  split_ifs with hp0 hp1
  · simp [hp0]
  · simp [hp1, hC.rpow_one]
  · exact rpowFDeriv_self hC ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩

/-! ### Partial derivatives of the mean -/

/-- The sandwich `H ↦ V H V` as a continuous linear map. -/
noncomputable abbrev sandwichL (V : Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  ContinuousLinearMap.mulLeftRight ℂ (Matrix n n ℂ) V V

theorem sandwichL_apply (V H : Matrix n n ℂ) : sandwichL V H = V * H * V := rfl

/-- A Hermitian sandwich is `k`-positive for every `k`. -/
theorem isNPositiveMap_sandwichL {V : Matrix n n ℂ} (hV : V.IsHermitian) (k : ℕ) :
    IsNPositiveMap k (sandwichL V).toLinearMap := by
  classical
  have h : (sandwichL V).toLinearMap = singleKrausMap V := by
    ext1 H; simp [sandwichL, singleKrausMap, hV.eq]
  rw [h]; exact isNPositiveMap_singleKrausMap V k

/-- The partial derivative of `A #_p B` in the second argument `B`:
`H ↦ A^{1/2} D(C^p)[A^{-1/2} H A^{-1/2}] A^{1/2}` with `C = A^{-1/2} B A^{-1/2}`. -/
noncomputable def geomMeanDerivRight (p : ℝ) (A B : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  sandwichL (A ^ (1 / 2 : ℝ)) ∘L
    rpowDeriv p (A ^ (-(1 / 2) : ℝ) * B * A ^ (-(1 / 2) : ℝ)) ∘L sandwichL (A ^ (-(1 / 2) : ℝ))

/-- The partial derivative of `A #_p B` in the first argument `A`, through exchange
symmetry `A #_p B = B #_{1-p} A`. -/
noncomputable def geomMeanDerivLeft (p : ℝ) (A B : Matrix n n ℂ) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  geomMeanDerivRight (1 - p) B A

/-- **The derivative of the mean in its second argument**, within the Hermitian
matrices, for `0 ≤ p ≤ 1`.

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex`
lines 165--167. -/
theorem hasFDerivWithinAt_geomMean_right {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hB : B.PosDef) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    HasFDerivWithinAt (fun X ↦ geomMean p A X) (geomMeanDerivRight p A B) (hermitianSet n) B := by
  have hai : (A ^ (-(1 / 2) : ℝ)).IsHermitian := hA.rpow_isHermitian _
  have h1 : HasFDerivWithinAt (fun X ↦ sandwichL (A ^ (-(1 / 2) : ℝ)) X)
      (sandwichL (A ^ (-(1 / 2) : ℝ))) (hermitianSet n) B :=
    (sandwichL _).hasFDerivAt.hasFDerivWithinAt
  have hmaps : MapsTo (fun X ↦ sandwichL (A ^ (-(1 / 2) : ℝ)) X) (hermitianSet n)
      (hermitianSet n) := fun X hX ↦ by
    change (A ^ (-(1 / 2) : ℝ) * X * A ^ (-(1 / 2) : ℝ)).IsHermitian
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, hai.eq, hX.eq, Matrix.mul_assoc]
  have h2 := (hasFDerivWithinAt_rpow_Icc (hA.whiten hB) hp).comp B h1 hmaps
  exact (sandwichL (A ^ (1 / 2 : ℝ))).hasFDerivAt.comp_hasFDerivWithinAt B h2

/-- **The derivative of the mean in its first argument**, within the Hermitian
matrices, for `0 ≤ p ≤ 1`.

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex`
line 168 (exchange symmetry). -/
theorem hasFDerivWithinAt_geomMean_left {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hB : B.PosDef) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    HasFDerivWithinAt (fun X ↦ geomMean p X B) (geomMeanDerivLeft p A B) (hermitianSet n) A := by
  have hp' : 1 - p ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  refine (hasFDerivWithinAt_geomMean_right hB hA hp').congr_of_eventuallyEq ?_
    (geomMean_comm hA hB p)
  filter_upwards [eventually_posDef_nhdsWithin hA] with X hX
  exact geomMean_comm hX hB p

/-- **Euler identity in the second argument**: `∂_B M[B] = p M`. -/
theorem geomMeanDerivRight_self {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) : geomMeanDerivRight p A B B = p • geomMean p A B := by
  simp only [geomMeanDerivRight, ContinuousLinearMap.comp_apply, sandwichL_apply]
  rw [rpowDeriv_self (hA.whiten hB) hp, geomMean, mul_smul_comm, smul_mul_assoc]

/-- **Euler identity in the first argument**: `∂_A M[A] = (1 - p) M`. -/
theorem geomMeanDerivLeft_self {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) : geomMeanDerivLeft p A B A = (1 - p) • geomMean p A B := by
  rw [geomMeanDerivLeft, geomMeanDerivRight_self hB hA ⟨by linarith [hp.2], by linarith [hp.1]⟩,
    ← geomMean_comm hA hB]

/-- The partial derivative in the second argument is `k`-positive for every `k`. -/
theorem isNPositiveMap_geomMeanDerivRight {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hB : B.PosDef) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    IsNPositiveMap k (geomMeanDerivRight p A B).toLinearMap := by
  have h1 := isNPositiveMap_sandwichL (hA.rpow_isHermitian (1 / 2)) k
  have h2 := isNPositiveMap_rpowDeriv (hA.whiten hB) hp k
  have h3 := isNPositiveMap_sandwichL (hA.rpow_isHermitian (-(1 / 2))) k
  rw [geomMeanDerivRight, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp]
  exact IsNPositiveMap.comp h1 (IsNPositiveMap.comp h2 h3)

/-- The partial derivative in the first argument is `k`-positive for every `k`. -/
theorem isNPositiveMap_geomMeanDerivLeft {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hB : B.PosDef) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    IsNPositiveMap k (geomMeanDerivLeft p A B).toLinearMap :=
  isNPositiveMap_geomMeanDerivRight hB hA ⟨by linarith [hp.2], by linarith [hp.1]⟩ k

/-! ### Normalized derivative maps -/

/-- The normalization `Z ↦ w⁻¹ M^{-1/2} L[D^{1/2} Z D^{1/2}] M^{-1/2}` of a derivative
map `L` at a child `D` of edge weight `w`, with output `M`.

Area-law paper, display `transport:edge-map`, `06-transport.tex` lines 139--142. -/
noncomputable def normalizedDerivMap (L : Matrix n n ℂ →L[ℂ] Matrix n n ℂ) (w : ℝ)
    (M D : Matrix n n ℂ) : Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  w⁻¹ • (sandwichL (M ^ (-(1 / 2) : ℝ)) ∘L L ∘L sandwichL (D ^ (1 / 2 : ℝ)))

/-- A normalized derivative map is unital when `L[D] = w M` with `w ≠ 0`. -/
theorem normalizedDerivMap_one {L : Matrix n n ℂ →L[ℂ] Matrix n n ℂ} {w : ℝ} (hw : w ≠ 0)
    {M D : Matrix n n ℂ} (hM : M.PosDef) (hD : D.PosDef) (hL : L D = w • M) :
    normalizedDerivMap L w M D 1 = 1 := by
  simp only [normalizedDerivMap, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, sandwichL_apply, Matrix.mul_one,
    hD.rpow_half_mul_rpow_half, hL, mul_smul_comm, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ hw, one_smul]
  have hh := hM.rpow_half_mul_rpow_half
  calc M ^ (-(1 / 2) : ℝ) * M * M ^ (-(1 / 2) : ℝ)
      = M ^ (-(1 / 2) : ℝ) * (M ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ)) * M ^ (-(1 / 2) : ℝ) := by
        rw [hh]
    _ = (M ^ (-(1 / 2) : ℝ) * M ^ (1 / 2 : ℝ)) * (M ^ (1 / 2 : ℝ) * M ^ (-(1 / 2) : ℝ)) := by
        noncomm_ring
    _ = 1 := by rw [hM.rpow_neg_mul_rpow, hM.rpow_mul_rpow_neg, one_mul]

/-- A normalized derivative map of a `k`-positive map with positive weight is `k`-positive. -/
theorem isNPositiveMap_normalizedDerivMap {L : Matrix n n ℂ →L[ℂ] Matrix n n ℂ} {k : ℕ}
    (hL : IsNPositiveMap k L.toLinearMap) {w : ℝ} (hw : 0 ≤ w) {M D : Matrix n n ℂ}
    (hM : M.PosDef) (hD : D.PosDef) :
    IsNPositiveMap k (normalizedDerivMap L w M D).toLinearMap := by
  have h : (normalizedDerivMap L w M D).toLinearMap = ((w⁻¹ : ℝ) : ℂ) •
      ((sandwichL (M ^ (-(1 / 2) : ℝ))).toLinearMap ∘ₗ L.toLinearMap ∘ₗ
        (sandwichL (D ^ (1 / 2 : ℝ))).toLinearMap) := by
    ext1 H
    simp only [normalizedDerivMap, ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_apply,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [← Complex.coe_smul]
  rw [h]
  have h1 := isNPositiveMap_sandwichL (hM.rpow_isHermitian (-(1 / 2))) k
  have h3 := isNPositiveMap_sandwichL (hD.rpow_isHermitian (1 / 2)) k
  exact (IsNPositiveMap.comp h1 (IsNPositiveMap.comp hL h3)).smul_nonneg (inv_nonneg.mpr hw)

/-- **The normalized derivative map at the second child is unital** (edge weight
`p > 0`).

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 143--144 and
168--169. -/
theorem normalizedDerivMap_right_one {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {p : ℝ} (hp : p ∈ Ioc (0 : ℝ) 1) :
    normalizedDerivMap (geomMeanDerivRight p A B) p (geomMean p A B) B 1 = 1 :=
  normalizedDerivMap_one (ne_of_gt hp.1) (hA.geomMean hB p) hB
    (geomMeanDerivRight_self hA hB (Ioc_subset_Icc_self hp))

/-- **The normalized derivative map at the first child is unital** (edge weight
`1 - p > 0`).

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 143--144 and
168--169. -/
theorem normalizedDerivMap_left_one {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {p : ℝ} (hp : p ∈ Ico (0 : ℝ) 1) :
    normalizedDerivMap (geomMeanDerivLeft p A B) (1 - p) (geomMean p A B) A 1 = 1 :=
  normalizedDerivMap_one (by linarith [hp.2]) (hA.geomMean hB p) hA
    (geomMeanDerivLeft_self hA hB (Ico_subset_Icc_self hp))

/-- **The normalized derivative map at the second child is completely positive.**

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 143--144 and
164--167. -/
theorem isNPositiveMap_normalizedDerivMap_right {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hB : B.PosDef) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    IsNPositiveMap k
      (normalizedDerivMap (geomMeanDerivRight p A B) p (geomMean p A B) B).toLinearMap :=
  isNPositiveMap_normalizedDerivMap (isNPositiveMap_geomMeanDerivRight hA hB hp k) hp.1
    (hA.geomMean hB p) hB

/-- **The normalized derivative map at the first child is completely positive.**

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 143--144 and
168. -/
theorem isNPositiveMap_normalizedDerivMap_left {A B : Matrix n n ℂ} (hA : A.PosDef)
    (hB : B.PosDef) {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    IsNPositiveMap k
      (normalizedDerivMap (geomMeanDerivLeft p A B) (1 - p) (geomMean p A B) A).toLinearMap :=
  isNPositiveMap_normalizedDerivMap (isNPositiveMap_geomMeanDerivLeft hA hB hp k)
    (by linarith [hp.2]) (hA.geomMean hB p) hA

end Matrix
