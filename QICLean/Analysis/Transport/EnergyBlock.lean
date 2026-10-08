/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Defs
import QICLean.Channel.Schwarz.TwoVariable
import QICLean.Channel.Schwarz.PositiveMapProperties

/-!
# The auxiliary block tree and the energy of the filtered vector

Fix a finite mean tree `T'` with positive definite inputs `A_j`, root `M`, and a positive
semidefinite operator `h` that commutes with `A_j` for every leaf outside a finite set
`S` of split leaves. With `W = ∑_{j ∈ S} π_j` and `s = 1/4`,
$$\langle v,hv\rangle\le 2\operatorname{Re}\langle M^{-s}v,hM^{s}v\rangle
 +\frac32 W\sum_{j\in S}\pi_j\int m_s(u)\operatorname{Tr}(\sigma_{j,u}\mathsf D_j)\,du,$$
where `σ_{j,u}` are the transport states of `v` and `𝖣_j` is the skew square of
`O_j = A_j^{-1/2} h A_j^{1/2}`. This is the generic matrix part of the energy estimate of
the area-law paper, Proposition 7.4 (`06-transport.tex` lines 588--766); the factor `W`
from Cauchy--Schwarz is kept separate from the split-leaf sum.

The paper factors `h = T^* T` through the last copy; any factorization works for the
argument, and this file uses `T = h^{1/2}`.

Proof outline (one lemma per paragraph of the source):

* `exists_auxBlock` — the auxiliary second diagonal block `B_j`, with
  `Y_j^* Z_j = O_j` and `(Y_j - Z_j)^*(Y_j - Z_j) = 𝖣_j`, and `Y_j = Z_j` on unsplit
  leaves (lines 604--656);
* `norm_sq_errorVec_le` — the block-rotation identity, both Fourier kernels `q_±`,
  Cauchy--Schwarz and the matrix Schwarz inequality give
  `‖E_± v‖² ≤ (1/4) W ∑_{j∈S} π_j ∫ m_s Tr(σ_{j,u} 𝖣_j)` (lines 658--729);
* `re_inner_errorVec_eq`, `re_inner_errorVec_ge` — the similarity pairing
  (lines 750--760).

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open MeasureTheory

namespace Matrix.Transport

open MeanTree

variable {n : Type*} [Fintype n] [DecidableEq n] {J : Type*} [Fintype J] [DecidableEq J]

/-- `Y = B^{1/2} T A^{-1/2}` with `T = h^{1/2}` (`06-transport.tex`,
display `transport:unsplit-block`). -/
noncomputable def auxY (A B h : Matrix n n ℂ) : Matrix n n ℂ :=
  B ^ (1 / 2 : ℝ) * CFC.sqrt h * A ^ (-(1 / 2) : ℝ)

/-- `Z = B^{-1/2} T A^{1/2}` with `T = h^{1/2}` (`06-transport.tex`,
display `transport:unsplit-block`). -/
noncomputable def auxZ (A B h : Matrix n n ℂ) : Matrix n n ℂ :=
  B ^ (-(1 / 2) : ℝ) * CFC.sqrt h * A ^ (1 / 2 : ℝ)

omit [DecidableEq n] in
/-- Moving matrices across the Euclidean pairing:
`⟨X v, Y w⟩ = ⟨v, X^* Y w⟩`. -/
theorem star_mulVec_dotProduct_mulVec (X Y : Matrix n n ℂ) (v w : n → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (Y *ᵥ w) = star v ⬝ᵥ ((Xᴴ * Y) *ᵥ w) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-! ### The kernel projection of `h` and the auxiliary block -/

/-- The projection onto the kernel of a Hermitian matrix `h`, through the functional
calculus. It regularizes the singular Gram operators of the auxiliary block. -/
noncomputable def kerProj (h : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) h

theorem sqrt_eq_cfc_real {h : Matrix n n ℂ} (hh : h.PosSemidef) :
    CFC.sqrt h = cfc Real.sqrt h := by
  rw [CFC.sqrt_eq_real_sqrt h (Matrix.nonneg_iff_posSemidef.mpr hh),
    cfcₙ_eq_cfc (hf0 := by simp)]

theorem kerProj_mul_sqrt {h : Matrix n n ℂ} (hh : h.PosSemidef) :
    kerProj h * CFC.sqrt h = 0 := by
  have hfin := (Matrix.finite_real_spectrum (A := h))
  rw [sqrt_eq_cfc_real hh, kerProj, ← cfc_mul _ _ h (hfin.continuousOn _) (hfin.continuousOn _)]
  refine (cfc_congr fun x _ => ?_).trans (cfc_zero ℝ h)
  split_ifs with hx <;> simp [hx]

theorem sqrt_mul_kerProj {h : Matrix n n ℂ} (hh : h.PosSemidef) :
    CFC.sqrt h * kerProj h = 0 := by
  have hfin := (Matrix.finite_real_spectrum (A := h))
  rw [sqrt_eq_cfc_real hh, kerProj, ← cfc_mul _ _ h (hfin.continuousOn _) (hfin.continuousOn _)]
  refine (cfc_congr fun x _ => ?_).trans (cfc_zero ℝ h)
  split_ifs with hx <;> simp [hx]

theorem posSemidef_kerProj (h : Matrix n n ℂ) : (kerProj h).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact cfc_nonneg fun x _ => by split_ifs <;> norm_num

theorem isUnit_sqrt_add_kerProj {h : Matrix n n ℂ} (hh : h.PosSemidef) :
    IsUnit (CFC.sqrt h + kerProj h) := by
  have hfin := (Matrix.finite_real_spectrum (A := h))
  rw [sqrt_eq_cfc_real hh, kerProj, ← cfc_add (a := h) _ _ (hfin.continuousOn _) (hfin.continuousOn _),
    isUnit_cfc_iff _ h (hfin.continuousOn _)]
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hh) hx
  split_ifs with h0
  · simp [h0]
  · have : 0 < Real.sqrt x := Real.sqrt_pos.mpr (lt_of_le_of_ne hx0 (Ne.symm h0))
    simp only [add_zero]; exact this.ne'

/-- The regularized Gram operator `T X T + P₀` is positive definite for positive definite
`X`, where `T = h^{1/2}` and `P₀` is the kernel projection of `h`. -/
theorem posDef_sqrt_mul_mul_sqrt_add_kerProj {h X : Matrix n n ℂ} (hh : h.PosSemidef)
    (hX : X.PosDef) : (CFC.sqrt h * X * CFC.sqrt h + kerProj h).PosDef := by
  have hT : (CFC.sqrt h)ᴴ = CFC.sqrt h := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
  have h1 : (CFC.sqrt h * X * CFC.sqrt h).PosSemidef := by
    simpa [hT] using hX.posSemidef.mul_mul_conjTranspose_same (CFC.sqrt h)
  have h2 := posSemidef_kerProj h
  refine (h1.add h2).posDef_iff_isUnit.mpr (mulVec_injective_iff_isUnit.mp fun x y hxy => ?_)
  rw [← sub_eq_zero, ← mulVec_sub] at hxy
  rw [← sub_eq_zero]
  set z := x - y
  have hsum : star z ⬝ᵥ ((CFC.sqrt h * X * CFC.sqrt h) *ᵥ z) + star z ⬝ᵥ (kerProj h *ᵥ z) = 0 := by
    rw [← dotProduct_add, ← add_mulVec, hxy, dotProduct_zero]
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (h1.dotProduct_mulVec_nonneg z)
    (h2.dotProduct_mulVec_nonneg z)).mp hsum
  have hTz : CFC.sqrt h *ᵥ z = 0 := by
    have h0 : star (CFC.sqrt h *ᵥ z) ⬝ᵥ (X *ᵥ (CFC.sqrt h *ᵥ z)) = 0 := by
      rw [star_mulVec_dotProduct_mulVec, hT, mulVec_mulVec, ha]
    by_contra hne
    exact (hX.dotProduct_mulVec_pos hne).ne' h0
  have hPz := (h2.dotProduct_mulVec_zero_iff).mp hb
  apply mulVec_injective_iff_isUnit.mpr (isUnit_sqrt_add_kerProj hh)
  rw [add_mulVec, hTz, hPz, add_zero, mulVec_zero]

omit [DecidableEq n] in
/-- Conjugating a positive definite matrix by a positive definite matrix. -/
theorem posDef_mul_mul_of_posDef {X Y : Matrix n n ℂ} (hX : X.PosDef) (hY : Y.PosDef) :
    (X * Y * X).PosDef := by
  classical
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := Y) hX.isUnit).mpr hY
  rwa [star_eq_conjTranspose, hX.isHermitian.eq] at h

/-- `Y^* Z = A^{-1/2} h A^{1/2}` for every positive definite `B`
(`06-transport.tex` lines 625--630). -/
theorem auxY_conjTranspose_mul_auxZ {A B h : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hh : h.PosSemidef) :
    (auxY A B h)ᴴ * auxZ A B h = A ^ (-(1 / 2) : ℝ) * h * A ^ (1 / 2 : ℝ) := by
  have hT : (CFC.sqrt h)ᴴ = CFC.sqrt h := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
  have hTT : CFC.sqrt h * CFC.sqrt h = h :=
    CFC.sqrt_mul_sqrt_self h (Matrix.nonneg_iff_posSemidef.mpr hh)
  rw [auxY, auxZ, conjTranspose_mul, conjTranspose_mul, hT, (hB.rpow_isHermitian _).eq,
    (hA.rpow_isHermitian _).eq]
  calc _ = A ^ (-(1 / 2) : ℝ) * CFC.sqrt h * (B ^ (1 / 2 : ℝ) * B ^ (-(1 / 2) : ℝ)) *
        CFC.sqrt h * A ^ (1 / 2 : ℝ) := by noncomm_ring
    _ = _ := by
      rw [hB.rpow_mul_rpow_neg, Matrix.mul_one]; conv_rhs => rw [← hTT]
      noncomm_ring

omit [DecidableEq n] in
/-- The ring identity behind `Y^*Y = |O^*|` and `Z^*Z = |O|`: if
`B (T x x T + P₀) B = T y y T + P₀` with `P₀ T = T P₀ = 0` and `[P₀, B] = 0`, then
`(x T B T x)² = (x T T y)(y T T x)`. -/
theorem sandwich_sq_eq {T Q x y B : Matrix n n ℂ} (hQT : Q * T = 0) (hTQ : T * Q = 0)
    (hQB : Q * B = B * Q) (hB : B * (T * (x * x) * T + Q) * B = T * (y * y) * T + Q) :
    (x * T * B * T * x) * (x * T * B * T * x) = (x * (T * T) * y) * (y * (T * T) * x) := by
  have e : B * (T * (x * x) * T) * B = T * (y * y) * T + Q - B * B * Q := by
    have : B * Q * B = B * B * Q := by
      rw [Matrix.mul_assoc, hQB, ← Matrix.mul_assoc]
    rw [← hB, mul_add, add_mul, this]; abel
  calc _ = x * T * (B * (T * (x * x) * T) * B) * T * x := by noncomm_ring
    _ = x * (T * T) * y * (y * (T * T) * x) + x * (T * Q) * T * x -
        x * T * B * B * (Q * T) * x := by rw [e]; noncomm_ring
    _ = _ := by rw [hQT, hTQ]; noncomm_ring

/-- The kernel projection commutes with the regularized Gram operator. -/
theorem commute_kerProj_sandwich {h : Matrix n n ℂ} (hh : h.PosSemidef) (X : Matrix n n ℂ) :
    Commute (kerProj h) (CFC.sqrt h * X * CFC.sqrt h + kerProj h) := by
  change kerProj h * (_ + _) = (_ + _) * kerProj h
  rw [mul_add, add_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, kerProj_mul_sqrt hh, zero_mul,
    zero_mul, Matrix.mul_assoc, sqrt_mul_kerProj hh, mul_zero]

/-- **The auxiliary block** (`06-transport.tex` lines 604--656): for a positive definite
`A` and positive semidefinite `h` there is a positive definite `B` with
`Y^* Z = A^{-1/2} h A^{1/2}`, `(Y - Z)^*(Y - Z) = 𝖣`, and `Y = Z` when `A` commutes
with `h`. The source builds `B` from the polar decomposition on unsplit leaves and from
display `transport:rank-deficient-B` on split leaves, never inverting `h` on its kernel. -/
theorem exists_auxBlock {A h : Matrix n n ℂ} (hA : A.PosDef) (hh : h.PosSemidef) :
    ∃ B : Matrix n n ℂ, B.PosDef ∧
      (auxY A B h)ᴴ * auxZ A B h = A ^ (-(1 / 2) : ℝ) * h * A ^ (1 / 2 : ℝ) ∧
      (auxY A B h - auxZ A B h)ᴴ * (auxY A B h - auxZ A B h) = skewSquare A h ∧
      (Commute A h → auxY A B h = auxZ A B h) := by
  have hh0 : 0 ≤ h := Matrix.nonneg_iff_posSemidef.mpr hh
  have hT : (CFC.sqrt h)ᴴ = CFC.sqrt h := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
  have hTT : CFC.sqrt h * CFC.sqrt h = h := CFC.sqrt_mul_sqrt_self h hh0
  by_cases hc : Commute A h
  · -- Unsplit leaf: `B = A` and `Y = Z = T` (display `transport:unsplit-block`).
    have hAT : Commute A (CFC.sqrt h) := by
      rw [sqrt_eq_cfc_real hh]; exact (Commute.cfc_real hc.symm _).symm
    have hY : auxY A A h = CFC.sqrt h := by
      rw [auxY, Matrix.mul_assoc, ← (hA.commute_rpow_left hAT _).eq, ← Matrix.mul_assoc,
        hA.rpow_mul_rpow_neg, Matrix.one_mul]
    have hZ : auxZ A A h = CFC.sqrt h := by
      rw [auxZ, Matrix.mul_assoc, ← (hA.commute_rpow_left hAT _).eq, ← Matrix.mul_assoc,
        hA.rpow_neg_mul_rpow, Matrix.one_mul]
    refine ⟨A, hA, auxY_conjTranspose_mul_auxZ hA hA hh, ?_, fun _ => hY.trans hZ.symm⟩
    have hO : A ^ (-(1 / 2) : ℝ) * h * A ^ (1 / 2 : ℝ) = h := by
      rw [Matrix.mul_assoc, ← (hA.commute_rpow_left hc _).eq, ← Matrix.mul_assoc,
        hA.rpow_neg_mul_rpow, Matrix.one_mul]
    simp only [skewSquare, hO, hh.isHermitian.eq, CFC.sqrt_mul_self h hh0, hY, hZ, sub_self,
      mul_zero, add_sub_cancel_right]
  · -- Split leaf: display `transport:rank-deficient-B`, written as a geometric mean of the
    -- two regularized Gram operators.
    set T := CFC.sqrt h with hTdef
    set Q := kerProj h
    have hQT : Q * T = 0 := kerProj_mul_sqrt hh
    have hTQ : T * Q = 0 := sqrt_mul_kerProj hh
    set a := A ^ (1 / 2 : ℝ)
    set ai := A ^ (-(1 / 2) : ℝ)
    have hai : (ai * ai).PosDef := by
      simp only [ai]; rw [hA.rpow_mul_rpow]; exact hA.rpow _
    have haa : (a * a).PosDef := by simp only [a]; rw [hA.rpow_half_mul_rpow_half]; exact hA
    set U := T * (ai * ai) * T + Q with hUdef
    set V := T * (a * a) * T + Q with hVdef
    have hU : U.PosDef := posDef_sqrt_mul_mul_sqrt_add_kerProj hh hai
    have hV : V.PosDef := posDef_sqrt_mul_mul_sqrt_add_kerProj hh haa
    set C := U ^ (1 / 2 : ℝ) * V * U ^ (1 / 2 : ℝ)
    have hC : C.PosDef := posDef_mul_mul_of_posDef (hU.rpow _) hV
    set B := U ^ (-(1 / 2) : ℝ) * C ^ (1 / 2 : ℝ) * U ^ (-(1 / 2) : ℝ) with hBdef
    have hB : B.PosDef := posDef_mul_mul_of_posDef (hU.rpow _) (hC.rpow _)
    have hUU : U ^ (-(1 / 2) : ℝ) * U * U ^ (-(1 / 2) : ℝ) = 1 := by
      have : U ^ (-(1 / 2) : ℝ) * U = U ^ (1 / 2 : ℝ) := by
        nth_rw 2 [← hU.rpow_one]; rw [hU.rpow_mul_rpow]; norm_num
      rw [this, hU.rpow_mul_rpow_neg]
    have hBUB : B * U * B = V := by
      calc B * U * B = U ^ (-(1 / 2) : ℝ) * C ^ (1 / 2 : ℝ) *
            (U ^ (-(1 / 2) : ℝ) * U * U ^ (-(1 / 2) : ℝ)) * C ^ (1 / 2 : ℝ) *
              U ^ (-(1 / 2) : ℝ) := by simp only [B]; noncomm_ring
        _ = U ^ (-(1 / 2) : ℝ) * U ^ (1 / 2 : ℝ) * V * (U ^ (1 / 2 : ℝ) *
              U ^ (-(1 / 2) : ℝ)) := by
          rw [hUU, Matrix.mul_one, Matrix.mul_assoc (U ^ (-(1 / 2) : ℝ)) (C ^ (1 / 2 : ℝ))
            (C ^ (1 / 2 : ℝ)), hC.rpow_half_mul_rpow_half]; simp only [C]; noncomm_ring
        _ = V := by rw [hU.rpow_neg_mul_rpow, hU.rpow_mul_rpow_neg, Matrix.one_mul,
          Matrix.mul_one]
    set Bi := B ^ (-1 : ℝ)
    have hBBi : B * Bi = 1 := by
      have := hB.rpow_mul_rpow_neg 1; rwa [hB.rpow_one] at this
    have hBiB : Bi * B = 1 := by
      have := hB.rpow_neg_mul_rpow 1; rwa [hB.rpow_one] at this
    have hBiVBi : Bi * V * Bi = U := by
      rw [← hBUB]
      calc Bi * (B * U * B) * Bi = (Bi * B) * U * (B * Bi) := by noncomm_ring
        _ = U := by rw [hBiB, hBBi, Matrix.one_mul, Matrix.mul_one]
    have hQU : Commute Q U := commute_kerProj_sandwich hh _
    have hQV : Commute Q V := commute_kerProj_sandwich hh _
    have hQUr : ∀ r : ℝ, Commute Q (U ^ r) := fun r => (hU.commute_rpow_left hQU.symm r).symm
    have hQC : Commute Q C := ((hQUr _).mul_right hQV).mul_right (hQUr _)
    have hQB : Commute Q B :=
      ((hQUr _).mul_right (hC.commute_rpow_left hQC.symm _).symm).mul_right (hQUr _)
    have hQBi : Commute Q Bi := (hB.commute_rpow_left hQB.symm _).symm
    have hYZ := auxY_conjTranspose_mul_auxZ hA hB hh
    refine ⟨B, hB, hYZ, ?_, fun h' => absurd h' hc⟩
    have hYY : (auxY A B h)ᴴ * auxY A B h = ai * T * B * T * ai := by
      rw [auxY, conjTranspose_mul, conjTranspose_mul, ← hTdef, hT, (hB.rpow_isHermitian _).eq,
        (hA.rpow_isHermitian _).eq]
      calc _ = ai * T * (B ^ (1 / 2 : ℝ) * B ^ (1 / 2 : ℝ)) * T * ai := by noncomm_ring
        _ = _ := by rw [hB.rpow_half_mul_rpow_half]
    have hZZ : (auxZ A B h)ᴴ * auxZ A B h = a * T * Bi * T * a := by
      rw [auxZ, conjTranspose_mul, conjTranspose_mul, ← hTdef, hT, (hB.rpow_isHermitian _).eq,
        (hA.rpow_isHermitian _).eq]
      calc _ = a * T * (B ^ (-(1 / 2) : ℝ) * B ^ (-(1 / 2) : ℝ)) * T * a := by noncomm_ring
        _ = _ := by rw [hB.rpow_mul_rpow]; norm_num; rfl
    have hO : A ^ (-(1 / 2) : ℝ) * h * A ^ (1 / 2 : ℝ) = ai * (T * T) * a := by rw [hTT]
    have hOH : (ai * (T * T) * a)ᴴ = a * (T * T) * ai := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_mul, hT,
        (hA.rpow_isHermitian _).eq, (hA.rpow_isHermitian _).eq]
      simp only [a, ai, Matrix.mul_assoc]
    have hY0 : 0 ≤ ai * T * B * T * ai := by
      rw [← hYY]; exact Matrix.nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self _)
    have hZ0 : 0 ≤ a * T * Bi * T * a := by
      rw [← hZZ]; exact Matrix.nonneg_iff_posSemidef.mpr (posSemidef_conjTranspose_mul_self _)
    have hsq1 : CFC.sqrt ((ai * (T * T) * a) * (ai * (T * T) * a)ᴴ) = ai * T * B * T * ai := by
      rw [CFC.sqrt_eq_iff _ _ (Matrix.nonneg_iff_posSemidef.mpr
          (posSemidef_self_mul_conjTranspose _)) hY0, hOH]
      exact sandwich_sq_eq hQT hTQ hQB.eq (by rw [← hUdef, ← hVdef, hBUB])
    have hsq2 : CFC.sqrt ((ai * (T * T) * a)ᴴ * (ai * (T * T) * a)) = a * T * Bi * T * a := by
      rw [CFC.sqrt_eq_iff _ _ (Matrix.nonneg_iff_posSemidef.mpr
          (posSemidef_conjTranspose_mul_self _)) hZ0, hOH]
      exact sandwich_sq_eq hQT hTQ hQBi.eq (by rw [← hUdef, ← hVdef, hBiVBi])
    have hZY : (auxZ A B h)ᴴ * auxY A B h = (ai * (T * T) * a)ᴴ := by
      rw [← hO, ← hYZ, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [skewSquare]
    rw [hO, hsq1, hsq2, ← hYY, ← hZZ, ← hZY, ← hO, ← hYZ, conjTranspose_sub, sub_mul, mul_sub,
      mul_sub]
    abel

/-! ### Infinitesimal congruence covariance and the block rotation -/

section Rotation

open NormedSpace Set

variable {m : Type*} [Fintype m] [DecidableEq m]

theorem hasDerivAt_star_exp_mul_mul_exp (X P : Matrix m m ℂ) :
    HasDerivAt (fun t : ℝ => star (exp (t • X)) * P * exp (t • X)) (Xᴴ * P + P * X) 0 := by
  have hexp : ∀ Y : Matrix m m ℂ, HasDerivAt (fun t : ℝ => exp (t • Y)) Y 0 := fun Y => by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
  have hstar : ∀ t : ℝ, star (exp (t • X)) = exp (t • Xᴴ) := by
    intro t
    rw [star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial]
  simp_rw [hstar]
  have := ((hexp Xᴴ).mul_const P).mul (hexp X)
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul] at this
  exact this

theorem posDef_star_mul_mul {P S : Matrix m m ℂ} (hP : P.PosDef) (hS : IsUnit S) :
    (star S * P * S).PosDef :=
  (Matrix.IsUnit.posDef_star_left_conjugate_iff hS).mpr hP

theorem geomMeanDeriv_congr {P R : Matrix m m ℂ} (hP : P.PosDef) (hR : R.PosDef) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (X : Matrix m m ℂ) :
    geomMeanDerivLeft p P R (Xᴴ * P + P * X) + geomMeanDerivRight p P R (Xᴴ * R + R * X) =
      Xᴴ * geomMean p P R + geomMean p P R * X := by
  set S : ℝ → Matrix m m ℂ := fun t => exp (t • X)
  set V : ℝ → Matrix m m ℂ := fun t => exp (t • -X)
  have hinv : ∀ t : ℝ, V t * S t = 1 := by
    intro t
    simp only [V, S]
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl X).neg_left.smul_left t).smul_right t),
      ← smul_add, neg_add_cancel, smul_zero, NormedSpace.exp_zero]
  have hSu : ∀ t, IsUnit (S t) := fun t => Matrix.isUnit_exp _
  have hVu : ∀ t, IsUnit (V t) := fun t => Matrix.isUnit_exp _
  have hherm : ∀ (Q : Matrix m m ℂ) (W : Matrix m m ℂ), Q.IsHermitian →
      (star W * Q * W) ∈ hermitianSet m := by
    intro Q W hQ
    change (star W * Q * W).IsHermitian
    unfold IsHermitian
    rw [conjTranspose_mul, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
      hQ.eq, Matrix.mul_assoc]
  have hid : ∀ t, geomMean p (star (S t) * P * S t) R =
      star (S t) * geomMean p P (star (V t) * R * V t) * S t := by
    intro t
    have h := geomMean_star_conj hP (posDef_star_mul_mul hR (hVu t)) (hSu t) p
    have hR' : star (S t) * (star (V t) * R * V t) * S t = R := by
      calc _ = star (V t * S t) * R * (V t * S t) := by rw [star_mul]; noncomm_ring
        _ = R := by rw [hinv, star_one, Matrix.one_mul, Matrix.mul_one]
    rwa [hR'] at h
  -- derivative of the left side
  have ha := hasDerivAt_star_exp_mul_mul_exp X P
  have hb := hasDerivAt_star_exp_mul_mul_exp (-X) R
  have hS0 : S 0 = 1 := by simp [S]
  have hV0 : V 0 = 1 := by simp [V]
  have hL : HasDerivAt (fun t => geomMean p (star (S t) * P * S t) R)
      (geomMeanDerivLeft p P R (Xᴴ * P + P * X)) 0 := by
    have h1 := (hasFDerivWithinAt_geomMean_left hP hR hp).restrictScalars ℝ
    have h2 : HasDerivWithinAt (fun t : ℝ => star (S t) * P * S t) (Xᴴ * P + P * X) univ 0 :=
      ha.hasDerivWithinAt
    have h3 := HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (0 : ℝ) h1 h2
      (fun t _ => hherm P (S t) hP.isHermitian) (by simp [hS0])
    exact h3.hasDerivAt Filter.univ_mem
  have hψ : HasDerivAt (fun t => geomMean p P (star (V t) * R * V t))
      (geomMeanDerivRight p P R ((-X)ᴴ * R + R * -X)) 0 := by
    have h1 := (hasFDerivWithinAt_geomMean_right hP hR hp).restrictScalars ℝ
    have h2 : HasDerivWithinAt (fun t : ℝ => star (V t) * R * V t) ((-X)ᴴ * R + R * -X) univ 0 :=
      hb.hasDerivWithinAt
    have h3 := HasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (0 : ℝ) h1 h2
      (fun t _ => hherm R (V t) hR.isHermitian) (by simp [hV0])
    exact h3.hasDerivAt Filter.univ_mem
  have hexpX : HasDerivAt S X 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  have hstarS : HasDerivAt (fun t => star (S t)) Xᴴ 0 := by
    have hst : ∀ t : ℝ, star (S t) = exp (t • Xᴴ) := by
      intro t
      rw [star_eq_conjTranspose, ← Matrix.exp_conjTranspose, conjTranspose_smul, star_trivial]
    simp_rw [hst]
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ 0
  have hR := (hstarS.mul hψ).mul hexpX
  have hfun : (fun t => geomMean p (star (S t) * P * S t) R) =
      fun t => star (S t) * geomMean p P (star (V t) * R * V t) * S t := funext hid
  rw [hfun] at hL
  have heq := hL.unique hR
  simp only [Pi.mul_apply, hS0, hV0, star_one, Matrix.one_mul, Matrix.mul_one, conjTranspose_neg,
    Matrix.neg_mul, Matrix.mul_neg, ← neg_add, map_neg] at heq
  rw [heq]; abel



open MeanTree in
theorem sum_derivLabel_congr {M : J → Matrix m m ℂ} (hM : ∀ j, (M j).PosDef) (T' : MeanTree J)
    (X : Matrix m m ℂ) :
    ∑ j, T'.derivLabel M j (Xᴴ * M j + M j * X) = Xᴴ * T'.eval M + T'.eval M * X := by
  induction T' with
  | leaf i =>
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [derivLabel, Ne.symm hj]) (by simp)]
    simp [derivLabel]
  | node p l r ihl ihr =>
    simp only [derivLabel, _root_.add_apply, ContinuousLinearMap.comp_apply,
      Finset.sum_add_distrib, ← map_sum, ihl, ihr, eval_node]
    exact geomMeanDeriv_congr (posDef_eval hM l) (posDef_eval hM r) p.2 X

open MeanTree in
theorem sum_derivLabel_commutator {M : J → Matrix m m ℂ} (hM : ∀ j, (M j).PosDef)
    (T' : MeanTree J) {L : Matrix m m ℂ} (hL : L.IsHermitian) :
    ∑ j, T'.derivLabel M j (M j * L - L * M j) = T'.eval M * L - L * T'.eval M := by
  have h := sum_derivLabel_congr hM T' (Complex.I • L)
  have hX : (Complex.I • L)ᴴ = -(Complex.I • L) := by
    rw [conjTranspose_smul, hL.eq, Complex.star_def, Complex.conj_I, neg_smul]
  have e : ∀ Y : Matrix m m ℂ, (Complex.I • L)ᴴ * Y + Y * (Complex.I • L) =
      Complex.I • (Y * L - L * Y) := by
    intro Y; rw [hX, smul_sub, Matrix.neg_mul, Matrix.smul_mul, Matrix.mul_smul]; abel
  simp only [e, map_smul, ← Finset.smul_sum] at h
  exact smul_right_injective _ Complex.I_ne_zero h

open MeanTree in
/-- **The block-rotation identity** (`06-transport.tex`, display `transport:block-rotation`,
lines 680--686): `2 sinh(ad_{log 𝕄}/2) L = ∑_j π_j Φ̂_j(K_j)`, written as
`𝕄^{1/2} L 𝕄^{-1/2} - 𝕄^{-1/2} L 𝕄^{1/2}`. -/
theorem sum_weight_smul_leafMap_rotation {M : J → Matrix m m ℂ} (hM : ∀ j, (M j).PosDef)
    (T' : MeanTree J) (hw : ∀ j, T'.weight j ≠ 0) {L : Matrix m m ℂ} (hL : L.IsHermitian) :
    ∑ j, T'.weight j • T'.leafMap M j (M j ^ (1 / 2 : ℝ) * L * M j ^ (-(1 / 2) : ℝ) -
        M j ^ (-(1 / 2) : ℝ) * L * M j ^ (1 / 2 : ℝ)) =
      T'.eval M ^ (1 / 2 : ℝ) * L * T'.eval M ^ (-(1 / 2) : ℝ) -
        T'.eval M ^ (-(1 / 2) : ℝ) * L * T'.eval M ^ (1 / 2 : ℝ) := by
  set R := T'.eval M
  have hR : R.PosDef := posDef_eval hM T'
  have hterm : ∀ j, T'.weight j • T'.leafMap M j (M j ^ (1 / 2 : ℝ) * L * M j ^ (-(1 / 2) : ℝ) -
      M j ^ (-(1 / 2) : ℝ) * L * M j ^ (1 / 2 : ℝ)) =
      R ^ (-(1 / 2) : ℝ) * T'.derivLabel M j (M j * L - L * M j) * R ^ (-(1 / 2) : ℝ) := by
    intro j
    have hK : M j ^ (1 / 2 : ℝ) * (M j ^ (1 / 2 : ℝ) * L * M j ^ (-(1 / 2) : ℝ) -
        M j ^ (-(1 / 2) : ℝ) * L * M j ^ (1 / 2 : ℝ)) * M j ^ (1 / 2 : ℝ) = M j * L - L * M j := by
      have h1 := (hM j).rpow_half_mul_rpow_half
      have h2 := (hM j).rpow_mul_rpow_neg (1 / 2)
      have h3 := (hM j).rpow_neg_mul_rpow (1 / 2)
      calc _ = (M j ^ (1 / 2 : ℝ) * M j ^ (1 / 2 : ℝ)) * L *
            (M j ^ (-(1 / 2) : ℝ) * M j ^ (1 / 2 : ℝ)) -
          (M j ^ (1 / 2 : ℝ) * M j ^ (-(1 / 2) : ℝ)) * L *
            (M j ^ (1 / 2 : ℝ) * M j ^ (1 / 2 : ℝ)) := by noncomm_ring
        _ = _ := by rw [h1, h2, h3, Matrix.mul_one, Matrix.one_mul]
    simp only [leafMap, normalizedDerivMap, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, sandwichL_apply, smul_smul, mul_inv_cancel₀ (hw j),
      one_smul, hK]
    rfl
  simp only [hterm, ← Finset.sum_mul, ← Finset.mul_sum, sum_derivLabel_commutator hM T' hL]
  have h1 := hR.rpow_half_mul_rpow_half
  have h2 := hR.rpow_mul_rpow_neg (1 / 2)
  have h3 := hR.rpow_neg_mul_rpow (1 / 2)
  calc R ^ (-(1 / 2) : ℝ) * (R * L - L * R) * R ^ (-(1 / 2) : ℝ)
      = R ^ (-(1 / 2) : ℝ) * (R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) * L * R ^ (-(1 / 2) : ℝ) -
        R ^ (-(1 / 2) : ℝ) * L * (R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) * R ^ (-(1 / 2) : ℝ) := by
        rw [h1]; noncomm_ring
    _ = (R ^ (-(1 / 2) : ℝ) * R ^ (1 / 2 : ℝ)) * R ^ (1 / 2 : ℝ) * L * R ^ (-(1 / 2) : ℝ) -
        R ^ (-(1 / 2) : ℝ) * L * R ^ (1 / 2 : ℝ) * (R ^ (1 / 2 : ℝ) * R ^ (-(1 / 2) : ℝ)) := by
        noncomm_ring
    _ = _ := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]

end Rotation

/-! ### Spectral form, Fourier densities and the Schwarz inequality -/

section Fourier

variable {m : Type*} [Fintype m] [DecidableEq m] {R : Matrix m m ℂ}

/-- Conjugation `U X U^*` by the eigenvector unitary of a Hermitian matrix. -/
noncomputable def eigConj (hR : R.IsHermitian) (X : Matrix m m ℂ) : Matrix m m ℂ :=
  (hR.eigenvectorUnitary : Matrix m m ℂ) * X * star (hR.eigenvectorUnitary : Matrix m m ℂ)

theorem star_eigU_mul_eigU (hR : R.IsHermitian) :
    star (hR.eigenvectorUnitary : Matrix m m ℂ) * (hR.eigenvectorUnitary : Matrix m m ℂ) = 1 :=
  Unitary.coe_star_mul_self _

theorem eigU_mul_star_eigU (hR : R.IsHermitian) :
    (hR.eigenvectorUnitary : Matrix m m ℂ) * star (hR.eigenvectorUnitary : Matrix m m ℂ) = 1 :=
  Unitary.coe_mul_star_self _

theorem eigConj_mul_eigConj (hR : R.IsHermitian) (X Y : Matrix m m ℂ) :
    eigConj hR X * eigConj hR Y = eigConj hR (X * Y) := by
  simp only [eigConj]
  calc _ = (hR.eigenvectorUnitary : Matrix m m ℂ) * X *
        (star (hR.eigenvectorUnitary : Matrix m m ℂ) * (hR.eigenvectorUnitary : Matrix m m ℂ)) *
        Y * star (hR.eigenvectorUnitary : Matrix m m ℂ) := by noncomm_ring
    _ = _ := by rw [star_eigU_mul_eigU, Matrix.mul_one, Matrix.mul_assoc _ X Y]

theorem eigConj_unconj (hR : R.IsHermitian) (X : Matrix m m ℂ) :
    eigConj hR (star (hR.eigenvectorUnitary : Matrix m m ℂ) * X *
      (hR.eigenvectorUnitary : Matrix m m ℂ)) = X := by
  simp only [eigConj]
  calc _ = ((hR.eigenvectorUnitary : Matrix m m ℂ) * star (hR.eigenvectorUnitary : Matrix m m ℂ)) *
        X * ((hR.eigenvectorUnitary : Matrix m m ℂ) *
          star (hR.eigenvectorUnitary : Matrix m m ℂ)) := by noncomm_ring
    _ = X := by rw [eigU_mul_star_eigU, Matrix.one_mul, Matrix.mul_one]

theorem conjTranspose_eigConj (hR : R.IsHermitian) (X : Matrix m m ℂ) :
    (eigConj hR X)ᴴ = eigConj hR Xᴴ := by
  simp only [eigConj, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem cfc_eq_eigConj (hR : R.IsHermitian) (f : ℝ → ℝ) :
    cfc f R = eigConj hR (diagonal fun a => (f (hR.eigenvalues a) : ℂ)) := by
  rw [hR.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply]; rfl

theorem rpow_eq_eigConj (hR : R.PosDef) (r : ℝ) :
    R ^ r = eigConj hR.isHermitian
      (diagonal fun a => (Real.exp (r * Real.log (hR.isHermitian.eigenvalues a)) : ℂ)) := by
  rw [CFC.rpow_eq_cfc_real hR.posSemidef.nonneg, cfc_eq_eigConj hR.isHermitian]
  congr 2; funext a
  rw [Real.rpow_def_of_pos (hR.eigenvalues_pos a), mul_comm]

theorem imagPow_eq_eigConj (hR : R.PosDef) (u : ℝ) :
    imagPow R u = eigConj hR.isHermitian
      (diagonal fun a => Complex.exp (-(u : ℂ) * Complex.I *
        (Real.log (hR.isHermitian.eigenvalues a) : ℂ))) := by
  have hU : IsUnit (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    (Unitary.isUnit_coe (U := hR.isHermitian.eigenvectorUnitary))
  have hinv : (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)⁻¹ =
      star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    Matrix.inv_eq_left_inv (star_eigU_mul_eigU hR.isHermitian)
  unfold imagPow hermitianUnitaryPath
  set U := (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)
  have harg : (-u) • (Complex.I • eigConj hR.isHermitian
      (diagonal fun a => ((Real.log (hR.isHermitian.eigenvalues a) : ℝ) : ℂ))) =
      U * diagonal (fun a => -(u : ℂ) * Complex.I *
        (Real.log (hR.isHermitian.eigenvalues a) : ℂ)) * U⁻¹ := by
    rw [hinv, ← Complex.coe_smul, smul_smul, eigConj, ← smul_mul_assoc, ← mul_smul_comm]
    congr 2
    ext i j
    by_cases h : i = j <;> simp [h, diagonal]
  rw [CFC.log, cfc_eq_eigConj hR.isHermitian, harg, Matrix.exp_conj _ _ hU, Matrix.exp_diagonal,
    Pi.exp_def, hinv, eigConj]
  simp only [← Complex.exp_eq_exp_ℂ]
  rfl


/-! ### The Fourier densities `q_±` -/

/-- The exponent `±1/4` of the error vectors `E_±`. -/
noncomputable abbrev signExp (sign : Bool) : ℝ := if sign then 1 / 4 else -(1 / 4)

/-- The Fourier densities `q_+(u) = m_{1/8}(u + i/8)` and `q_-(u) = -m_{1/8}(u - i/8)`
(`06-transport.tex`, display `transport:q-density`). -/
noncomputable def qDensity (sign : Bool) (u : ℝ) : ℂ :=
  if sign then Complex.sinhRatioDensity ((1 / 4 : ℝ) / 2) (u + ((1 / 4 : ℝ) / 2 : ℝ) * Complex.I)
  else -Complex.sinhRatioDensity ((1 / 4 : ℝ) / 2) (u + (-((1 / 4 : ℝ) / 2) : ℝ) * Complex.I)

theorem norm_qDensity_le (sign : Bool) (u : ℝ) :
    ‖qDensity sign u‖ ≤ fourierWeight u / √2 := by
  cases sign
  · have h := Complex.norm_sinhRatioDensity_shift_le u (Or.inr rfl : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1)
    simp only [qDensity, Bool.false_eq_true, ↓reduceIte, norm_neg]
    convert h using 3 <;> push_cast <;> ring
  · have h := Complex.norm_sinhRatioDensity_shift_le u (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1)
    simp only [qDensity, ↓reduceIte]
    convert h using 3 <;> push_cast <;> ring

theorem continuous_qDensity (sign : Bool) : Continuous (qDensity sign) := by
  have hs : (1 / 4 : ℝ) ∈ Set.Ioo 0 (1 / 2) := by norm_num
  have key : ∀ τ : ℝ, |τ| ≤ (1 / 4 : ℝ) / 2 →
      Continuous fun u : ℝ => Complex.sinhRatioDensity ((1 / 4 : ℝ) / 2) (u + τ * Complex.I) := by
    intro τ hσ
    refine continuous_const.div ((Complex.differentiable_densityDenom _).continuous.comp
      (by fun_prop)) fun u => ?_
    exact Complex.densityDenom_half_ne_zero hs (by simpa using hσ)
  cases sign
  · exact (key _ (by rw [abs_neg, abs_of_pos (by norm_num)])).neg
  · exact key _ (by rw [abs_of_pos (by norm_num)])

theorem integrable_fourierWeight : Integrable fourierWeight :=
  Real.integrable_sinhRatioDensity (by norm_num)

theorem integral_fourierWeight : ∫ u, fourierWeight u = 1 / 2 := by
  rw [Real.integral_sinhRatioDensity (by norm_num)]; norm_num

theorem integrable_qDensity (sign : Bool) : Integrable (qDensity sign) :=
  (integrable_fourierWeight.div_const √2).mono' (continuous_qDensity sign).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_qDensity_le sign))

theorem integral_norm_qDensity_le (sign : Bool) :
    ∫ u, ‖qDensity sign u‖ ≤ 1 / 2 / √2 := by
  calc ∫ u, ‖qDensity sign u‖ ≤ ∫ u, fourierWeight u / √2 :=
        integral_mono (integrable_qDensity sign).norm (integrable_fourierWeight.div_const _)
          (norm_qDensity_le sign)
    _ = 1 / 2 / √2 := by rw [integral_div, integral_fourierWeight]

/-- The Fourier multiplier of `q_±` against the hyperbolic factor:
`(∫ q_±(u) e^{iuz} du) (e^{z/2} - e^{-z/2}) = e^{±z/4} - 1` (`06-transport.tex`,
displays `transport:h-def` and `transport:q-density`). -/
theorem integral_qDensity_mul_cexp_mul (sign : Bool) (z : ℝ) :
    (∫ u, qDensity sign u * Complex.exp (Complex.I * u * z)) *
        ((Real.exp (z / 2) : ℂ) - (Real.exp (-(z / 2)) : ℂ)) =
      (Real.exp (signExp sign * z) : ℂ) - 1 := by
  have hs : (1 / 4 : ℝ) ∈ Set.Ioo 0 (1 / 2) := by norm_num
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hsinh : (Real.exp (z / 2) : ℂ) - (Real.exp (-(z / 2)) : ℂ) =
      ((2 * Real.sinh (z / 2) : ℝ) : ℂ) := by
    rw [Real.sinh_eq]; push_cast; ring
  have hsh : Real.sinh (z / 2) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; intro h; exact hz (by linarith)
  simp_rw [mul_comm (qDensity sign _)]
  cases sign
  · have h := Complex.integral_exp_mul_qMinus_of_ne_zero hs hz
    simp only [qDensity, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [h, hsinh, ← Complex.ofReal_mul, div_mul_cancel₀ _ (by positivity)]
    push_cast; simp only [signExp]; push_cast; ring_nf
  · have h := Complex.integral_exp_mul_qPlus_of_ne_zero hs hz
    simp only [qDensity, ↓reduceIte] at h ⊢
    rw [h, hsinh, ← Complex.ofReal_mul, div_mul_cancel₀ _ (by positivity)]
    push_cast; simp only [signExp]; push_cast; ring_nf


theorem eigConj_sub (hR : R.IsHermitian) (X Y : Matrix m m ℂ) :
    eigConj hR (X - Y) = eigConj hR X - eigConj hR Y := by
  simp only [eigConj, Matrix.mul_sub, Matrix.sub_mul]

theorem star_dotProduct_eigConj_mulVec (hR : R.IsHermitian) (Z : Matrix m m ℂ) (x y : m → ℂ) :
    star y ⬝ᵥ (eigConj hR Z *ᵥ x) =
      ∑ a, ∑ b, star ((star (hR.eigenvectorUnitary : Matrix m m ℂ) *ᵥ y) a) * Z a b *
        (star (hR.eigenvectorUnitary : Matrix m m ℂ) *ᵥ x) b := by
  set U := (hR.eigenvectorUnitary : Matrix m m ℂ)
  have h := star_mulVec_dotProduct_mulVec (star U) Z y (star U *ᵥ x)
  rw [star_eq_conjTranspose U, conjTranspose_conjTranspose, ← star_eq_conjTranspose U] at h
  rw [eigConj, ← mulVec_mulVec, ← h]
  generalize star U *ᵥ x = x'
  generalize star U *ᵥ y = y'
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `q_±` times a bounded continuous function is integrable. -/
theorem integrable_qDensity_mul {f : ℝ → ℂ} (sign : Bool) (hf : Continuous f) {C : ℝ}
    (hC : ∀ u, ‖f u‖ ≤ C) : Integrable fun u => qDensity sign u * f u :=
  (integrable_qDensity sign).mul_bdd hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem integrable_qDensity_mul_cexp (sign : Bool) (z : ℝ) (k : ℂ) :
    Integrable fun u : ℝ => qDensity sign u * (Complex.exp (Complex.I * u * z) * k) :=
  integrable_qDensity_mul sign (by fun_prop) (C := ‖k‖) fun u => by
    rw [norm_mul, show Complex.I * u * z = ((u * z : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **Fourier form of the error operators** (`06-transport.tex`, displays `transport:E-def`
and the Fourier formula following it, lines 688--700): for positive definite `R`,
`⟨y, (R^{±s} L R^{∓s} - L) x⟩ = ∫ q_±(u) ⟨R^{-iu} y, (R^{1/2} L R^{-1/2} - R^{-1/2} L R^{1/2})
R^{-iu} x⟩ du` with `s = 1/4`. -/
theorem integral_qDensity_mul_inner (hR : R.PosDef) (L : Matrix m m ℂ) (sign : Bool)
    (x y : m → ℂ) :
    ∫ u, qDensity sign u * (star (imagPow R u *ᵥ y) ⬝ᵥ
      ((R ^ (1 / 2 : ℝ) * L * R ^ (-(1 / 2) : ℝ) - R ^ (-(1 / 2) : ℝ) * L * R ^ (1 / 2 : ℝ)) *ᵥ
        (imagPow R u *ᵥ x))) =
      star y ⬝ᵥ ((R ^ signExp sign * L * R ^ (-signExp sign) - L) *ᵥ x) := by
  set hH := hR.isHermitian
  set U := (hH.eigenvectorUnitary : Matrix m m ℂ)
  set ℓ : m → ℝ := fun a => Real.log (hH.eigenvalues a)
  set ex : ℝ → m → ℂ := fun r a => (Real.exp (r * ℓ a) : ℂ)
  set L' := star U * L * U
  have hL : L = eigConj hH L' := (eigConj_unconj hH L).symm
  have hpow : ∀ r : ℝ, R ^ r = eigConj hH (diagonal (ex r)) := rpow_eq_eigConj hR
  set ph : ℝ → m → ℂ := fun u a => Complex.exp (-(u : ℂ) * Complex.I * (ℓ a : ℂ))
  have hW : ∀ u, imagPow R u = eigConj hH (diagonal (ph u)) := imagPow_eq_eigConj hR
  set c : m → m → ℂ := fun a b => star ((star U *ᵥ y) a) * L' a b * (star U *ᵥ x) b
  -- the integrand in the eigenbasis
  have hint : ∀ u, star (imagPow R u *ᵥ y) ⬝ᵥ
      ((R ^ (1 / 2 : ℝ) * L * R ^ (-(1 / 2) : ℝ) - R ^ (-(1 / 2) : ℝ) * L * R ^ (1 / 2 : ℝ)) *ᵥ
        (imagPow R u *ᵥ x)) = ∑ a, ∑ b, Complex.exp (Complex.I * u * ((ℓ a - ℓ b : ℝ) : ℂ)) *
          ((ex (1 / 2) a * ex (-(1 / 2)) b - ex (-(1 / 2)) a * ex (1 / 2) b) * c a b) := by
    intro u
    rw [star_mulVec_dotProduct_mulVec, mulVec_mulVec, hW, hpow, hpow, hL, conjTranspose_eigConj,
      eigConj_mul_eigConj, eigConj_mul_eigConj, eigConj_mul_eigConj, eigConj_mul_eigConj,
      ← eigConj_sub, eigConj_mul_eigConj, eigConj_mul_eigConj, star_dotProduct_eigConj_mulVec]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hph : star (ph u a) * ph u b = Complex.exp (Complex.I * u * ((ℓ a - ℓ b : ℝ) : ℂ)) := by
      simp only [ph, ← Complex.exp_conj, Complex.star_def, map_mul, map_neg, Complex.conj_ofReal,
        Complex.conj_I, ← Complex.exp_add]
      congr 1; push_cast; ring
    simp only [diagonal_conjTranspose, sub_apply, diagonal_mul, mul_diagonal, Pi.star_apply, c]
    calc _ = (star (ph u a) * ph u b) * ((ex (1 / 2) a * ex (-(1 / 2)) b -
          ex (-(1 / 2)) a * ex (1 / 2) b) * (star ((star U *ᵥ y) a) * L' a b *
            (star U *ᵥ x) b)) := by ring
      _ = _ := by rw [hph]
  simp_rw [hint]
  rw [hpow, hpow, hL, eigConj_mul_eigConj, eigConj_mul_eigConj, ← eigConj_sub,
    star_dotProduct_eigConj_mulVec]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun a _ => ?_]
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => integrable_qDensity_mul_cexp sign _ _]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h := integral_qDensity_mul_cexp_mul sign (ℓ a - ℓ b)
    simp_rw [← mul_assoc]
    rw [integral_mul_const, integral_mul_const]
    simp only [sub_apply, diagonal_mul, mul_diagonal, c, ex]
    have e1 : ((Real.exp (1 / 2 * ℓ a) : ℂ) * (Real.exp (-(1 / 2) * ℓ b) : ℂ) -
        (Real.exp (-(1 / 2) * ℓ a) : ℂ) * (Real.exp (1 / 2 * ℓ b) : ℂ)) =
        (Real.exp ((ℓ a - ℓ b) / 2) : ℂ) - (Real.exp (-((ℓ a - ℓ b) / 2)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      congr 3 <;> ring
    have e2 : (Real.exp (signExp sign * ℓ a) : ℂ) * (Real.exp (-signExp sign * ℓ b) : ℂ) =
        (Real.exp (signExp sign * (ℓ a - ℓ b)) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    rw [e1, h]
    calc _ = star ((star U *ᵥ y) a) * ((Real.exp (signExp sign * (ℓ a - ℓ b)) : ℂ) * L' a b -
          L' a b) * (star U *ᵥ x) b := by ring
      _ = _ := by rw [← e2]; ring
  · exact integrable_finsetSum _ fun b _ => integrable_qDensity_mul_cexp sign _ _

/-- **Schwarz inequality for a unital 2-positive map** (`06-transport.tex`, display
`transport:cp-schwarz`, lines 712--722): `‖Ψ(K) y‖² ≤ ⟨y, Ψ(K^*K) y⟩`. -/
theorem re_star_mulVec_dotProduct_le_of_twoPositive {Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h2 : IsNPositiveMap 2 Φ) (h1 : Φ 1 = 1) (K : Matrix m m ℂ) (y : m → ℂ) :
    (star (Φ K *ᵥ y) ⬝ᵥ (Φ K *ᵥ y)).re ≤ (star y ⬝ᵥ (Φ (Kᴴ * K) *ᵥ y)).re := by
  have hpos : IsPositiveMap Φ := Is2PositiveMap.isPositiveMap h2
  have h := SchwarzTwoVariable.schwarz_two_variable Φ h2 K 1 y (Φ K *ᵥ y)
    (by simp [h1])
  rw [Matrix.mul_one, hpos.map_conjTranspose] at h
  rw [star_mulVec, ← dotProduct_mulVec]
  exact (Complex.le_def.mp h).1

end Fourier

/-! ### The transported square -/

section TransportedSquare

variable {m : Type*} [Fintype m] [DecidableEq m] {R : Matrix m m ℂ}

/-- The pairing `⟨R^{-iu} y, Z R^{-iu} x⟩` in the eigenbasis of `R`: a finite sum of
characters `e^{iu(ℓ_a - ℓ_b)}`. -/
theorem inner_imagPow_eq_sum (hR : R.PosDef) (Z : Matrix m m ℂ) (x y : m → ℂ) (u : ℝ) :
    star (imagPow R u *ᵥ y) ⬝ᵥ (Z *ᵥ (imagPow R u *ᵥ x)) =
      ∑ a, ∑ b, Complex.exp (Complex.I * u *
        ((Real.log (hR.isHermitian.eigenvalues a) - Real.log (hR.isHermitian.eigenvalues b) : ℝ) :
          ℂ)) *
        (star ((star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *ᵥ y) a) *
          (star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) * Z *
            (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)) a b *
          (star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *ᵥ x) b) := by
  set hH := hR.isHermitian
  set U := (hH.eigenvectorUnitary : Matrix m m ℂ)
  set ℓ : m → ℝ := fun a => Real.log (hH.eigenvalues a)
  set ph : ℝ → m → ℂ := fun u a => Complex.exp (-(u : ℂ) * Complex.I * (ℓ a : ℂ))
  have hZ : Z = eigConj hH (star U * Z * U) := (eigConj_unconj hH Z).symm
  rw [star_mulVec_dotProduct_mulVec, mulVec_mulVec, imagPow_eq_eigConj hR, hZ,
    conjTranspose_eigConj, eigConj_mul_eigConj, eigConj_mul_eigConj,
    star_dotProduct_eigConj_mulVec, ← hZ]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hph : star (ph u a) * ph u b = Complex.exp (Complex.I * u * ((ℓ a - ℓ b : ℝ) : ℂ)) := by
    simp only [ph, ← Complex.exp_conj, Complex.star_def, map_mul, map_neg, Complex.conj_ofReal,
      Complex.conj_I, ← Complex.exp_add]
    congr 1; push_cast; ring
  simp only [diagonal_conjTranspose, diagonal_mul, mul_diagonal, Pi.star_apply]
  calc _ = (star (ph u a) * ph u b) * (star ((star U *ᵥ y) a) * (star U * Z * U) a b *
        (star U *ᵥ x) b) := by ring
    _ = _ := by rw [hph]

theorem continuous_inner_imagPow (hR : R.PosDef) (Z : Matrix m m ℂ) (x y : m → ℂ) :
    Continuous fun u : ℝ => star (imagPow R u *ᵥ y) ⬝ᵥ (Z *ᵥ (imagPow R u *ᵥ x)) := by
  simp_rw [inner_imagPow_eq_sum hR]
  fun_prop

theorem norm_inner_imagPow_le (hR : R.PosDef) (Z : Matrix m m ℂ) (x y : m → ℂ) :
    ∃ C, ∀ u : ℝ, ‖star (imagPow R u *ᵥ y) ⬝ᵥ (Z *ᵥ (imagPow R u *ᵥ x))‖ ≤ C := by
  refine ⟨∑ a, ∑ b, ‖star ((star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *ᵥ y) a) *
          (star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) * Z *
            (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ)) a b *
          (star (hR.isHermitian.eigenvectorUnitary : Matrix m m ℂ) *ᵥ x) b‖, fun u => ?_⟩
  rw [inner_imagPow_eq_sum hR]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun b _ => ?_))
  rw [norm_mul, show Complex.I * (u : ℂ) * _ = ((u * (Real.log (hR.isHermitian.eigenvalues a) -
    Real.log (hR.isHermitian.eigenvalues b)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

theorem conjTranspose_imagPow_mul_self (hR : R.PosDef) (u : ℝ) :
    (imagPow R u)ᴴ * imagPow R u = 1 := by
  rw [imagPow_eq_eigConj hR, conjTranspose_eigConj, eigConj_mul_eigConj, diagonal_conjTranspose,
    diagonal_mul_diagonal]
  have : (fun a => star (Complex.exp (-(u : ℂ) * Complex.I *
      (Real.log (hR.isHermitian.eigenvalues a) : ℂ))) * Complex.exp (-(u : ℂ) * Complex.I *
      (Real.log (hR.isHermitian.eigenvalues a) : ℂ))) = fun _ => 1 := by
    funext a
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    rw [← Complex.exp_zero]; congr 1; ring
  simp only [Pi.star_apply] at this ⊢
  rw [this, diagonal_one, eigConj, Matrix.mul_one, eigU_mul_star_eigU]

theorem nsq_imagPow_mulVec (hR : R.PosDef) (u : ℝ) (y : m → ℂ) :
    star (imagPow R u *ᵥ y) ⬝ᵥ (imagPow R u *ᵥ y) = star y ⬝ᵥ y := by
  rw [star_mulVec_dotProduct_mulVec, conjTranspose_imagPow_mul_self hR, one_mulVec]


omit [Fintype m] [DecidableEq m] in
theorem nsq_nonneg' [Fintype m] (y : m → ℂ) : 0 ≤ (star y ⬝ᵥ y).re := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (y i).re, sq_nonneg (y i).im]

omit [DecidableEq m] in
/-- `Re(q ⟨p, g⟩) ≤ |q| (c/2 ‖p‖² + ‖g‖²/(2c))` for `c > 0`. -/
theorem re_mul_dotProduct_le (q : ℂ) (p g : m → ℂ) {c : ℝ} (hc : 0 < c) :
    (q * (star p ⬝ᵥ g)).re ≤
      ‖q‖ * (c / 2 * (star p ⬝ᵥ p).re + 1 / (2 * c) * (star g ⬝ᵥ g).re) := by
  simp only [dotProduct, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hpp : (star (p i) * p i).re = ‖p i‖ ^ 2 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]; rfl
  have hgg : (star (g i) * g i).re = ‖g i‖ ^ 2 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]; rfl
  rw [hpp, hgg]
  calc (q * (star (p i) * g i)).re ≤ ‖q * (star (p i) * g i)‖ := Complex.re_le_norm _
    _ = ‖q‖ * (‖p i‖ * ‖g i‖) := by rw [norm_mul, norm_mul, norm_star]
    _ ≤ _ := by
      gcongr
      have key : c / 2 * ‖p i‖ ^ 2 + 1 / (2 * c) * ‖g i‖ ^ 2 - ‖p i‖ * ‖g i‖ =
          (c * ‖p i‖ - ‖g i‖) ^ 2 / (2 * c) := by field_simp; ring
      nlinarith [key, div_nonneg (sq_nonneg (c * ‖p i‖ - ‖g i‖)) (by positivity : (0 : ℝ) ≤ 2 * c)]

/-- The closing scalar step of the transported-square estimate. -/
theorem le_of_forall_pos_le_aux {N A W S' : ℝ} (hN : 0 ≤ N) (hA0 : 0 ≤ A)
    (hA : A ≤ 1 / 2 / √2) (hW : 0 ≤ W) (hS0 : 0 ≤ S')
    (h : ∀ c : ℝ, 0 < c → N ≤ c / 2 * N * (A * W) + 1 / (2 * c) * (S' / √2)) :
    N ≤ 1 / 4 * W * S' := by
  have hs2 : (0 : ℝ) < √2 := by positivity
  have ha : 0 ≤ S' / √2 := by positivity
  set P := A * W with hPdef
  rcases eq_or_lt_of_le (mul_nonneg hA0 hW : 0 ≤ P) with hAW | hAW
  · have hN0 : N ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have := h ((S' / √2 + 1) / N) (by positivity)
      rw [hPdef, ← hAW, mul_zero, zero_add] at this
      have e : 1 / (2 * ((S' / √2 + 1) / N)) * (S' / √2) =
          N * (S' / √2) / (2 * (S' / √2 + 1)) := by field_simp
      rw [e, le_div_iff₀ (by positivity)] at this
      nlinarith
    nlinarith
  · have hP0 : P ≠ 0 := hAW.ne'
    have := h (1 / P) (by positivity)
    have e1 : 1 / P / 2 * N * P = N / 2 := by field_simp
    have e2 : 1 / (2 * (1 / P)) * (S' / √2) = P * S' / (2 * √2) := by field_simp
    rw [e1, e2] at this
    have hNle : N ≤ P * S' / √2 := by
      have h2 : P * S' / (2 * √2) * 2 = P * S' / √2 := by field_simp
      linarith
    calc N ≤ P * S' / √2 := hNle
      _ ≤ 1 / 2 / √2 * W * S' / √2 := by
        gcongr
        calc P = A * W := rfl
          _ ≤ 1 / 2 / √2 * W := by gcongr
      _ = 1 / 4 * W * S' := by
        field_simp; rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring


/-- **The transported square, generic form** (`06-transport.tex` lines 688--729): if
`R^{1/2} L R^{-1/2} - R^{-1/2} L R^{1/2} = ∑_{j∈S} w_j G_j` with `w_j ≥ 0` and
`‖G_j R^{-iu} x‖² ≤ t_j(u)`, then
`‖(R^{±s} L R^{∓s} - L) x‖² ≤ (1/4) W ∑_{j∈S} w_j ∫ m_s(u) t_j(u) du`, `W = ∑_{j∈S} w_j`.
The factor `W` comes from Cauchy--Schwarz over the positive measure `w_j |q_±(u)| du`. -/
theorem nsq_conj_sub_le {J : Type*} (hR : R.PosDef) (L : Matrix m m ℂ) (sign : Bool)
    (S : Finset J) {w : J → ℝ} (hw : ∀ j, 0 ≤ w j) (G : J → Matrix m m ℂ)
    (hG : R ^ (1 / 2 : ℝ) * L * R ^ (-(1 / 2) : ℝ) - R ^ (-(1 / 2) : ℝ) * L * R ^ (1 / 2 : ℝ) =
      ∑ j ∈ S, w j • G j)
    (x : m → ℂ) (t : J → ℝ → ℝ)
    (ht : ∀ j u, (star (G j *ᵥ (imagPow R u *ᵥ x)) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x))).re ≤ t j u)
    (htc : ∀ j, Continuous (t j)) (htb : ∀ j, ∃ C, ∀ u, ‖t j u‖ ≤ C) :
    (star ((R ^ signExp sign * L * R ^ (-signExp sign) - L) *ᵥ x) ⬝ᵥ
        ((R ^ signExp sign * L * R ^ (-signExp sign) - L) *ᵥ x)).re ≤
      1 / 4 * (∑ j ∈ S, w j) * ∑ j ∈ S, w j * ∫ u, fourierWeight u * t j u := by
  set F := R ^ signExp sign * L * R ^ (-signExp sign) - L
  set y := F *ᵥ x
  set N := (star y ⬝ᵥ y).re
  set A := ∫ u, ‖qDensity sign u‖
  have ht0 : ∀ j u, 0 ≤ t j u := fun j u => (nsq_nonneg' _).trans (ht j u)
  have hint_t : ∀ j, Integrable fun u => fourierWeight u * t j u := fun j =>
    integrable_fourierWeight.mul_bdd (htc j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => (htb j).choose_spec u)
  have hint_qt : ∀ j, Integrable fun u => ‖qDensity sign u‖ * t j u := fun j =>
    (integrable_qDensity sign).norm.mul_bdd (htc j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => (htb j).choose_spec u)
  have hf : ∀ j, Integrable fun u => qDensity sign u *
      (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x))) := fun j =>
    integrable_qDensity_mul sign (continuous_inner_imagPow hR _ _ _)
      (norm_inner_imagPow_le hR (G j) x y).choose_spec
  -- Fourier form and the block decomposition
  have hfour := integral_qDensity_mul_inner hR L sign x y
  rw [hG] at hfour
  simp_rw [sum_mulVec, smul_mulVec, dotProduct_sum, dotProduct_smul, Finset.mul_sum,
    mul_smul_comm] at hfour
  have hfs : ∀ j ∈ S, Integrable fun u => w j • (qDensity sign u *
      (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))) := fun j _ => (hf j).smul (w j)
  rw [integral_finsetSum _ hfs] at hfour
  simp_rw [integral_smul] at hfour
  -- the bound for each `c > 0`
  have hmain : ∀ c : ℝ, 0 < c → N ≤ c / 2 * N * (A * ∑ j ∈ S, w j) +
      1 / (2 * c) * ((∑ j ∈ S, w j * ∫ u, fourierWeight u * t j u) / √2) := by
    intro c hc
    have hN : N = ∑ j ∈ S, w j * (∫ u, qDensity sign u *
        (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))).re := by
      have := congrArg Complex.re hfour
      simp only [Complex.re_sum, Complex.real_smul, Complex.re_ofReal_mul] at this
      exact this.symm
    have hj : ∀ j, (∫ u, qDensity sign u *
        (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))).re ≤
        c / 2 * N * A + 1 / (2 * c) * ((∫ u, fourierWeight u * t j u) / √2) := by
      intro j
      have hre := integral_re (hf j)
      simp only [RCLike.re_to_complex] at hre
      rw [← hre]
      calc ∫ u, (qDensity sign u *
            (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))).re
          ≤ ∫ u, (c / 2 * N * ‖qDensity sign u‖ + 1 / (2 * c) * (‖qDensity sign u‖ * t j u)) := by
            refine integral_mono (by simpa using (hf j).re) (((integrable_qDensity sign).norm.const_mul _).add
              ((hint_qt j).const_mul _)) fun u => ?_
            have h1 := re_mul_dotProduct_le (qDensity sign u) (imagPow R u *ᵥ y)
              (G j *ᵥ (imagPow R u *ᵥ x)) hc
            rw [nsq_imagPow_mulVec hR] at h1
            have h2 := mul_le_mul_of_nonneg_left (ht j u) (norm_nonneg (qDensity sign u))
            have hNy : (star y ⬝ᵥ y).re = N := rfl
            rw [hNy] at h1
            have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (2 * c))
            nlinarith [h1, h3]
        _ = c / 2 * N * A + 1 / (2 * c) * ∫ u, ‖qDensity sign u‖ * t j u := by
            rw [integral_add ((integrable_qDensity sign).norm.const_mul _)
              ((hint_qt j).const_mul _), integral_const_mul, integral_const_mul]
        _ ≤ _ := by
            gcongr
            calc ∫ u, ‖qDensity sign u‖ * t j u ≤ ∫ u, fourierWeight u / √2 * t j u :=
                  integral_mono (hint_qt j) ((hint_t j).div_const √2 |>.congr
                    (Filter.Eventually.of_forall fun u => by ring)) fun u =>
                    mul_le_mul_of_nonneg_right (norm_qDensity_le sign u) (ht0 j u)
              _ = (∫ u, fourierWeight u * t j u) / √2 := by
                  rw [← integral_div]; congr 1; funext u; ring
    have hsum : ∑ j ∈ S, w j * (∫ u, qDensity sign u *
          (star (imagPow R u *ᵥ y) ⬝ᵥ (G j *ᵥ (imagPow R u *ᵥ x)))).re ≤
        ∑ j ∈ S, w j * (c / 2 * N * A + 1 / (2 * c) * ((∫ u, fourierWeight u * t j u) / √2)) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hj j) (hw j)
    have heq : ∑ j ∈ S, w j * (c / 2 * N * A + 1 / (2 * c) *
          ((∫ u, fourierWeight u * t j u) / √2)) = c / 2 * N * (A * ∑ j ∈ S, w j) +
        1 / (2 * c) * ((∑ j ∈ S, w j * ∫ u, fourierWeight u * t j u) / √2) := by
      conv_rhs => simp only [Finset.mul_sum, Finset.sum_div]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith
  exact le_of_forall_pos_le_aux (nsq_nonneg' y) (integral_nonneg fun u => norm_nonneg _)
    (integral_norm_qDensity_le sign) (Finset.sum_nonneg fun j _ => hw j)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hw j)
      (integral_nonneg fun u => mul_nonneg (Real.sinhRatioDensity_pos (by norm_num) u).le
        (ht0 j u))) hmain

end TransportedSquare

/-- The error vectors `E_± = 𝓑^{±s} T M^{∓s} - T` of the block root
(`06-transport.tex`, display `transport:E-def`), with `s = 1/4` and `T = h^{1/2}`. -/
noncomputable def errorOp (M Broot h : Matrix n n ℂ) (sign : Bool) : Matrix n n ℂ :=
  let s : ℝ := if sign then 1 / 4 else -(1 / 4)
  Broot ^ s * CFC.sqrt h * M ^ (-s) - CFC.sqrt h

/-- **The transported square** (`06-transport.tex`, displays `transport:block-rotation`,
`transport:cp-schwarz` and `transport:block-bound`, lines 658--729): with the auxiliary
blocks of `exists_auxBlock` attached to every leaf, both error vectors satisfy
`‖E_± v‖² ≤ (1/4) W ∑_{j∈S} π_j ∫ m_s(u) Tr(σ_{j,u} 𝖣_j) du`, where the transport states
`σ_{j,u}` are those of the original tree (first diagonal block, Lemma 7.2). -/
theorem norm_sq_errorVec_le (T' : MeanTree J) {A B : J → Matrix n n ℂ}
    (hA : ∀ j, (A j).PosDef) (hB : ∀ j, (B j).PosDef) (hw : ∀ j, 0 < T'.weight j)
    {h : Matrix n n ℂ} (hh : h.PosSemidef) (S : Finset J)
    (hYZ : ∀ j, (auxY (A j) (B j) h)ᴴ * auxZ (A j) (B j) h =
      A j ^ (-(1 / 2) : ℝ) * h * A j ^ (1 / 2 : ℝ))
    (hD : ∀ j, (auxY (A j) (B j) h - auxZ (A j) (B j) h)ᴴ *
      (auxY (A j) (B j) h - auxZ (A j) (B j) h) = skewSquare (A j) h)
    (hS : ∀ j ∉ S, auxY (A j) (B j) h = auxZ (A j) (B j) h) (v : n → ℂ) (sign : Bool) :
    let E := errorOp (T'.eval A) (T'.eval B) h sign *ᵥ v
    (star E ⬝ᵥ E).re ≤ 1 / 4 * (∑ j ∈ S, T'.weight j) *
      ∑ j ∈ S, T'.weight j * ∫ u, fourierWeight u *
        (transportState T' A v j u * skewSquare (A j) h).trace.re := by
  sorry

/-- The opposite powers of the block root cancel in the pairing
(`06-transport.tex`, display `transport:energy-similarity`, first line). -/
theorem re_inner_errorVec_eq {M Broot h : Matrix n n ℂ} (hM : M.PosDef) (hB : Broot.PosDef)
    (hh : h.PosSemidef) (v : n → ℂ) :
    (star ((CFC.sqrt h + errorOp M Broot h true) *ᵥ v) ⬝ᵥ
        ((CFC.sqrt h + errorOp M Broot h false) *ᵥ v)).re =
      (star (M ^ (-(1 / 4) : ℝ) *ᵥ v) ⬝ᵥ (h *ᵥ (M ^ (1 / 4 : ℝ) *ᵥ v))).re := by
  have hT : (CFC.sqrt h)ᴴ = CFC.sqrt h := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
  have hTT : CFC.sqrt h * CFC.sqrt h = h :=
    CFC.sqrt_mul_sqrt_self h (Matrix.nonneg_iff_posSemidef.mpr hh)
  have h1 : CFC.sqrt h + errorOp M Broot h true =
      Broot ^ (1 / 4 : ℝ) * CFC.sqrt h * M ^ (-(1 / 4) : ℝ) := by
    simp [errorOp]
  have h2 : CFC.sqrt h + errorOp M Broot h false =
      Broot ^ (-(1 / 4) : ℝ) * CFC.sqrt h * M ^ (1 / 4 : ℝ) := by
    simp [errorOp]
  rw [h1, h2, star_mulVec_dotProduct_mulVec, star_mulVec_dotProduct_mulVec, mulVec_mulVec]
  congr 3
  rw [conjTranspose_mul, conjTranspose_mul, hT, (hB.rpow_isHermitian _).eq,
    (hM.rpow_isHermitian _).eq]
  calc _ = M ^ (-(1 / 4) : ℝ) * CFC.sqrt h * (Broot ^ (1 / 4 : ℝ) * Broot ^ (-(1 / 4) : ℝ)) *
          CFC.sqrt h * M ^ (1 / 4 : ℝ) := by noncomm_ring
    _ = M ^ (-(1 / 4) : ℝ) * h * M ^ (1 / 4 : ℝ) := by
      rw [hB.rpow_mul_rpow_neg, Matrix.mul_one]; conv_rhs => rw [← hTT]
      noncomm_ring

omit [DecidableEq n] in
/-- `Re⟨(x + e₊), (x + e₋)⟩ ≥ ½‖x‖² - (3/2)(‖e₊‖² + ‖e₋‖²)`
(`06-transport.tex`, display `transport:energy-similarity`, second line, lines 754--757). -/
theorem re_inner_add_add_ge (x e₁ e₂ : n → ℂ) :
    1 / 2 * (star x ⬝ᵥ x).re - 3 / 2 * ((star e₁ ⬝ᵥ e₁).re + (star e₂ ⬝ᵥ e₂).re) ≤
      (star (x + e₁) ⬝ᵥ (x + e₂)).re := by
  simp only [dotProduct, Pi.star_apply, Pi.add_apply, Complex.re_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im]
  nlinarith [sq_nonneg ((x i).re + (e₁ i).re + (e₂ i).re),
    sq_nonneg ((x i).im + (e₁ i).im + (e₂ i).im), sq_nonneg (e₁ i).re, sq_nonneg (e₁ i).im,
    sq_nonneg (e₂ i).re, sq_nonneg (e₂ i).im]

/-- **Energy of the filtered vector, one term** (`06-transport.tex` lines 588--766):
`⟨v, h v⟩ ≤ 2 Re⟨M^{-s} v, h M^s v⟩ + (3/2) W ∑_{j∈S} π_j ∫ m_s Tr(σ_{j,u} 𝖣_j) du`. -/
theorem re_star_dotProduct_mulVec_le_energy (T' : MeanTree J) {A : J → Matrix n n ℂ}
    (hA : ∀ j, (A j).PosDef) (hw : ∀ j, 0 < T'.weight j) {h : Matrix n n ℂ}
    (hh : h.PosSemidef) (S : Finset J) (hS : ∀ j ∉ S, Commute (A j) h) (v : n → ℂ) :
    (star v ⬝ᵥ (h *ᵥ v)).re ≤
      2 * (star (T'.eval A ^ (-(1 / 4) : ℝ) *ᵥ v) ⬝ᵥ
          (h *ᵥ (T'.eval A ^ (1 / 4 : ℝ) *ᵥ v))).re +
        3 / 2 * (∑ j ∈ S, T'.weight j) *
          ∑ j ∈ S, T'.weight j * ∫ u, fourierWeight u *
            (transportState T' A v j u * skewSquare (A j) h).trace.re := by
  choose B hB hYZ hD hC using fun j => exists_auxBlock (hA j) hh
  have hp := norm_sq_errorVec_le T' hA hB hw hh S hYZ hD (fun j hj => hC j (hS j hj)) v true
  have hm := norm_sq_errorVec_le T' hA hB hw hh S hYZ hD (fun j hj => hC j (hS j hj)) v false
  have heq := re_inner_errorVec_eq (posDef_eval hA T') (posDef_eval hB T') hh v
  have hge := re_inner_add_add_ge (CFC.sqrt h *ᵥ v) (errorOp (T'.eval A) (T'.eval B) h true *ᵥ v)
    (errorOp (T'.eval A) (T'.eval B) h false *ᵥ v)
  rw [← add_mulVec, ← add_mulVec, heq] at hge
  have hT : (CFC.sqrt h)ᴴ = CFC.sqrt h := (CFC.sqrt_nonneg h).isSelfAdjoint.star_eq
  have hTT : CFC.sqrt h * CFC.sqrt h = h :=
    CFC.sqrt_mul_sqrt_self h (Matrix.nonneg_iff_posSemidef.mpr hh)
  rw [star_mulVec_dotProduct_mulVec, hT, hTT] at hge
  simp only at hp hm
  linarith

end Matrix.Transport
