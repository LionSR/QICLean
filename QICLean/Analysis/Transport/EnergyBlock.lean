/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Defs

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
