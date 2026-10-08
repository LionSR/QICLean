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
  sorry

omit [DecidableEq n] in
/-- Moving matrices across the Euclidean pairing:
`⟨X v, Y w⟩ = ⟨v, X^* Y w⟩`. -/
theorem star_mulVec_dotProduct_mulVec (X Y : Matrix n n ℂ) (v w : n → ℂ) :
    star (X *ᵥ v) ⬝ᵥ (Y *ᵥ w) = star v ⬝ᵥ ((Xᴴ * Y) *ᵥ w) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

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
