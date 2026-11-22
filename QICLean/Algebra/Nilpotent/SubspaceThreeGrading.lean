/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Nilpotent.SubspaceThree
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.NoncommRing

/-!
# Nilpotent subspaces of `M₃(ℂ)` without a common kernel

A linear space of nilpotent `3 × 3` complex matrices without a common kernel vector is, up to
similarity, contained in the exceptional two-dimensional space spanned by
`J = E₁₂ + E₂₃` and `B₀ = E₃₂ - E₂₁`. Every member of that space maps `span{e₂}` into
`span{e₁, e₃}` and back, so the whole space is graded: there are matrices `P₀, P₁` with
`P₀ + P₁ = 1`, `P₀ - P₁ ≠ 0`, and `M P₀ = P₁ M` for every member `M`.

This is the exceptional similarity type in the classification of nilpotent matrix spaces invoked
in Wolf's low-dimensional quantum Wielandt corollary; see
`docs/paper-gaps/wolf_ch6_lowdim_wielandt_classification.tex`.

## Main results

* `QICLean.trace_mul_eq_zero_of_isNilpotent`: the trace identities `tr(XC) = 0` and
  `tr(X²C) = 0` on a nilpotent space.
* `QICLean.exists_grading_of_isNilpotent_submodule_fin_three`: the grading of a nilpotent space
  in `M₃(ℂ)` without a common kernel.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 6, corollary after the quantum
  Wielandt inequality; local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
  lines 1110--1126.
-/

open Matrix
open scoped Matrix

namespace QICLean

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℂ

private theorem trace_eq_zero_of_isNilpotent {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : IsNilpotent M) : M.trace = 0 :=
  (Matrix.isNilpotent_trace_of_isNilpotent hM).eq_zero

private theorem isNilpotent_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : IsNilpotent M) : IsNilpotent (M * M) :=
  (Commute.refl M).isNilpotent_mul_left hM

private theorem isNilpotent_mul_self_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : IsNilpotent M) : IsNilpotent (M * M * M) :=
  ((Commute.refl M).mul_left (Commute.refl M)).isNilpotent_mul_left hM

/-- **Trace identities on a nilpotent space.** If `C`, `X + C` and `X - C` are nilpotent,
then `tr(XC) = 0` and `tr(X²C) = 0`. These are the polarized identities `tr((X + C)^k) = 0`
for `k = 2, 3`. -/
theorem trace_mul_eq_zero_of_isNilpotent {n : Type*} [Fintype n] [DecidableEq n]
    {X C : Matrix n n ℂ} (hC : IsNilpotent C)
    (hp : IsNilpotent (X + C)) (hm : IsNilpotent (X - C)) :
    (X * C).trace = 0 ∧ (X * X * C).trace = 0 := by
  have hsq : (X + C) * (X + C) - (X - C) * (X - C) = 2 • (X * C + C * X) := by
    noncomm_ring
  have hcube : (X + C) * (X + C) * (X + C) - (X - C) * (X - C) * (X - C) =
      2 • (X * X * C + X * C * X + C * X * X) + 2 • (C * C * C) := by
    noncomm_ring
  have h2 := congrArg Matrix.trace hsq
  have h3 := congrArg Matrix.trace hcube
  rw [trace_sub, trace_eq_zero_of_isNilpotent (isNilpotent_mul_self hp),
    trace_eq_zero_of_isNilpotent (isNilpotent_mul_self hm), sub_zero, trace_smul,
    trace_add, trace_mul_comm C X] at h2
  rw [trace_sub, trace_eq_zero_of_isNilpotent (isNilpotent_mul_self_mul_self hp),
    trace_eq_zero_of_isNilpotent (isNilpotent_mul_self_mul_self hm), sub_zero, trace_add,
    trace_smul, trace_smul, trace_add, trace_add,
    trace_eq_zero_of_isNilpotent (isNilpotent_mul_self_mul_self hC),
    trace_mul_cycle C X X, trace_mul_cycle X C X] at h3
  constructor
  · have : (2 : ℕ) • ((X * C).trace + (X * C).trace) = 0 := h2.symm
    simp only [nsmul_eq_mul, Nat.cast_ofNat] at this
    linear_combination this / 4
  · have : (2 : ℕ) • ((X * X * C).trace + (X * X * C).trace + (X * X * C).trace) +
        (2 : ℕ) • (0 : ℂ) = 0 := h3.symm
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_zero, add_zero] at this
    linear_combination this / 6

/-- The cyclic shift `J = E₁₂ + E₂₃`. -/
def shiftJ : Mat3 := !![0, 1, 0; 0, 0, 1; 0, 0, 0]

/-- The exceptional partner `B₀ = E₃₂ - E₂₁`. -/
def shiftB : Mat3 := !![0, 0, 0; -1, 0, 0; 0, 1, 0]

/-- The projection `E₂₂` onto the middle coordinate. -/
def gradeE : Mat3 := !![0, 0, 0; 0, 1, 0; 0, 0, 0]

/-- The complementary projection `E₁₁ + E₃₃`. -/
def gradeF : Mat3 := !![1, 0, 0; 0, 0, 0; 0, 0, 1]

/-- In the normalized coordinates, the trace constraints against `J`, `B₀` and `J + B₀`
force `C` to exchange the two grades: `C E₂₂ = (E₁₁ + E₃₃) C`. -/
theorem mul_gradeE_eq_gradeF_mul_of_trace (C : Mat3) (h0 : C.trace = 0)
    (h1 : (C * C).trace = 0) (hJ : (shiftJ * C).trace = 0) (hJJ : (shiftJ * shiftJ * C).trace = 0)
    (hB : (shiftB * C).trace = 0) (hBB : (shiftB * shiftB * C).trace = 0)
    (hJB : ((shiftJ + shiftB) * (shiftJ + shiftB) * C).trace = 0) :
    C * gradeE = gradeF * C := by
  simp only [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diag_apply, shiftJ,
    shiftB, Matrix.add_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at h0 h1 hJ hJJ hB hBB hJB
  ring_nf at h0 h1 hJ hJJ hB hBB hJB
  have h31 : C 2 0 = 0 := by linear_combination hJJ
  have h13 : C 0 2 = 0 := by linear_combination -hBB
  have h32 : C 2 1 = -C 1 0 := by linear_combination hJ
  have h23 : C 1 2 = C 0 1 := by linear_combination hB
  have h33 : C 2 2 = C 0 0 := by linear_combination hJB + h13 - h31
  have h22 : C 1 1 = -2 * C 0 0 := by linear_combination h0 - h33
  have h11sq : C 0 0 ^ 2 = 0 := by
    rw [h22, h33, h32, h23, h13, h31] at h1
    linear_combination (1 / 6 : ℂ) * h1
  have h11 : C 0 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h11sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, gradeE, gradeF, h31, h13, h11, h22, h33]

/-- **Normalizing the exceptional partner.** Let `B` satisfy the trace constraints of a
nilpotent space containing `J`, and suppose `B e₁ ≠ 0`. Then `c = B₃₂ ≠ 0`, and the
unitriangular matrix `S = 1 + αJ + βJ²`, which commutes with `J`, satisfies `B S = c S B₀`. -/
theorem exists_normalizing_of_trace (B : Mat3) (h0 : B.trace = 0) (h1 : (B * B).trace = 0)
    (h2 : (B * B * B).trace = 0) (hJ : (shiftJ * B).trace = 0)
    (hJJ : (shiftJ * shiftJ * B).trace = 0) (hBBJ : (B * B * shiftJ).trace = 0)
    (he : B *ᵥ Pi.single 0 1 ≠ 0) :
    ∃ (c : ℂ) (S : Mat3), c ≠ 0 ∧ S.det = 1 ∧ S * shiftJ = shiftJ * S ∧
      B * S = c • (S * shiftB) := by
  simp only [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diag_apply, shiftJ,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at h0 h1 h2 hJ hJJ hBBJ
  ring_nf at h0 h1 h2 hJ hJJ hBBJ
  have h31 : B 2 0 = 0 := by linear_combination hJJ
  have h21 : B 1 0 = -B 2 1 := by linear_combination hJ
  set c := B 2 1 with hc
  have hc0 : c ≠ 0 := by
    intro hcz
    apply he
    have hz10 : B 1 0 = 0 := by rw [h21, hcz, neg_zero]
    rw [hcz] at h1 h2
    rw [h31, hz10] at h1 h2
    have hp2 : B 0 0 ^ 2 + B 1 1 ^ 2 + B 2 2 ^ 2 = 0 := by linear_combination h1
    have hp3 : B 0 0 ^ 3 + B 1 1 ^ 3 + B 2 2 ^ 3 = 0 := by linear_combination h2
    have he2 : B 0 0 * B 1 1 + B 0 0 * B 2 2 + B 1 1 * B 2 2 = 0 := by
      linear_combination (1 / 2 : ℂ) * (B 0 0 + B 1 1 + B 2 2) * h0 - (1 / 2 : ℂ) * hp2
    have he3 : B 0 0 * B 1 1 * B 2 2 = 0 := by
      linear_combination (1 / 3 : ℂ) * hp3 -
        (1 / 3 : ℂ) * ((B 0 0 + B 1 1 + B 2 2) ^ 2 - 3 * (B 0 0 * B 1 1 + B 0 0 * B 2 2 +
          B 1 1 * B 2 2)) * h0
    have hcube : B 0 0 ^ 3 = 0 := by
      linear_combination B 0 0 ^ 2 * h0 - B 0 0 * he2 + he3
    have h00 : B 0 0 = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h00, hz10, h31]
  have h33 : B 2 2 = B 0 0 := by
    rw [h31, h21] at hBBJ
    have : c * (B 2 2 - B 0 0) = 0 := by linear_combination hBBJ
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc0))
  set sv := B 0 0 with hsv
  have h22 : B 1 1 = -2 * sv := by linear_combination h0 - h33
  set w := B 1 2 with hw
  rw [h31, h21, h22, h33] at h1 h2
  have h12' : c * B 0 1 = c * w + 3 * sv ^ 2 := by linear_combination (-1 / 2 : ℂ) * h1
  have h13' : c ^ 2 * B 0 2 = sv ^ 3 := by linear_combination (-1 / 3 : ℂ) * h2 + sv * h12'
  have h12 : B 0 1 = w + 3 * sv ^ 2 / c := by
    field_simp
    linear_combination h12'
  have h13 : B 0 2 = sv ^ 3 / c ^ 2 := by
    field_simp
    linear_combination h13'
  let α : ℂ := -sv / c
  let β : ℂ := (c * w + 2 * sv ^ 2) / c ^ 2
  refine ⟨c, 1 + α • shiftJ + β • (shiftJ * shiftJ), hc0, ?_, ?_, ?_⟩
  · simp [Matrix.det_fin_three, shiftJ]
  · noncomm_ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, shiftJ, shiftB, α, β, h31, h21, h22, h33,
        h12, h13, ← hc] <;> field_simp <;> ring

/-- A nilpotent `3 × 3` complex matrix has vanishing cube, by the Cayley--Hamilton theorem. -/
theorem cube_eq_zero_of_isNilpotent {A : Mat3} (hA : IsNilpotent A) : A * A * A = 0 := by
  have hchar : A.charpoly = Polynomial.X ^ 3 := by
    have h := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hA).eq_zero
    simpa [sub_eq_zero] using h
  have hCH := Matrix.aeval_self_charpoly A
  rw [hchar, map_pow, Polynomial.aeval_X] at hCH
  simpa [pow_succ, pow_two, Matrix.mul_assoc] using hCH

/-- **A cyclic basis for a nilpotent matrix of index three.** If `A` is nilpotent with
`A² ≠ 0`, then `A` is similar to the cyclic shift `J`. -/
theorem exists_conj_shiftJ (A : Mat3) (hA : IsNilpotent A) (hA2 : A * A ≠ 0) :
    ∃ P : Mat3, IsUnit P.det ∧ A * P = P * shiftJ := by
  have hA3 := cube_eq_zero_of_isNilpotent hA
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → ℂ, (A * A) *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hA2
    ext i j
    simpa [Matrix.mulVec_single] using congrFun (h (Pi.single j 1)) i
  let u1 := (A * A) *ᵥ v
  let u2 := A *ᵥ v
  let P : Mat3 := Matrix.of fun i j ↦ ![u1 i, u2 i, v i] j
  have hPw : ∀ w : Fin 3 → ℂ, P *ᵥ w = w 0 • u1 + w 1 • u2 + w 2 • v := by
    intro w
    ext i
    simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hAu1 : A *ᵥ u1 = 0 := by
    simp only [u1, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA3, Matrix.zero_mulVec]
  have hAu2 : A *ᵥ u2 = u1 := by simp only [u1, u2, Matrix.mulVec_mulVec]
  have hAv : A *ᵥ v = u2 := rfl
  refine ⟨P, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    apply (Matrix.mulVec_injective_iff_isUnit).mp
    intro w₁ w₂ hw
    have h0 : P *ᵥ (w₁ - w₂) = 0 := by rw [Matrix.mulVec_sub, hw, sub_self]
    set w := w₁ - w₂ with hwdef
    rw [hPw] at h0
    have hA2u1 : (A * A) *ᵥ u1 = 0 := by
      rw [← Matrix.mulVec_mulVec, hAu1, Matrix.mulVec_zero]
    have hA2u2 : (A * A) *ᵥ u2 = 0 := by
      rw [← Matrix.mulVec_mulVec, hAu2, hAu1]
    have e2 : w 2 • u1 = 0 := by
      have := congrArg (fun x ↦ (A * A) *ᵥ x) h0
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hA2u1, hA2u2] using this
    have hw2 : w 2 = 0 := (smul_eq_zero.mp e2).resolve_right hv
    have e1 : w 1 • u1 = 0 := by
      have := congrArg (fun x ↦ A *ᵥ x) h0
      simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hAu1, hAu2, hAv, hw2] using this
    have hw1 : w 1 = 0 := (smul_eq_zero.mp e1).resolve_right hv
    have hw0 : w 0 = 0 := by
      have : w 0 • u1 = 0 := by simpa [hw1, hw2] using h0
      exact (smul_eq_zero.mp this).resolve_right hv
    have hwz : w = 0 := by
      ext i
      fin_cases i <;> simp [hw0, hw1, hw2]
    exact sub_eq_zero.mp hwz
  · ext i j
    have hcol : ∀ k : Fin 3, (A * P) i k = (A *ᵥ fun l ↦ P l k) i := fun k ↦ rfl
    rw [hcol]
    fin_cases j
    · simp [hAu1, Matrix.mul_apply, Fin.sum_univ_three, shiftJ, P]
    · simp [hAu2, Matrix.mul_apply, Fin.sum_univ_three, shiftJ, P]
    · simp [hAv, Matrix.mul_apply, Fin.sum_univ_three, shiftJ, P]

private theorem isNilpotent_conj {Q Qinv M : Mat3} (hQ : Q * Qinv = 1) (hM : IsNilpotent M) :
    IsNilpotent (Qinv * M * Q) := by
  obtain ⟨n, hn⟩ := hM
  have hpow : ∀ k : ℕ, (Qinv * M * Q) ^ (k + 1) = Qinv * M ^ (k + 1) * Q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      calc Qinv * M ^ (k + 1) * Q * (Qinv * M * Q)
          = Qinv * M ^ (k + 1) * (Q * Qinv) * M * Q := by noncomm_ring
        _ = Qinv * (M ^ (k + 1) * M) * Q := by
          rw [hQ]; noncomm_ring
  refine ⟨n + 1, ?_⟩
  rw [hpow, pow_succ, hn, zero_mul, mul_zero, zero_mul]

/-- **Grading of a nilpotent space in `M₃(ℂ)` without a common kernel.** If every member of
`N` is nilpotent and the members have no common nonzero kernel vector, then there are `P₀, P₁`
with `P₀ + P₁ = 1` and `P₀ - P₁ ≠ 0` such that `M P₀ = P₁ M` for every `M ∈ N`. In suitable
coordinates `N` lies in the span of `J = E₁₂ + E₂₃` and `B₀ = E₃₂ - E₂₁`, the exceptional
similarity type of Wolf's low-dimensional corollary. -/
theorem exists_grading_of_isNilpotent_submodule_fin_three (N : Submodule ℂ Mat3)
    (hN : ∀ M ∈ N, IsNilpotent M) (hker : ∀ v : Fin 3 → ℂ, (∀ M ∈ N, M *ᵥ v = 0) → v = 0) :
    ∃ P₀ P₁ : Mat3, P₀ + P₁ = 1 ∧ P₀ - P₁ ≠ 0 ∧ ∀ M ∈ N, M * P₀ = P₁ * M := by
  classical
  -- An element of index three.
  obtain ⟨A, hAN, hA2⟩ : ∃ A ∈ N, A * A ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨u, hu, hcommon⟩ := exists_common_ker_of_forall_sq_eq_zero N
      (fun M hM ↦ by rw [pow_two]; exact h M hM)
    exact hu (hker u hcommon)
  obtain ⟨P, hPdet, hAP⟩ := exists_conj_shiftJ A (hN A hAN) hA2
  let Pinv := P⁻¹
  have hPinvP : Pinv * P = 1 := Matrix.nonsing_inv_mul P hPdet
  have hPPinv : P * Pinv = 1 := Matrix.mul_nonsing_inv P hPdet
  have hJ : Pinv * A * P = shiftJ := by
    rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, hPinvP, Matrix.one_mul]
  -- A partner moving the kernel line of `J`.
  obtain ⟨B, hBN, hBe⟩ : ∃ B ∈ N, (Pinv * B * P) *ᵥ Pi.single 0 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hv := hker (P *ᵥ (Pi.single 0 1 : Fin 3 → ℂ)) (fun M hM ↦ by
      have key : P * (Pinv * M * P) = M * P := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPPinv, Matrix.one_mul]
      have := congrArg (fun x ↦ P *ᵥ x) (h M hM)
      simp only [Matrix.mulVec_mulVec, key, Matrix.mulVec_zero] at this
      rw [← Matrix.mulVec_mulVec] at this
      exact this)
    have h1 : (Pi.single 0 1 : Fin 3 → ℂ) = 0 := by
      have h2 := congrArg (fun x ↦ Pinv *ᵥ x) hv
      simp only [Matrix.mulVec_mulVec, hPinvP, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      exact h2
    simpa using congrFun h1 0
  set B' := Pinv * B * P with hB'
  have hconj : ∀ M ∈ N, IsNilpotent (Pinv * M * P) := fun M hM ↦ isNilpotent_conj hPPinv (hN M hM)
  have hB'nil : IsNilpotent B' := hconj B hBN
  have hJnil : IsNilpotent shiftJ := hJ ▸ hconj A hAN
  have hsum : ∀ (X Y : Mat3), Pinv * X * P + Pinv * Y * P = Pinv * (X + Y) * P := by
    intro X Y; noncomm_ring
  have hdiff : ∀ (X Y : Mat3), Pinv * X * P - Pinv * Y * P = Pinv * (X - Y) * P := by
    intro X Y; noncomm_ring
  have hJB := trace_mul_eq_zero_of_isNilpotent (X := shiftJ) (C := B') hB'nil
    (by rw [← hJ, hB', hsum]; exact hconj _ (N.add_mem hAN hBN))
    (by rw [← hJ, hB', hdiff]; exact hconj _ (N.sub_mem hAN hBN))
  have hBJ := trace_mul_eq_zero_of_isNilpotent (X := B') (C := shiftJ) hJnil
    (by rw [← hJ, hB', hsum]; exact hconj _ (N.add_mem hBN hAN))
    (by rw [← hJ, hB', hdiff]; exact hconj _ (N.sub_mem hBN hAN))
  obtain ⟨c, S, hc, hSdet, hSJ, hBS⟩ := exists_normalizing_of_trace B'
    (trace_eq_zero_of_isNilpotent hB'nil)
    (trace_eq_zero_of_isNilpotent (isNilpotent_mul_self hB'nil))
    (trace_eq_zero_of_isNilpotent (isNilpotent_mul_self_mul_self hB'nil))
    hJB.1 hJB.2 hBJ.2 hBe
  have hSunit : IsUnit S.det := by rw [hSdet]; exact isUnit_one
  let Sinv := S⁻¹
  have hSinvS : Sinv * S = 1 := Matrix.nonsing_inv_mul S hSunit
  have hSSinv : S * Sinv = 1 := Matrix.mul_nonsing_inv S hSunit
  let Q := P * S
  let Qinv := Sinv * Pinv
  have hQinvQ : Qinv * Q = 1 := by
    change Sinv * Pinv * (P * S) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Pinv, hPinvP, Matrix.one_mul, hSinvS]
  have hQQinv : Q * Qinv = 1 := by
    change P * S * (Sinv * Pinv) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc S, hSSinv, Matrix.one_mul, hPPinv]
  have hQconj : ∀ M : Mat3, Qinv * M * Q = Sinv * (Pinv * M * P) * S := by
    intro M; simp only [Q, Qinv, Matrix.mul_assoc]
  have hJQ : Qinv * A * Q = shiftJ := by
    rw [hQconj, hJ, Matrix.mul_assoc, ← hSJ, ← Matrix.mul_assoc, hSinvS, Matrix.one_mul]
  have hBQ : Qinv * (c⁻¹ • B) * Q = shiftB := by
    have hsm : Pinv * (c⁻¹ • B) * P = c⁻¹ • B' := by rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [hQconj, hsm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, hBS, Matrix.mul_smul,
      ← Matrix.mul_assoc, hSinvS, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hJBQ : Qinv * (A + c⁻¹ • B) * Q = shiftJ + shiftB := by
    rw [Matrix.mul_add, Matrix.add_mul, hJQ, hBQ]
  have hQnil : ∀ M ∈ N, IsNilpotent (Qinv * M * Q) := fun M hM ↦
    isNilpotent_conj hQQinv (hN M hM)
  have hcB : c⁻¹ • B ∈ N := N.smul_mem _ hBN
  have hAB : A + c⁻¹ • B ∈ N := N.add_mem hAN hcB
  -- The traces of every member against the three normalized members.
  have hmem : ∀ M ∈ N, (Qinv * M * Q) * gradeE = gradeF * (Qinv * M * Q) := by
    intro M hM
    have hQsum : ∀ (X Y : Mat3), Qinv * X * Q + Qinv * Y * Q = Qinv * (X + Y) * Q := by
      intro X Y; noncomm_ring
    have hQdiff : ∀ (X Y : Mat3), Qinv * X * Q - Qinv * Y * Q = Qinv * (X - Y) * Q := by
      intro X Y; noncomm_ring
    have htr : ∀ Y ∈ N, ((Qinv * Y * Q) * (Qinv * M * Q)).trace = 0 ∧
        ((Qinv * Y * Q) * (Qinv * Y * Q) * (Qinv * M * Q)).trace = 0 := by
      intro Y hY
      exact trace_mul_eq_zero_of_isNilpotent (hQnil M hM)
        (by rw [hQsum]; exact hQnil _ (N.add_mem hY hM))
        (by rw [hQdiff]; exact hQnil _ (N.sub_mem hY hM))
    have hA' := htr A hAN
    have hB'' := htr _ hcB
    have hAB' := htr _ hAB
    rw [hJQ] at hA'
    rw [hBQ] at hB''
    rw [hJBQ] at hAB'
    exact mul_gradeE_eq_gradeF_mul_of_trace _ (trace_eq_zero_of_isNilpotent (hQnil M hM))
      (trace_eq_zero_of_isNilpotent (isNilpotent_mul_self (hQnil M hM)))
      hA'.1 hA'.2 hB''.1 hB''.2 hAB'.2
  refine ⟨Q * gradeE * Qinv, Q * gradeF * Qinv, ?_, ?_, ?_⟩
  · have hEF : gradeE + gradeF = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [gradeE, gradeF]
    rw [← Matrix.add_mul, ← Matrix.mul_add, hEF, Matrix.mul_one, hQQinv]
  · intro h
    have h' : Qinv * (Q * gradeE * Qinv - Q * gradeF * Qinv) * Q = gradeE - gradeF := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hQinvQ, Matrix.one_mul]
      simp only [Matrix.mul_assoc, hQinvQ, Matrix.mul_one]
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at h'
    have := congrFun (congrFun h' 0) 0
    simp [gradeE, gradeF] at this
  · intro M hM
    have h := hmem M hM
    calc M * (Q * gradeE * Qinv)
        = Q * ((Qinv * M * Q) * gradeE) * Qinv := by
          simp only [← Matrix.mul_assoc, hQQinv, Matrix.one_mul]
      _ = Q * (gradeF * (Qinv * M * Q)) * Qinv := by rw [h]
      _ = Q * gradeF * Qinv * M := by
          simp only [Matrix.mul_assoc, hQQinv, Matrix.mul_one]

end QICLean
