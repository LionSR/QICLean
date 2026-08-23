/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Basic
import QICLean.Channel.KrausRank
import QICLean.Channel.Stinespring
import QICLean.Algebra.MatrixGramUnitary
import QICLean.Analysis.MatrixSqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Ordered completely positive maps (Wolf Section 2.1, Theorem 2.3)

This file proves Wolf's supplied, rectangular form of Theorem 2.3. For CP maps
`Tᵢ : M_{d'}(ℂ) → M_d(ℂ)` with `T₂ - T₁` CP, any two supplied
Heisenberg Stinespring representations are related by a contraction on their
possibly different dilation spaces. The contraction is unique when the
dominating representation has ancilla dimension `rank(τ₂)`.

The proof follows Wolf's Choi/auxiliary-matrix argument. It defines the
normalized matrices `Wᵢ`, obtains the squared norm comparison (2.13) from
Choi order, applies a rectangular contraction factorization, and transports
the result back to the supplied `Vᵢ`. The earlier explicit construction by
concatenating Kraus families is retained as a canonical square corollary.

## Main definitions

* `CPDominates S T` — the CP partial order: `S - T` is completely positive.
* `stinespringW V` — Wolf's normalized auxiliary matrix associated with a
  supplied Stinespring matrix.
* `Matrix.blockTopRows r s` — the rectangular `r × (r+s)` matrix whose rows
  are the first `r` rows of the identity; equivalently, the block `[𝟙_r | 0]`.

## Main results (Wolf Theorem 2.3)

* `CPDominates.exists_supplied_stinespring_contraction` — the source theorem
  for supplied rectangular dilations, including minimal-dilation uniqueness.
* `stinespringW_conjTranspose_mul_self` — the source identity `WᴴW = τ`.
* `Matrix.exists_contraction_mul_of_sqNorm_le` — the rectangular
  factorization of Wolf's norm comparison.
* `CPDominates.exists_stinespring_contraction` — the canonical square
  corollary obtained by appending Kraus families.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.3][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset BigOperators

variable {D : ℕ}

/-! ### The CP partial order -/

/-- **CP partial order**: `S` dominates `T` iff `S - T` is completely positive.
This is the partial order on CP maps used throughout Wolf Chapter 2. -/
def CPDominates {d d' : ℕ}
    (S T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) : Prop :=
  IsKrausCP (S - T)

/-- Reflexivity of the CP order: `T - T = 0` has the empty Kraus family. -/
theorem CPDominates.refl
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    CPDominates T T := by
  refine ⟨0, (fun i : Fin 0 => i.elim0), ?_⟩
  intro X
  simp

/-! ### Rectangular contraction factorization -/

/-- The rectangular contraction factorization used in Wolf's proof of
Theorem 2.3. If `Aᴴ * A ≤ Bᴴ * B`, then `A` factors through `B` on the
left by a contraction.

This is the finite-dimensional Douglas lemma in the orientation of Wolf
Equation (2.13). The row types of `A` and `B` may be different. -/
theorem Matrix.exists_contraction_mul_of_conjTranspose_mul_le
    {n r₁ r₂ : Type*}
    [Fintype n] [DecidableEq n] [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (A : Matrix r₁ n ℂ) (B : Matrix r₂ n ℂ)
    (hAB : Aᴴ * A ≤ Bᴴ * B) :
    ∃ C : Matrix r₁ r₂ ℂ, Cᴴ * C ≤ 1 ∧ A = C * B := by
  classical
  let P : Matrix n n ℂ := Bᴴ * B - Aᴴ * A
  have hP : P.PosSemidef := hAB
  let S : Matrix n n ℂ := hP.isHermitian.cfc Real.sqrt
  have hS_herm : Sᴴ = S := hP.cfc_sqrt_isHermitian.eq
  have hSS : Sᴴ * S = P := by
    rw [hS_herm]
    exact hP.cfc_sqrt_mul_self
  let Abar : Matrix (Sum r₁ (Sum n r₂)) n ℂ := fun x j =>
    match x with
    | Sum.inl a => A a j
    | Sum.inr (Sum.inl i) => S i j
    | Sum.inr (Sum.inr _) => 0
  let Bbar : Matrix (Sum r₁ (Sum n r₂)) n ℂ := fun x j =>
    match x with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr b) => B b j
  have hGram : Abarᴴ * Abar = Bbarᴴ * Bbar := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
      Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp_rw [Matrix.conjTranspose_apply]
    simp only [Abar, Bbar, star_zero, zero_mul, Finset.sum_const_zero, zero_add]
    simp only [add_zero]
    have hSSij := congr_fun (congr_fun hSS i) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply] at hSSij
    change (∑ x : r₁, star (A x i) * A x j) +
        ∑ x : n, star (S x i) * S x j =
      ∑ x : r₂, star (B x i) * B x j
    rw [hSSij]
    simp [P, Matrix.mul_apply]
  obtain ⟨U, hU⟩ :=
    Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq Abar Bbar hGram
  let C : Matrix r₁ r₂ ℂ := fun a b =>
    (U : Matrix (Sum r₁ (Sum n r₂)) (Sum r₁ (Sum n r₂)) ℂ)
      (Sum.inl a) (Sum.inr (Sum.inr b))
  have hfactor : A = C * B := by
    ext a j
    have hentry := congr_fun (congr_fun hU (Sum.inl a)) j
    rw [Matrix.mul_apply] at hentry
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at hentry
    simp only [Abar, Bbar] at hentry
    rw [Matrix.mul_apply]
    simpa [C] using hentry
  let R : Matrix (Sum n r₂) r₂ ℂ := fun x b =>
    (U : Matrix (Sum r₁ (Sum n r₂)) (Sum r₁ (Sum n r₂)) ℂ)
      (Sum.inr x) (Sum.inr (Sum.inr b))
  have hU_iso :
      (U : Matrix (Sum r₁ (Sum n r₂)) (Sum r₁ (Sum n r₂)) ℂ)ᴴ *
          (U : Matrix (Sum r₁ (Sum n r₂)) (Sum r₁ (Sum n r₂)) ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  have hsplit : (1 : Matrix r₂ r₂ ℂ) - Cᴴ * C = Rᴴ * R := by
    ext b c
    have hentry := congr_fun
      (congr_fun hU_iso (Sum.inr (Sum.inr b))) (Sum.inr (Sum.inr c))
    rw [Matrix.mul_apply, Fintype.sum_sum_type] at hentry
    simp only [Matrix.conjTranspose_apply,
      Matrix.one_apply, Sum.inr.injEq] at hentry
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
    simp_rw [Matrix.conjTranspose_apply]
    simp only [Matrix.one_apply, C, R]
    rw [← hentry]
    ring_nf
    rw [Fintype.sum_sum_type]
  refine ⟨C, ?_, hfactor⟩
  rw [Matrix.le_iff, hsplit]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- Quadratic Gram domination is Wolf's squared norm comparison. -/
theorem Matrix.sqNorm_mulVec_le_of_conjTranspose_mul_le
    {n r₁ r₂ : Type*} [Fintype n] [Fintype r₁] [Fintype r₂]
    (A : Matrix r₁ n ℂ) (B : Matrix r₂ n ℂ)
    (hAB : Aᴴ * A ≤ Bᴴ * B) (x : n → ℂ) :
    star (A.mulVec x) ⬝ᵥ A.mulVec x ≤ star (B.mulVec x) ⬝ᵥ B.mulVec x := by
  have hq := (Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg x
  have hA : star x ⬝ᵥ ((Aᴴ * A).mulVec x) =
      star (A.mulVec x) ⬝ᵥ A.mulVec x := by
    calc
      star x ⬝ᵥ ((Aᴴ * A).mulVec x) =
          star x ⬝ᵥ (Aᴴ.mulVec (A.mulVec x)) := by
            rw [Matrix.mulVec_mulVec]
      _ = star (A.mulVec x) ⬝ᵥ A.mulVec x := by
        simpa using Matrix.star_dotProduct_mulVec Aᴴ x (A.mulVec x)
  have hB : star x ⬝ᵥ ((Bᴴ * B).mulVec x) =
      star (B.mulVec x) ⬝ᵥ B.mulVec x := by
    calc
      star x ⬝ᵥ ((Bᴴ * B).mulVec x) =
          star x ⬝ᵥ (Bᴴ.mulVec (B.mulVec x)) := by
            rw [Matrix.mulVec_mulVec]
      _ = star (B.mulVec x) ⬝ᵥ B.mulVec x := by
        simpa using Matrix.star_dotProduct_mulVec Bᴴ x (B.mulVec x)
  rw [Matrix.sub_mulVec, dotProduct_sub, hB, hA] at hq
  exact sub_nonneg.mp hq

/-- Rectangular contraction factorization stated from Wolf's norm comparison
(Equation (2.13), in squared form). -/
theorem Matrix.exists_contraction_mul_of_sqNorm_le
    {n r₁ r₂ : Type*}
    [Fintype n] [DecidableEq n] [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    (A : Matrix r₁ n ℂ) (B : Matrix r₂ n ℂ)
    (hAB : ∀ x : n → ℂ,
      star (A.mulVec x) ⬝ᵥ A.mulVec x ≤ star (B.mulVec x) ⬝ᵥ B.mulVec x) :
    ∃ C : Matrix r₁ r₂ ℂ, Cᴴ * C ≤ 1 ∧ A = C * B := by
  have hGram : Aᴴ * A ≤ Bᴴ * B := by
    rw [Matrix.le_iff]
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact (Matrix.posSemidef_conjTranspose_mul_self B).isHermitian.sub
        (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
    · intro x
      have hq := sub_nonneg.mpr (hAB x)
      have hA : star x ⬝ᵥ ((Aᴴ * A).mulVec x) =
          star (A.mulVec x) ⬝ᵥ A.mulVec x := by
        calc
          star x ⬝ᵥ ((Aᴴ * A).mulVec x) =
              star x ⬝ᵥ (Aᴴ.mulVec (A.mulVec x)) := by
                rw [Matrix.mulVec_mulVec]
          _ = star (A.mulVec x) ⬝ᵥ A.mulVec x := by
            simpa using Matrix.star_dotProduct_mulVec Aᴴ x (A.mulVec x)
      have hB : star x ⬝ᵥ ((Bᴴ * B).mulVec x) =
          star (B.mulVec x) ⬝ᵥ B.mulVec x := by
        calc
          star x ⬝ᵥ ((Bᴴ * B).mulVec x) =
              star x ⬝ᵥ (Bᴴ.mulVec (B.mulVec x)) := by
                rw [Matrix.mulVec_mulVec]
          _ = star (B.mulVec x) ⬝ᵥ B.mulVec x := by
            simpa using Matrix.star_dotProduct_mulVec Bᴴ x (B.mulVec x)
      rw [Matrix.sub_mulVec, dotProduct_sub, hB, hA]
      exact hq
  exact Matrix.exists_contraction_mul_of_conjTranspose_mul_le A B hGram

/-! ### Wolf's auxiliary matrices `Wᵢ` -/

/-- Wolf's auxiliary matrix
`W = (1ᵣ ⊗ ⟨Ω|)(V ⊗ 1)` from the proof of Theorem 2.3.

For `V : ℂᵈ → ℂᵈ' ⊗ ℂʳ`, the matrix `W` maps
`ℂᵈ ⊗ ℂᵈ' → ℂʳ`. Its entries use Wolf's normalized maximally
entangled vector on the `d'`-dimensional factor. -/
noncomputable def stinespringW {d d' r : ℕ}
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ) :
    Matrix (Fin r) (Fin d × Fin d') ℂ :=
  fun j p => ((1 : ℂ) / ((d' : ℝ).sqrt : ℂ)) * V (p.2, j) p.1

@[simp] theorem stinespringW_apply {d d' r : ℕ}
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (j : Fin r) (i : Fin d) (a : Fin d') :
    stinespringW V j (i, a) =
      ((1 : ℂ) / ((d' : ℝ).sqrt : ℂ)) * V (a, j) i := rfl

/-- For a nonzero physical output dimension, Wolf's assignment `V ↦ W` is
injective. This is the elementary inversion of the displayed definition of
`W` in the proof of Theorem 2.3. -/
theorem stinespringW_injective {d d' r : ℕ} [NeZero d'] :
    Function.Injective
      (stinespringW : Matrix (Fin d' × Fin r) (Fin d) ℂ →
        Matrix (Fin r) (Fin d × Fin d') ℂ) := by
  intro V₁ V₂ hW
  apply Matrix.ext
  rintro ⟨a, j⟩ i
  have hentry := congr_fun (congr_fun hW j) (i, a)
  have hdpos : 0 < d' := Nat.pos_of_ne_zero (NeZero.ne d')
  have hsqrt : (((d' : ℝ).sqrt : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hdpos))
  have hc : (1 : ℂ) / ((d' : ℝ).sqrt : ℂ) ≠ 0 := one_div_ne_zero hsqrt
  exact (mul_left_cancel₀ hc hentry)

/-- Left multiplication of a supplied Stinespring matrix by `1 ⊗ C`
becomes left multiplication of Wolf's auxiliary matrix by `C`. -/
theorem stinespringW_kronecker_mul {d d' r₁ r₂ : ℕ}
    (C : Matrix (Fin r₁) (Fin r₂) ℂ)
    (V : Matrix (Fin d' × Fin r₂) (Fin d) ℂ) :
    stinespringW
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin d') (Fin d') ℂ) C * V) =
      C * stinespringW V := by
  ext j ⟨i, a⟩
  simp only [stinespringW_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
    ring
  · intro b _ hba
    have hab : a ≠ b := Ne.symm hba
    simp [hab]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Wolf's `V`-intertwining equation is equivalent to the corresponding
`W`-factorization equation. -/
theorem stinespring_eq_kronecker_mul_iff_W_eq_mul
    {d d' r₁ r₂ : ℕ} [NeZero d']
    (V₁ : Matrix (Fin d' × Fin r₁) (Fin d) ℂ)
    (V₂ : Matrix (Fin d' × Fin r₂) (Fin d) ℂ)
    (C : Matrix (Fin r₁) (Fin r₂) ℂ) :
    V₁ = Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin d') (Fin d') ℂ) C * V₂ ↔
      stinespringW V₁ = C * stinespringW V₂ := by
  constructor
  · rintro rfl
    exact stinespringW_kronecker_mul C V₂
  · intro hW
    apply stinespringW_injective
    rw [hW, stinespringW_kronecker_mul]

/-- The Gram matrix of Wolf's auxiliary `W` is the Choi matrix of the
Heisenberg map represented by the supplied Stinespring matrix `V`.

This is the identity used immediately before Wolf Equation (2.13). -/
theorem stinespringW_conjTranspose_mul_self
    {d d' r : ℕ}
    {T : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (hV : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      T A = Vᴴ * stinespringPi (r := r) A * V) :
    (stinespringW V)ᴴ * stinespringW V = ChoiRectangular.choiMatrix T := by
  classical
  let K : Fin r → Matrix (Fin d') (Fin d) ℂ := fun j a i => V (a, j) i
  have hstV : stinespringV K = V := by
    ext ⟨a, j⟩ i
    rfl
  have hdual : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      T A = ∑ j : Fin r, (K j)ᴴ * A * K j := by
    intro A
    rw [hV A, ← hstV]
    exact stinespring_dual_representation K A
  have hKraus : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      T A = ∑ j : Fin r, (K j)ᴴ * A * ((K j)ᴴ)ᴴ := by
    intro A
    simpa using hdual A
  rw [Channel.choiMatrix_eq_sum_vecMulVec_of_kraus
    (fun j => (K j)ᴴ) T hKraus]
  ext ⟨i, a⟩ ⟨k, b⟩
  rw [Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [stinespringW_apply, Matrix.conjTranspose_apply,
    Matrix.vecMulVec_apply, K]
  change star (((1 : ℂ) / ((d' : ℝ).sqrt : ℂ)) * V (a, j) i) *
      (((1 : ℂ) / ((d' : ℝ).sqrt : ℂ)) * V (b, j) k) =
    ((1 : ℂ) / ((d' : ℝ).sqrt : ℂ)) * star (V (a, j) i) *
      star (((1 : ℂ) / ((d' : ℝ).sqrt : ℂ)) * star (V (b, j) k))
  have hcstar : star ((1 : ℂ) / ((d' : ℝ).sqrt : ℂ)) =
      (1 : ℂ) / ((d' : ℝ).sqrt : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [star_mul, star_mul, hcstar, star_star]
  ring

/-- A matrix with surjective right factor may be cancelled on the right. -/
theorem Matrix.eq_of_mul_eq_mul_of_mulVec_surjective
    {m n p : Type*} [Fintype n] [DecidableEq n] [Fintype p]
    (A B : Matrix m n ℂ) (W : Matrix n p ℂ)
    (hW : Function.Surjective W.mulVec)
    (h : A * W = B * W) : A = B := by
  have hall : ∀ y : n → ℂ, A.mulVec y = B.mulVec y := by
    intro y
    obtain ⟨x, rfl⟩ := hW y
    calc
      A.mulVec (W.mulVec x) = (A * W).mulVec x :=
        Matrix.mulVec_mulVec x A W
      _ = (B * W).mulVec x := congrArg (fun M => M.mulVec x) h
      _ = B.mulVec (W.mulVec x) := (Matrix.mulVec_mulVec x B W).symm
  ext i j
  have hentry := congr_fun (hall (Pi.single j 1)) i
  simpa using hentry

/-- A supplied Stinespring representation at Choi-rank ancilla dimension has
surjective Wolf matrix `W`. This is Wolf's minimality argument: the Gram
identity `WᴴW = τ` gives `rank W = rank τ = r`. -/
theorem stinespringW_mulVec_surjective_of_minimal
    {d d' r : ℕ}
    {T : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (V : Matrix (Fin d' × Fin r) (Fin d) ℂ)
    (hV : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      T A = Vᴴ * stinespringPi (r := r) A * V)
    (hmin : r = Channel.choiRank T) :
    Function.Surjective (stinespringW V).mulVec := by
  have hGram := stinespringW_conjTranspose_mul_self V hV
  have hrank : (stinespringW V).rank = r := by
    calc
      (stinespringW V).rank = ((stinespringW V)ᴴ * stinespringW V).rank :=
        (Matrix.rank_conjTranspose_mul_self (stinespringW V)).symm
      _ = (ChoiRectangular.choiMatrix T).rank := congrArg Matrix.rank hGram
      _ = Channel.choiRank T := rfl
      _ = r := hmin.symm
  change Function.Surjective (stinespringW V).mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  change (stinespringW V).rank = Module.finrank ℂ (Fin r → ℂ)
  simpa using hrank

/-! ### Wolf Theorem 2.3 for supplied rectangular dilations -/

/-- **Wolf Theorem 2.3 (relation between ordered CP maps).**

Let `T₁, T₂ : M_{d'}(ℂ) → M_d(ℂ)` be completely positive maps with
`T₂ ≥ T₁`, and let `Vᵢ : ℂᵈ → ℂᵈ' ⊗ ℂʳᵢ` be supplied Stinespring
representations. Then there is a contraction from the `r₂`-dimensional
ancilla to the `r₁`-dimensional ancilla, represented by
`C : Matrix (Fin r₁) (Fin r₂) ℂ`, such that
`V₁ = (1 ⊗ C) V₂`. If the dominating representation is minimal in
Wolf's sense, `r₂ = rank(τ₂)`, then this `C` is unique.

The proof follows Wolf's order exactly: Choi order gives
`W₁ᴴW₁ ≤ W₂ᴴW₂` (equivalently, his norm comparison (2.13));
the rectangular contraction factorization gives `W₁ = C W₂`; the
`V ↔ W` identity transports this equation back to the supplied dilations;
and minimality makes the supplied `W₂` surjective, which gives uniqueness.

The complete-positivity assumptions are retained exactly as in Wolf's
statement, although each is also forced by its supplied Stinespring identity. -/
theorem CPDominates.exists_supplied_stinespring_contraction
    {d d' r₁ r₂ : ℕ} [NeZero d']
    {T₁ T₂ : Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (_hT₁ : IsKrausCP T₁) (_hT₂ : IsKrausCP T₂)
    (hdom : CPDominates T₂ T₁)
    (V₁ : Matrix (Fin d' × Fin r₁) (Fin d) ℂ)
    (V₂ : Matrix (Fin d' × Fin r₂) (Fin d) ℂ)
    (hV₁ : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      T₁ A = V₁ᴴ * stinespringPi (r := r₁) A * V₁)
    (hV₂ : ∀ A : Matrix (Fin d') (Fin d') ℂ,
      T₂ A = V₂ᴴ * stinespringPi (r := r₂) A * V₂) :
    ∃ C : Matrix (Fin r₁) (Fin r₂) ℂ,
      Cᴴ * C ≤ 1 ∧
      V₁ = Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin d') (Fin d') ℂ) C * V₂ ∧
      (r₂ = Channel.choiRank T₂ →
        ∀ C' : Matrix (Fin r₁) (Fin r₂) ℂ,
          V₁ = Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin d') (Fin d') ℂ) C' * V₂ →
          C' = C) := by
  have hChoiSub : ChoiRectangular.choiMatrix (T₂ - T₁) =
      ChoiRectangular.choiMatrix T₂ - ChoiRectangular.choiMatrix T₁ := by
    exact (ChoiRectangular.choiMatrixLinearMap (d := d') (d' := d)).map_sub T₂ T₁
  have hChoiOrder : ChoiRectangular.choiMatrix T₁ ≤
      ChoiRectangular.choiMatrix T₂ := by
    rw [Matrix.le_iff, ← hChoiSub]
    exact (ChoiRectangular.isKrausCP_iff_choiMatrix_posSemidef (T₂ - T₁)).mp hdom
  have hW₁Gram := stinespringW_conjTranspose_mul_self V₁ hV₁
  have hW₂Gram := stinespringW_conjTranspose_mul_self V₂ hV₂
  have hWOrder : (stinespringW V₁)ᴴ * stinespringW V₁ ≤
      (stinespringW V₂)ᴴ * stinespringW V₂ := by
    rw [hW₁Gram, hW₂Gram]
    exact hChoiOrder
  have hWNorm : ∀ ψ : (Fin d × Fin d') → ℂ,
      star ((stinespringW V₁).mulVec ψ) ⬝ᵥ (stinespringW V₁).mulVec ψ ≤
        star ((stinespringW V₂).mulVec ψ) ⬝ᵥ (stinespringW V₂).mulVec ψ := by
    intro ψ
    exact Matrix.sqNorm_mulVec_le_of_conjTranspose_mul_le
      (stinespringW V₁) (stinespringW V₂) hWOrder ψ
  obtain ⟨C, hC, hWfactor⟩ :=
    Matrix.exists_contraction_mul_of_sqNorm_le
      (stinespringW V₁) (stinespringW V₂) hWNorm
  have hVfactor :
      V₁ = Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin d') (Fin d') ℂ) C * V₂ :=
    (stinespring_eq_kronecker_mul_iff_W_eq_mul V₁ V₂ C).mpr hWfactor
  refine ⟨C, hC, hVfactor, ?_⟩
  intro hmin C' hVfactor'
  have hWfactor' :=
    (stinespring_eq_kronecker_mul_iff_W_eq_mul V₁ V₂ C').mp hVfactor'
  have hsurj := stinespringW_mulVec_surjective_of_minimal V₂ hV₂ hmin
  exact Matrix.eq_of_mul_eq_mul_of_mulVec_surjective C' C (stinespringW V₂) hsurj
    (hWfactor'.symm.trans hWfactor)

/-! ### The block-top rectangular co-isometry -/

/-- The block-top rectangular matrix `C : Fin r → Fin (r+s)` whose rows are
the first `r` rows of `𝟙_{r+s}`. Concretely, `C i j = 1` if `j = castAdd s i`
and `0` otherwise. This is the canonical co-isometry from `ℂ^{r+s}` onto
`ℂ^r` that picks out the first `r` coordinates. -/
noncomputable def Matrix.blockTopRows (r s : ℕ) :
    Matrix (Fin r) (Fin (r + s)) ℂ :=
  fun i j => if j = Fin.castAdd s i then 1 else 0

theorem Matrix.blockTopRows_apply (r s : ℕ) (i : Fin r) (j : Fin (r + s)) :
    blockTopRows r s i j = if j = Fin.castAdd s i then 1 else 0 := rfl

@[simp] theorem Matrix.blockTopRows_apply_castAdd (r s : ℕ) (i : Fin r) :
    blockTopRows r s i (Fin.castAdd s i) = 1 := by
  simp [Matrix.blockTopRows]

/-- `C * Cᴴ = 𝟙_r` for the block-top projector. -/
theorem Matrix.blockTopRows_mul_conjTranspose (r s : ℕ) :
    (blockTopRows r s) * (blockTopRows r s)ᴴ = (1 : Matrix (Fin r) (Fin r) ℂ) := by
  ext i i'
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.blockTopRows_apply]
  have hterm : ∀ j : Fin (r + s),
      (if j = Fin.castAdd s i then (1 : ℂ) else 0) *
        star (if j = Fin.castAdd s i' then (1 : ℂ) else 0) =
      if j = Fin.castAdd s i ∧ j = Fin.castAdd s i' then 1 else 0 := by
    intro j
    by_cases h1 : j = Fin.castAdd s i <;> by_cases h2 : j = Fin.castAdd s i' <;>
      simp [h1, h2]
  simp_rw [hterm]
  by_cases hii : i = i'
  · subst hii
    rw [Finset.sum_eq_single (Fin.castAdd s i)]
    · simp [Matrix.one_apply_eq]
    · intro b _ hb
      simp [hb]
    · intro hj; exact absurd (Finset.mem_univ (Fin.castAdd s i)) hj
  · have hcast : Fin.castAdd s i ≠ Fin.castAdd s i' := by
      intro h; exact hii (Fin.castAdd_injective r s h)
    have hsum : ∑ j : Fin (r + s),
        (if j = Fin.castAdd s i ∧ j = Fin.castAdd s i' then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      split_ifs with hk
      · exact absurd (hk.1.symm.trans hk.2) hcast
      · rfl
    rw [hsum, Matrix.one_apply_ne hii]

/-- The "diagonal" block-top projector `Cᴴ * C` equals the diagonal matrix that
is `1` on the first `r` coordinates and `0` on the last `s`. -/
theorem Matrix.blockTopRows_conjTranspose_mul_apply (r s : ℕ)
    (j j' : Fin (r + s)) :
    ((blockTopRows r s)ᴴ * blockTopRows r s) j j' =
      if j = j' ∧ (j : ℕ) < r then 1 else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.blockTopRows_apply]
  have hterm : ∀ k : Fin r,
      star (if j = Fin.castAdd s k then (1 : ℂ) else 0) *
        (if j' = Fin.castAdd s k then 1 else 0) =
      if j = Fin.castAdd s k ∧ j' = Fin.castAdd s k then 1 else 0 := by
    intro k
    by_cases h1 : j = Fin.castAdd s k <;> by_cases h2 : j' = Fin.castAdd s k <;>
      simp [h1, h2]
  simp_rw [hterm]
  by_cases hjr : (j : ℕ) < r
  · set jFin : Fin r := ⟨(j : ℕ), hjr⟩ with hjFin
    have hj : j = Fin.castAdd s jFin := by
      ext; simp [Fin.castAdd, hjFin]
    by_cases hjeq : j = j'
    · subst hjeq
      have hconv : ∀ k : Fin r,
          (if j = Fin.castAdd s k ∧ j = Fin.castAdd s k then (1 : ℂ) else 0) =
          if k = jFin then 1 else 0 := by
        intro k
        by_cases hk : j = Fin.castAdd s k
        · have hkF : k = jFin := by
            have : Fin.castAdd s k = Fin.castAdd s jFin := hk.symm.trans hj
            exact Fin.castAdd_injective r s this
          simp [hk, hkF]
        · have hkF : k ≠ jFin := by
            intro he; apply hk; rw [he]; exact hj
          simp [hk, hkF]
      simp_rw [hconv]
      rw [Finset.sum_eq_single jFin]
      · simp [hjr]
      · intro b _ hb; simp [hb]
      · intro hj'; exact absurd (Finset.mem_univ jFin) hj'
    · have hrhs : ¬ (j = j' ∧ (j : ℕ) < r) := fun ⟨h, _⟩ => hjeq h
      rw [ite_eq_right hrhs]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) hjeq
      · rfl
  · have hrhs : ¬ (j = j' ∧ (j : ℕ) < r) := fun ⟨_, h⟩ => hjr h
    rw [ite_eq_right hrhs]
    apply Finset.sum_eq_zero
    intro k _
    have hk : j ≠ Fin.castAdd s k := by
      intro he
      have := Fin.val_eq_of_eq he
      simp [Fin.castAdd] at this
      omega
    simp [hk]

/-- **C is a contraction**: `Cᴴ * C ≤ 𝟙_{r+s}`. -/
theorem Matrix.blockTopRows_conjTranspose_mul_le_one (r s : ℕ) :
    (blockTopRows r s)ᴴ * blockTopRows r s ≤ (1 : Matrix (Fin (r+s)) (Fin (r+s)) ℂ) := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian.
    ext j j'
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
      Matrix.blockTopRows_conjTranspose_mul_apply]
    by_cases hjj : j = j'
    · subst hjj
      by_cases hjr : (j : ℕ) < r
      all_goals simp [hjr]
    · have hne : j' ≠ j := fun h => hjj h.symm
      simp [hjj, hne]
  · -- PSD condition.
    intro x
    -- Compute ((1 - CᴴC).mulVec x) j entrywise.
    have hmul : ∀ j : Fin (r + s),
        (((1 : Matrix (Fin (r+s)) (Fin (r+s)) ℂ) -
            ((blockTopRows r s)ᴴ * blockTopRows r s)) *ᵥ x) j =
        (if (j : ℕ) < r then 0 else x j) := by
      intro j
      rw [Matrix.sub_mulVec]
      rw [Matrix.one_mulVec]
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
      simp_rw [Matrix.blockTopRows_conjTranspose_mul_apply]
      by_cases hjr : (j : ℕ) < r
      · rw [ite_eq_left hjr]
        have hsum : ∑ j' : Fin (r + s),
            (if j = j' ∧ (j : ℕ) < r then (1 : ℂ) else 0) * x j' = x j := by
          rw [Finset.sum_eq_single j]
          · simp [hjr]
          · intro b _ hb
            have : ¬ (j = b ∧ (j : ℕ) < r) := fun ⟨hjb, _⟩ => hb hjb.symm
            simp [this]
          · intro hj; exact absurd (Finset.mem_univ j) hj
        rw [hsum, sub_self]
      · rw [ite_eq_right hjr]
        have hsum : ∑ j' : Fin (r + s),
            (if j = j' ∧ (j : ℕ) < r then (1 : ℂ) else 0) * x j' = 0 := by
          apply Finset.sum_eq_zero
          intro j' _
          split_ifs with h
          · exact absurd h.2 hjr
          · ring
        rw [hsum, sub_zero]
    simp only [dotProduct]
    refine Finset.sum_nonneg fun j _ => ?_
    rw [hmul]
    by_cases hjr : (j : ℕ) < r
    · simp [hjr]
    · simp only [hjr, ite_false]
      change 0 ≤ star (x j) * x j
      have hsq : star (x j) * x j = ((‖x j‖ : ℝ) ^ 2 : ℂ) := by
        simpa [Complex.star_def, Complex.normSq_eq_norm_sq] using
          (Complex.normSq_eq_conj_mul_self (z := x j)).symm
      rw [hsq]
      exact_mod_cast sq_nonneg ‖x j‖

/-! ### Intertwining identity for the canonical Stinespring matrices -/

/-- **Entrywise intertwining (canonical square corollary of Wolf Theorem 2.3)**:
the block-top
co-isometry `C = blockTopRows r s` relates the Stinespring matrix of a Kraus
family `K : Fin r → M` with that of its append with another family
`L : Fin s → M`:
  `stinespringV K = (𝟙_D ⊗ C) * stinespringV (Fin.append K L)`. -/
theorem stinespringV_eq_kronecker_blockTopRows_mul_append
    {r s : ℕ}
    (K : Fin r → Matrix (Fin D) (Fin D) ℂ)
    (L : Fin s → Matrix (Fin D) (Fin D) ℂ) :
    stinespringV K =
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ)
          (Matrix.blockTopRows r s)) *
        stinespringV (Fin.append K L) := by
  ext ⟨i, j₁⟩ k
  simp only [stinespringV_apply, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.blockTopRows_apply]
  -- Reduce double sum to a single value.
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single (Fin.castAdd s j₁)]
    · simp [Fin.append_left, Matrix.one_apply_eq]
    · intro b _ hb
      simp [Matrix.one_apply_eq, hb]
    · intro hj; exact absurd (Finset.mem_univ (Fin.castAdd s j₁)) hj
  · intro b _ hb
    refine Finset.sum_eq_zero ?_
    intro j _
    have : ((1 : Matrix (Fin D) (Fin D) ℂ) i b) = 0 := Matrix.one_apply_ne (Ne.symm hb)
    simp [this]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-! ### Canonical square corollary -/

/-- **Canonical square corollary of Wolf Theorem 2.3.**

Let `T₁, T₂ : M_D(ℂ) →ₗ M_D(ℂ)` be CP maps with `T₁ ≤ T₂` in the CP partial
order (i.e. `T₂ - T₁` is CP). Then there exist an ancilla dimension `m`,
Heisenberg-form Stinespring matrices
`V₁ : Matrix (Fin D × Fin r₁) (Fin D) ℂ` and
`V₂ : Matrix (Fin D × Fin m) (Fin D) ℂ` realizing `Tᵢ(A) = Vᵢᴴ * (A ⊗ 𝟙) * Vᵢ`,
together with a **contraction** `C : Matrix (Fin r₁) (Fin m) ℂ` satisfying
`Cᴴ * C ≤ 𝟙` and the intertwining identity `V₁ = (𝟙_D ⊗ C) * V₂`.

In the canonical realization returned below, `m = r₁ + s` where `s` is a Kraus
length of `T₂ - T₁`, the two Stinespring matrices come from conjugated Kraus
families, and `C = blockTopRows r₁ s`. -/
theorem CPDominates.exists_stinespring_contraction
    {T₁ T₂ : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT₁ : IsCPMap T₁) (hdom : CPDominates T₂ T₁) :
    ∃ (r₁ m : ℕ)
      (K₁ : Fin r₁ → Matrix (Fin D) (Fin D) ℂ)
      (K₂ : Fin m → Matrix (Fin D) (Fin D) ℂ)
      (C : Matrix (Fin r₁) (Fin m) ℂ),
      (∀ A, T₁ A =
        (stinespringV K₁)ᴴ * stinespringPi (r := r₁) A * stinespringV K₁) ∧
      (∀ A, T₂ A =
        (stinespringV K₂)ᴴ * stinespringPi (r := m) A * stinespringV K₂) ∧
      Cᴴ * C ≤ 1 ∧
      stinespringV K₁ =
        (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin D) (Fin D) ℂ) C) *
          stinespringV K₂ := by
  obtain ⟨r₁, K₁h, hK₁⟩ := exists_stinespring_dilation T₁ hT₁
  obtain ⟨s, L, hL⟩ := hdom
  let Lh : Fin s → Matrix (Fin D) (Fin D) ℂ := fun j => (L j)ᴴ
  let K₂ : Fin (r₁ + s) → Matrix (Fin D) (Fin D) ℂ := Fin.append K₁h Lh
  refine ⟨r₁, r₁ + s, K₁h, K₂, Matrix.blockTopRows r₁ s, hK₁, ?_, ?_, ?_⟩
  · -- T₂ Heisenberg identity.
    intro A
    have hsum : T₂ A = T₁ A + (T₂ - T₁) A := by
      simp [LinearMap.sub_apply]
    rw [hsum, hK₁, hL]
    have hLsum : ∑ j : Fin s, L j * A * (L j)ᴴ =
        ∑ j : Fin s, (Lh j)ᴴ * A * (Lh j) := by
      refine Finset.sum_congr rfl ?_
      intro j _; simp [Lh]
    rw [hLsum]
    have hStK₂ : ∑ j : Fin (r₁ + s), (K₂ j)ᴴ * A * (K₂ j) =
        (stinespringV K₂)ᴴ * stinespringPi (r := r₁ + s) A * stinespringV K₂ :=
      (stinespring_dual_representation (K := K₂) (A := A)).symm
    have hStK₁ : ∑ i : Fin r₁, (K₁h i)ᴴ * A * (K₁h i) =
        (stinespringV K₁h)ᴴ * stinespringPi (r := r₁) A * stinespringV K₁h :=
      (stinespring_dual_representation (K := K₁h) (A := A)).symm
    have hSplit : ∑ j : Fin (r₁ + s), (K₂ j)ᴴ * A * (K₂ j) =
        (∑ i : Fin r₁, (K₁h i)ᴴ * A * (K₁h i)) +
        (∑ j : Fin s, (Lh j)ᴴ * A * (Lh j)) := by
      rw [Fin.sum_univ_add]
      congr 1 <;>
      · refine Finset.sum_congr rfl ?_
        intro i _
        simp [K₂, Fin.append_left, Fin.append_right]
    rw [← hStK₁, ← hStK₂, hSplit]
  · exact Matrix.blockTopRows_conjTranspose_mul_le_one r₁ s
  · exact stinespringV_eq_kronecker_blockTopRows_mul_append K₁h Lh
