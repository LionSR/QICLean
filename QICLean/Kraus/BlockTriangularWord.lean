/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Block
import QICLean.Kraus.Word

/-!
# Block-triangular word products and coordinate embeddings

Diagonal blocks of a product of block upper-triangular matrices multiply, word evaluations of a
block upper-triangular family stay block upper triangular with word-evaluated diagonal blocks,
and the coordinate embeddings and projections of each block form a biorthogonal system that
reassembles a block-diagonal matrix. The file closes with a nilpotency count: a product of as many
strictly block upper-triangular matrices as there are blocks vanishes.

Blocks are indexed by a type `o` which is ordered indirectly, through an injective labelling
`b : o → α` into a linear order; the case `b = id` recovers the usual block-triangular
statements for an ordered block index. The indirect form covers block families whose labels and
whose order are separate data.

Word evaluation on the `Σ k, Fin (n k)` index type is `Kraus.evalWord`, which takes any finite
basis.

Moved from TNLean, `TNLean/Algebra/BlockTriangularWord.lean` at commit `49b78ed821`
(Apache-2.0).

## Main results

* `Matrix.blockDiag'_mul_of_blockTriangular` — diagonal blocks of a product of block
  upper-triangular matrices multiply (Lemma 7.3 of the TNLean note on asymmetric compressions).
* `Matrix.blockTriangular_evalWord` — word evaluations of a block upper-triangular family
  stay block upper triangular.
* `Matrix.blockDiag'_evalWord` — diagonal blocks of a word evaluation are the word
  evaluations of the diagonal blocks.
* `Matrix.blockEmbed`, `Matrix.blockProj` — coordinate embedding/projection of a block, with
  the biorthogonality relations `Matrix.blockProj_mul_blockEmbed_self`,
  `Matrix.blockProj_mul_blockEmbed_of_ne`, `Matrix.blockProj_mul_mul_blockEmbed`, and the
  reassembly identity `Matrix.sum_blockEmbed_mul_mul_blockProj`.
* `Matrix.StrictBlockTriangular` and `Matrix.evalWord_eq_zero_of_strictBlockTriangular` — a
  product of as many strictly block upper-triangular matrices as there are blocks vanishes.

## References

TNLean note on asymmetric compressions, Lemma 7.3 and Theorem 7.7(vi).

Moved from TNLean, `TNLean/MPS/FundamentalTheorem/Compression/LongWords.lean`,
`TNLean/MPS/FundamentalTheorem/Compression/UniquenessSameFlag.lean`,
`TNLean/MPS/FundamentalTheorem/Compression/SplitUniqueness.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

open scoped Matrix

namespace Matrix

variable {o : Type*} [Fintype o] [DecidableEq o] {n : o → ℕ} {ι : Type*}

section Order

variable {α : Type*} [LinearOrder α] {b : o → α}

omit [DecidableEq o] in
/-- Diagonal blocks of a product of block upper-triangular matrices multiply. -/
theorem blockDiag'_mul_of_blockTriangular (hb : Function.Injective b)
    {X Y : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hX : X.BlockTriangular fun x => b x.1) (hY : Y.BlockTriangular fun x => b x.1) (k : o) :
    (X * Y).blockDiag' k = X.blockDiag' k * Y.blockDiag' k := by
  ext i j
  simp only [blockDiag'_apply, Matrix.mul_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [Finset.sum_eq_single k]
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro i' _
    rcases lt_or_lt_iff_ne.mpr (fun h : b l = b k => hl (hb h)) with hlt | hgt
    · have hX0 : X ⟨k, i⟩ ⟨l, i'⟩ = 0 := hX hlt
      rw [hX0, zero_mul]
    · have hY0 : Y ⟨l, i'⟩ ⟨k, j⟩ = 0 := hY hgt
      rw [hY0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Word evaluations of a block upper-triangular family stay block upper triangular. -/
theorem blockTriangular_evalWord
    {T : ι → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hT : ∀ i, (T i).BlockTriangular fun x => b x.1) (w : List ι) :
    (Kraus.evalWord T w).BlockTriangular fun x => b x.1 := by
  induction w with
  | nil => simpa [Kraus.evalWord] using blockTriangular_one
  | cons i w ih => simpa only [Kraus.evalWord] using (hT i).mul ih

/-- Diagonal blocks of a word evaluation are the word evaluations of the diagonal blocks. -/
theorem blockDiag'_evalWord (hb : Function.Injective b)
    {T : ι → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hT : ∀ i, (T i).BlockTriangular fun x => b x.1) (w : List ι) (k : o) :
    (Kraus.evalWord T w).blockDiag' k = Kraus.evalWord (fun i => (T i).blockDiag' k) w := by
  induction w with
  | nil => simp [Kraus.evalWord]
  | cons i w ih =>
      simp only [Kraus.evalWord]
      rw [blockDiag'_mul_of_blockTriangular hb (hT i) (blockTriangular_evalWord hT w) k, ih]

end Order

section Embed

/-- Coordinate embedding of the `k`-th block. -/
def blockEmbed (n : o → ℕ) (k : o) : Matrix (Σ k, Fin (n k)) (Fin (n k)) ℂ :=
  Matrix.of fun x j => if x = ⟨k, j⟩ then 1 else 0

/-- Coordinate projection onto the `k`-th block: the transpose of the embedding. -/
def blockProj (n : o → ℕ) (k : o) : Matrix (Fin (n k)) (Σ k, Fin (n k)) ℂ :=
  (blockEmbed n k).transpose

omit [Fintype o] in
/-- The block embedding vanishes away from its recorded coordinate. -/
theorem blockEmbed_apply_of_ne {k : o} {x : Σ k, Fin (n k)} {j : Fin (n k)}
    (h : x ≠ (⟨k, j⟩ : Σ k, Fin (n k))) : blockEmbed n k x j = 0 := by
  simp [blockEmbed, Matrix.of_apply, h]

omit [Fintype o] in
/-- The block embedding vanishes off its own block. -/
theorem blockEmbed_apply_of_fst_ne {k : o} {x : Σ k, Fin (n k)} (h : x.1 ≠ k) (j : Fin (n k)) :
    blockEmbed n k x j = 0 :=
  blockEmbed_apply_of_ne fun heq => h (congrArg Sigma.fst heq)

omit [Fintype o] in
/-- The block embedding restricted to its own block is the identity indicator. -/
theorem blockEmbed_apply_fst_eq (k : o) (i j : Fin (n k)) :
    blockEmbed n k (⟨k, i⟩ : Σ k, Fin (n k)) j = if i = j then 1 else 0 := by
  simp [blockEmbed, Matrix.of_apply, Sigma.mk.injEq]

omit [Fintype o] in
/-- The block embedding restricted to its own block vanishes off the matching coordinate. -/
theorem blockEmbed_apply_fst_eq_of_ne {k : o} {i j : Fin (n k)} (h : i ≠ j) :
    blockEmbed n k (⟨k, i⟩ : Σ k, Fin (n k)) j = 0 := by
  rw [blockEmbed_apply_fst_eq]; simp [h]

theorem blockProj_mul_blockEmbed_self (k : o) : blockProj n k * blockEmbed n k = 1 := by
  ext i j
  simp only [Matrix.mul_apply, blockProj, Matrix.transpose_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (⟨k, i⟩ : Σ k, Fin (n k))]
  · rw [blockEmbed_apply_fst_eq, blockEmbed_apply_fst_eq]
    simp
  · intro x _ hx
    rw [blockEmbed_apply_of_ne hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (⟨k, i⟩ : Σ k, Fin (n k))) h

theorem blockProj_mul_blockEmbed_of_ne {k l : o} (h : k ≠ l) :
    blockProj n k * blockEmbed n l = 0 := by
  ext i j
  simp only [Matrix.mul_apply, blockProj, Matrix.transpose_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x _
  rcases eq_or_ne x.1 k with hx | hx
  · have hxne : x.1 ≠ l := hx ▸ h
    rw [blockEmbed_apply_of_fst_ne hxne, mul_zero]
  · rw [blockEmbed_apply_of_fst_ne hx, zero_mul]

theorem blockProj_mul_mul_blockEmbed (M : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) (k : o) :
    blockProj n k * M * blockEmbed n k = M.blockDiag' k := by
  ext i j
  simp only [Matrix.mul_apply, blockDiag'_apply]
  rw [Finset.sum_eq_single (⟨k, j⟩ : Σ k, Fin (n k))]
  · rw [Finset.sum_eq_single (⟨k, i⟩ : Σ k, Fin (n k))]
    · simp [blockProj, Matrix.transpose_apply, blockEmbed_apply_fst_eq]
    · intro y _ hy
      simp only [blockProj, Matrix.transpose_apply]
      rw [blockEmbed_apply_of_ne hy, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (⟨k, i⟩ : Σ k, Fin (n k))) h
  · intro x _ hx
    rw [blockEmbed_apply_of_ne hx, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (⟨k, j⟩ : Σ k, Fin (n k))) h

/-- Reassembling the diagonal blocks: `∑ k, P k * D k * Q k = blockDiagonal' D`. -/
theorem sum_blockEmbed_mul_mul_blockProj (D : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) :
    ∑ k, blockEmbed n k * D k * blockProj n k = Matrix.blockDiagonal' D := by
  ext x y
  obtain ⟨kx, ix⟩ := x
  obtain ⟨ky, iy⟩ := y
  simp only [Matrix.sum_apply]
  by_cases hxy : kx = ky
  · subst hxy
    rw [blockDiagonal'_apply_eq]
    rw [Finset.sum_eq_single kx]
    · simp only [Matrix.mul_apply]
      rw [Finset.sum_eq_single iy]
      · rw [Finset.sum_eq_single ix]
        · simp [blockProj, Matrix.transpose_apply, blockEmbed_apply_fst_eq]
        · intro b _ hb
          rw [blockEmbed_apply_fst_eq_of_ne hb.symm, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ ix) h
      · intro a _ ha
        simp only [blockProj, Matrix.transpose_apply]
        rw [blockEmbed_apply_fst_eq_of_ne ha.symm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ iy) h
    · intro k _ hk
      have hne : kx ≠ k := hk.symm
      simp only [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a _
      simp [blockEmbed_apply_of_fst_ne (x := (⟨kx, ix⟩ : Σ k, Fin (n k))) hne]
    · intro h
      exact absurd (Finset.mem_univ kx) h
  · rw [blockDiagonal'_apply_ne D ix iy hxy]
    apply Finset.sum_eq_zero
    intro k _
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases hk : kx = k
    · have hne : ky ≠ k := fun heq => hxy (hk.trans heq.symm)
      simp only [blockProj, Matrix.transpose_apply]
      rw [blockEmbed_apply_of_fst_ne (x := (⟨ky, iy⟩ : Σ k, Fin (n k))) hne, mul_zero]
    · have hne : kx ≠ k := hk
      simp [blockEmbed_apply_of_fst_ne (x := (⟨kx, ix⟩ : Σ k, Fin (n k))) hne]

end Embed

section Strict

variable {α : Type*} [LinearOrder α]

/-- Strictly block upper triangular for the block labelling `b`: entries whose column block
label is at most their row block label vanish. -/
def StrictBlockTriangular (b : o → α) (M : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) : Prop :=
  ∀ ⦃x y⦄, b y.1 ≤ b x.1 → M x y = 0

variable {b : o → α}

omit [Fintype o] [DecidableEq o] in
theorem strictBlockTriangular_of_blockTriangular_of_blockDiag'_eq_zero
    (hb : Function.Injective b) {M : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hM : M.BlockTriangular fun x => b x.1) (hd : ∀ k, M.blockDiag' k = 0) :
    StrictBlockTriangular b M := by
  rintro ⟨kx, ix⟩ ⟨ky, iy⟩ hxy
  rcases hxy.lt_or_eq with hlt | heq
  · exact hM hlt
  · obtain rfl : ky = kx := hb heq
    have h2 : M.blockDiag' ky ix iy = 0 := by rw [hd ky]; simp
    rwa [blockDiag'_apply] at h2

omit [Fintype o] in
theorem StrictBlockTriangular.sub_blockDiagonal'_blockDiag' (hb : Function.Injective b)
    {M : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hM : M.BlockTriangular fun x => b x.1) :
    StrictBlockTriangular b (M - Matrix.blockDiagonal' M.blockDiag') := by
  have hdiag : (Matrix.blockDiagonal' M.blockDiag').BlockTriangular fun x => b x.1 := by
    rintro ⟨kx, ix⟩ ⟨ky, iy⟩ hlt
    have hne : kx ≠ ky := by
      rintro rfl
      exact absurd hlt (lt_irrefl _)
    exact Matrix.blockDiagonal'_apply_ne M.blockDiag' ix iy hne
  refine strictBlockTriangular_of_blockTriangular_of_blockDiag'_eq_zero hb (hM.sub hdiag) ?_
  intro k
  simp

end Strict

section Nilpotency

variable {r : ℕ} {b : o → Fin r}

/-- Auxiliary entrywise bound for a word evaluation of strictly block upper-triangular
matrices: `m` letters move the block label up by at least `m`. -/
theorem entry_evalWord_eq_zero_of_lt
    {R : ι → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hR : ∀ i, StrictBlockTriangular b (R i)) :
    ∀ (w : List ι) (x y : Σ k, Fin (n k)),
      (b y.1 : ℕ) < (b x.1 : ℕ) + w.length → Kraus.evalWord R w x y = 0 := by
  intro w
  induction w with
  | nil =>
      intro x y h
      simp only [List.length_nil, Nat.add_zero] at h
      have hxy : x ≠ y := by
        rintro rfl
        exact absurd h (lt_irrefl _)
      simp [Kraus.evalWord, hxy]
  | cons i w' ih =>
      intro x y h
      simp only [List.length_cons] at h
      simp only [Kraus.evalWord, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hzx : b z.1 ≤ b x.1
      · rw [hR i hzx, zero_mul]
      · have hzx' : (b x.1 : ℕ) < (b z.1 : ℕ) := Fin.lt_def.mp (not_le.mp hzx)
        have hzy : (b y.1 : ℕ) < (b z.1 : ℕ) + w'.length := by omega
        rw [ih z y hzy, mul_zero]

/-- A product of `r` strictly block upper-triangular matrices whose block labels take at most
`r` values vanishes. -/
theorem evalWord_eq_zero_of_strictBlockTriangular
    {R : ι → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hR : ∀ i, StrictBlockTriangular b (R i)) (w : List ι) (hw : r ≤ w.length) :
    Kraus.evalWord R w = 0 := by
  ext x y
  have hy : (b y.1 : ℕ) < r := (b y.1).isLt
  exact entry_evalWord_eq_zero_of_lt hR w x y (by omega)

end Nilpotency

end Matrix

section

open scoped Matrix

namespace Matrix

variable {o : Type*} [Fintype o] [DecidableEq o] {n : o → ℕ} {d r : ℕ} {b : o → Fin r}

/-- **The chain count** (proof of blueprint `lem:asym_uniq_long_words`, *Long words in a triangular
form*). Let `T` be a family of block upper-triangular matrices for an injective labelling `b` of the
blocks by positions. If every block at a position between those of `x` and `y` has zero diagonal
block in every letter, and the word is longer than the distance from the position of `x` to that of
`y`, then the `(x, y)` entry of the word vanishes: every nondecreasing chain of positions from `x`
to `y` has an equal step, whose factor is a zero diagonal block. -/
theorem entry_evalWord_eq_zero_of_blockDiag'_eq_zero (hb : Function.Injective b)
    {T : Fin d → Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ}
    (hT : ∀ i, (T i).BlockTriangular fun x => b x.1) :
    ∀ (w : List (Fin d)) (x y : Σ k, Fin (n k)),
      (∀ k, b x.1 ≤ b k → b k ≤ b y.1 → ∀ i, (T i).blockDiag' k = 0) →
      (b y.1 : ℕ) < (b x.1 : ℕ) + w.length → Kraus.evalWord T w x y = 0 := by
  intro w
  induction w with
  | nil =>
      intro x y _ h
      simp only [List.length_nil, Nat.add_zero] at h
      have hxy : x ≠ y := by
        rintro rfl
        exact absurd h (lt_irrefl _)
      simp [Kraus.evalWord, hxy]
  | cons i w' ih =>
      intro x y hdiag h
      simp only [List.length_cons] at h
      rcases lt_or_ge (b y.1) (b x.1) with hyx | hxy
      · exact blockTriangular_evalWord hT (i :: w') hyx
      simp only [Kraus.evalWord, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun z _ => ?_
      rcases lt_trichotomy (b z.1) (b x.1) with hzx | hzx | hzx
      · rw [hT i hzx, zero_mul]
      · obtain ⟨kz, jz⟩ := z
        obtain ⟨kx, jx⟩ := x
        obtain rfl : kz = kx := hb hzx
        have h0 := congrFun (congrFun (hdiag kz le_rfl hxy i) jx) jz
        rw [blockDiag'_apply, zero_apply] at h0
        rw [h0, zero_mul]
      · have hzx' : (b x.1 : ℕ) < (b z.1 : ℕ) := Fin.lt_def.mp hzx
        have hzy : (b y.1 : ℕ) < (b z.1 : ℕ) + w'.length := by omega
        rw [ih z y (fun k hk hk' => hdiag k (hzx.le.trans hk) hk') hzy, mul_zero]

end Matrix

end

section

open scoped Matrix

namespace Matrix

variable {o : Type*} [Fintype o] [DecidableEq o] {n : o → ℕ}

/-- The rows of `blockProj n k * X` are the rows of `X` at the coordinates of the block `k`. -/
theorem blockProj_mul_apply {m : Type*} (X : Matrix (Σ k, Fin (n k)) m ℂ) (k : o)
    (i : Fin (n k)) (y : m) : (blockProj n k * X) i y = X ⟨k, i⟩ y := by
  simp only [Matrix.mul_apply, blockProj, Matrix.transpose_apply]
  rw [Finset.sum_eq_single ⟨k, i⟩]
  · rw [blockEmbed_apply_fst_eq]
    simp
  · intro x _ hx
    rw [blockEmbed_apply_of_ne hx, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The columns of `X * blockEmbed n k` are the columns of `X` at the coordinates of the block
`k`. -/
theorem mul_blockEmbed_apply {m : Type*} (X : Matrix m (Σ k, Fin (n k)) ℂ) (k : o) (x : m)
    (j : Fin (n k)) : (X * blockEmbed n k) x j = X x ⟨k, j⟩ := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single ⟨k, j⟩]
  · rw [blockEmbed_apply_fst_eq]
    simp
  · intro y _ hy
    rw [blockEmbed_apply_of_ne hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The rows of `X` at the block `k`, expanded over the blocks of its columns. -/
theorem blockProj_mul_eq_sum_submatrix_mul_blockProj
    (X : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) (k : o) :
    blockProj n k * X = ∑ l, X.submatrix (Sigma.mk k) (Sigma.mk l) * blockProj n l := by
  ext i ⟨l, j⟩
  rw [blockProj_mul_apply, Matrix.sum_apply, Finset.sum_eq_single l]
  · simp [Matrix.mul_apply, blockProj, Matrix.transpose_apply, blockEmbed_apply_fst_eq]
  · intro l' _ hl'
    simp only [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun j' _ => by
      have h0 : blockProj n l' j' ⟨l, j⟩ = 0 := by
        simp only [blockProj, Matrix.transpose_apply]
        exact blockEmbed_apply_of_fst_ne (Ne.symm hl') j'
      rw [h0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The columns of `X` at the block `k`, expanded over the blocks of its rows. -/
theorem mul_blockEmbed_eq_sum_blockEmbed_mul_submatrix
    (X : Matrix (Σ k, Fin (n k)) (Σ k, Fin (n k)) ℂ) (k : o) :
    X * blockEmbed n k = ∑ l, blockEmbed n l * X.submatrix (Sigma.mk l) (Sigma.mk k) := by
  ext ⟨l, i⟩ j
  rw [mul_blockEmbed_apply, Matrix.sum_apply, Finset.sum_eq_single l]
  · simp [Matrix.mul_apply, blockEmbed_apply_fst_eq]
  · intro l' _ hl'
    simp only [Matrix.mul_apply]
    exact Finset.sum_eq_zero fun j' _ => by
      rw [blockEmbed_apply_of_fst_ne (x := ⟨l, i⟩) (Ne.symm hl') j', zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A square matrix that is a scalar multiple of the identity is the multiple by its normalized
trace. -/
theorem eq_trace_smul_one_of_exists_eq_smul_one {m : ℕ} {M : Matrix (Fin m) (Fin m) ℂ}
    (h : ∃ c : ℂ, M = c • 1) : M = ((m : ℂ)⁻¹ * M.trace) • 1 := by
  obtain ⟨c, rfl⟩ := h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · ext i
    exact i.elim0
  · have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    congr 1
    rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    field_simp

end Matrix

end

section

open scoped Matrix

namespace Matrix

variable {o : Type*} [Fintype o] [DecidableEq o] {n : o → ℕ}

/-- The coordinate blocks resolve the identity: `∑ k, blockEmbed n k * blockProj n k = 1`. -/
theorem sum_blockEmbed_mul_blockProj : ∑ k, blockEmbed n k * blockProj n k = 1 := by
  have h := sum_blockEmbed_mul_mul_blockProj (n := n) fun _ => 1
  simp only [Matrix.mul_one] at h
  rw [h]
  exact blockDiagonal'_one

/-- A block diagonal matrix maps the `k`-th coordinate block into itself by its `k`-th block. -/
theorem blockDiagonal'_mul_blockEmbed (M : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) (k : o) :
    blockDiagonal' M * blockEmbed n k = blockEmbed n k * M k := by
  rw [← sum_blockEmbed_mul_mul_blockProj, Matrix.sum_mul, Finset.sum_eq_single k]
  · rw [Matrix.mul_assoc, blockProj_mul_blockEmbed_self, Matrix.mul_one]
  · intro l _ hl
    rw [Matrix.mul_assoc, blockProj_mul_blockEmbed_of_ne hl, Matrix.mul_zero]
  · simp

/-- The `k`-th coordinate projection of a block diagonal matrix is its `k`-th block. -/
theorem blockProj_mul_blockDiagonal' (M : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℂ) (k : o) :
    blockProj n k * blockDiagonal' M = M k * blockProj n k := by
  rw [← sum_blockEmbed_mul_mul_blockProj, Matrix.mul_sum, Finset.sum_eq_single k]
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, blockProj_mul_blockEmbed_self, Matrix.one_mul]
  · intro l _ hl
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, blockProj_mul_blockEmbed_of_ne (Ne.symm hl),
      Matrix.zero_mul, Matrix.zero_mul]
  · simp

end Matrix

end
