/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Algebra.BigOperators.Fin

/-!
# Block and orbit positive-semidefiniteness reduction

This file provides elementary, ring-polymorphic reduction lemmas for proving
positive semidefiniteness of a finite matrix that decomposes into blocks along
the fibers of a key map and whose fiber blocks are transported by explicit
equivalences to a smaller family of canonical representative matrices.

## Main results

- `Matrix.posSemidef_blockDiagonal'_iff`: a finite dependent block-diagonal matrix
  over an ordered star ring is positive semidefinite iff every diagonal block is.
- `Matrix.posSemidef_blockDiagonal_iff`: the non-dependent block-diagonal version.
- `Matrix.posSemidef_reindex_iff`: simultaneous reindexing preserves positive
  semidefiniteness.
- `Matrix.submatrix_sigmaFiberEquiv_eq_blockDiagonal'`: a matrix vanishing outside
  the fibers of `key : α → κ` becomes a dependent block-diagonal matrix under
  `Equiv.sigmaFiberEquiv key`.
- `Matrix.posSemidef_iff_forall_fiberBlock`: positive semidefiniteness of a
  fiber-supported matrix is equivalent to positive semidefiniteness of every fiber block.
- `Matrix.posSemidef_of_fiber_transport`: if every fiber block of a fiber-supported
  matrix is transported by an explicit equivalence to a positive-semidefinite
  representative matrix, the global matrix is positive semidefinite.
- `Matrix.posSemidef_of_global_orbit_transport`: specialization where fiber
  equivalences are induced by global index permutations preserving the matrix.
- `Matrix.posSemidef_of_mul_blockDiagonal'_conjTranspose`: positive semidefiniteness
  from an explicit block-diagonal congruence `V * blockDiagonal' B * Vᴴ`.
-/

open scoped Matrix BigOperators

namespace Matrix

section BlockDiagonal

/-- Simultaneous reindexing preserves positive semidefiniteness. -/
theorem posSemidef_reindex_iff {m n R : Type*} [Ring R] [PartialOrder R] [StarRing R]
    (e : m ≃ n) (M : Matrix m m R) :
    (Matrix.reindex e e M).PosSemidef ↔ M.PosSemidef := by
  simp [Matrix.reindex_apply]

/-- A dependent block-diagonal matrix is Hermitian iff every diagonal block is Hermitian. -/
theorem isHermitian_blockDiagonal'_iff' {ι R : Type*} [DecidableEq ι]
    [Ring R] [StarRing R] {m : ι → Type*}
    (B : ∀ k, Matrix (m k) (m k) R) :
    (Matrix.blockDiagonal' B).IsHermitian ↔ ∀ k, (B k).IsHermitian := by
  constructor
  · intro h k
    ext a b
    have hk := congrFun (congrFun h ⟨k, a⟩) ⟨k, b⟩
    simpa [Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply_eq] using hk
  · intro h
    ext ⟨k, a⟩ ⟨l, b⟩
    by_cases hkl : k = l
    · subst hkl
      have hk := congrFun (congrFun (h k) a) b
      simpa [Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply_eq] using hk
    · have hlk : l ≠ k := Ne.symm hkl
      simp [Matrix.conjTranspose_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hkl,
        Matrix.blockDiagonal'_apply_ne _ _ _ hlk]

/-- The quadratic form of a dependent block-diagonal matrix splits as the sum of the
quadratic forms of its diagonal blocks. -/
theorem dotProduct_mulVec_blockDiagonal' {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [StarRing R] {m : ι → Type*} [∀ k, Fintype (m k)]
    (B : ∀ k, Matrix (m k) (m k) R) (x : (Σ k, m k) → R) :
    star x ⬝ᵥ (Matrix.blockDiagonal' B).mulVec x =
      ∑ k : ι, star (fun a : m k ↦ x ⟨k, a⟩) ⬝ᵥ (B k).mulVec (fun a : m k ↦ x ⟨k, a⟩) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 1
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    simp [Matrix.blockDiagonal'_apply_eq]
  · intro l _ hlk
    apply Finset.sum_eq_zero
    intro b _
    have hkl : k ≠ l := Ne.symm hlk
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ hkl]
  · intro hk
    exact (hk (Finset.mem_univ k)).elim

/-- A finite dependent block-diagonal matrix over an ordered star ring is positive
semidefinite iff every diagonal block is positive semidefinite. -/
theorem posSemidef_blockDiagonal'_iff {ι R : Type*} [Finite ι] [DecidableEq ι]
    [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    {m : ι → Type*} [∀ k, Finite (m k)]
    (B : ∀ k, Matrix (m k) (m k) R) :
    (Matrix.blockDiagonal' B).PosSemidef ↔ ∀ k, (B k).PosSemidef := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ (k : ι) : Fintype (m k) := Fintype.ofFinite (m k)
  constructor
  · intro hB k
    have hsub : (Matrix.blockDiagonal' B).submatrix
        (fun a : m k ↦ (⟨k, a⟩ : Σ l, m l))
        (fun a : m k ↦ (⟨k, a⟩ : Σ l, m l)) = B k := by
      ext a b
      simp [Matrix.blockDiagonal'_apply_eq]
    rw [← hsub]
    exact hB.submatrix (fun a : m k ↦ (⟨k, a⟩ : Σ l, m l))
  · intro hB
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((isHermitian_blockDiagonal'_iff' B).mpr fun k ↦ (hB k).isHermitian) ?_
    intro x
    rw [dotProduct_mulVec_blockDiagonal']
    exact Finset.sum_nonneg fun k _ ↦ (hB k).dotProduct_mulVec_nonneg (fun a ↦ x ⟨k, a⟩)

/-- A finite non-dependent block-diagonal matrix over an ordered star ring is positive
semidefinite iff every diagonal block is positive semidefinite. -/
theorem posSemidef_blockDiagonal_iff {ι m R : Type*} [Finite ι] [DecidableEq ι]
    [Finite m] [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    (B : ι → Matrix m m R) :
    (Matrix.blockDiagonal B).PosSemidef ↔ ∀ k, (B k).PosSemidef := by
  let e : (Σ _ : ι, m) ≃ (m × ι) :=
    (Equiv.sigmaEquivProd ι m).trans (Equiv.prodComm ι m)
  have hsub : (Matrix.blockDiagonal B).submatrix e e = Matrix.blockDiagonal' B := by
    ext ⟨k, a⟩ ⟨l, b⟩
    by_cases hkl : k = l
    · subst hkl
      simp [e, Matrix.blockDiagonal_apply, Matrix.blockDiagonal'_apply_eq]
    · simp [e, Matrix.blockDiagonal_apply, Matrix.blockDiagonal'_apply_ne _ _ _ hkl, hkl]
  rw [← Matrix.posSemidef_submatrix_equiv e, hsub, posSemidef_blockDiagonal'_iff]

end BlockDiagonal

section FiberBlocks

variable {α κ R : Type*}

/-- The principal submatrix of `M` restricted to the fiber `{i : α // key i = k}`. -/
def fiberBlock (key : α → κ) (M : Matrix α α R) (k : κ) :
    Matrix {i : α // key i = k} {i : α // key i = k} R :=
  M.submatrix Subtype.val Subtype.val

@[simp]
theorem fiberBlock_apply (key : α → κ) (M : Matrix α α R) (k : κ)
    (a b : {i : α // key i = k}) :
    fiberBlock key M k a b = M a.1 b.1 :=
  rfl

/-- If `M` vanishes whenever `key i ≠ key j`, then pulling `M` back along
`Equiv.sigmaFiberEquiv key` yields the dependent block-diagonal matrix of its fiber blocks. -/
theorem submatrix_sigmaFiberEquiv_eq_blockDiagonal'
    [DecidableEq κ] [Zero R] (key : α → κ) (M : Matrix α α R)
    (hsupp : ∀ i j, key i ≠ key j → M i j = 0) :
    M.submatrix (Equiv.sigmaFiberEquiv key) (Equiv.sigmaFiberEquiv key) =
      Matrix.blockDiagonal' (fiberBlock key M) := by
  ext ⟨k, a⟩ ⟨l, b⟩
  by_cases hkl : k = l
  · subst hkl
    simp [fiberBlock, Matrix.blockDiagonal'_apply_eq]
  · have hne : key a.1 ≠ key b.1 := by
      rw [a.2, b.2]
      exact hkl
    simp [Matrix.blockDiagonal'_apply_ne _ _ _ hkl, hsupp a.1 b.1 hne]

/-- Reindexing a fiber-supported matrix by `(Equiv.sigmaFiberEquiv key).symm` yields
the dependent block-diagonal matrix of its fiber blocks. -/
theorem reindex_sigmaFiberEquiv_symm_eq_blockDiagonal'
    [DecidableEq κ] [Zero R] (key : α → κ) (M : Matrix α α R)
    (hsupp : ∀ i j, key i ≠ key j → M i j = 0) :
    Matrix.reindex (Equiv.sigmaFiberEquiv key).symm (Equiv.sigmaFiberEquiv key).symm M =
      Matrix.blockDiagonal' (fiberBlock key M) := by
  simpa [Matrix.reindex_apply] using submatrix_sigmaFiberEquiv_eq_blockDiagonal' key M hsupp

/-- A matrix supported inside the fibers of a finite key map is positive semidefinite
iff every fiber block is positive semidefinite. -/
theorem posSemidef_iff_forall_fiberBlock
    [Finite α] [Finite κ]
    [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    (key : α → κ) (M : Matrix α α R)
    (hsupp : ∀ i j, key i ≠ key j → M i j = 0) :
    M.PosSemidef ↔ ∀ k : κ, (fiberBlock key M k).PosSemidef := by
  classical
  rw [← Matrix.posSemidef_submatrix_equiv (Equiv.sigmaFiberEquiv key),
    submatrix_sigmaFiberEquiv_eq_blockDiagonal' key M hsupp,
    posSemidef_blockDiagonal'_iff]

/-- If `M` vanishes outside the fibers of `key : α → κ` and each fiber block is
transported entrywise by an explicit equivalence `transport k` to a representative
matrix `rep (repIdx k)`, then `M` is positive semidefinite iff every reached
representative matrix is positive semidefinite. -/
theorem posSemidef_iff_forall_fiber_transport
    {τ : Type*} [Finite α] [Finite κ]
    [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    (key : α → κ) (M : Matrix α α R)
    (hsupp : ∀ i j, key i ≠ key j → M i j = 0)
    (repIdx : κ → τ) (repDim : τ → Type*)
    (rep : ∀ t, Matrix (repDim t) (repDim t) R)
    (transport : ∀ k : κ, {i : α // key i = k} ≃ repDim (repIdx k))
    (htransport : ∀ k (a b : {i : α // key i = k}),
      M a.1 b.1 = rep (repIdx k) (transport k a) (transport k b)) :
    M.PosSemidef ↔ ∀ k : κ, (rep (repIdx k)).PosSemidef := by
  rw [posSemidef_iff_forall_fiberBlock key M hsupp]
  refine forall_congr' fun k ↦ ?_
  have hblk : fiberBlock key M k = (rep (repIdx k)).submatrix (transport k) (transport k) := by
    ext a b
    exact htransport k a b
  rw [hblk, Matrix.posSemidef_submatrix_equiv]

/-- Generic block/orbit PSD reduction: if `M` has entries only inside fibers of a
finite key map `key : α → κ` and each fiber is transported by an explicit equivalence
to one of a family of positive-semidefinite representative matrices `rep t`, then `M`
is positive semidefinite globally. -/
theorem posSemidef_of_fiber_transport
    {τ : Type*} [Finite α] [Finite κ]
    [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    (key : α → κ) (M : Matrix α α R)
    (hsupp : ∀ i j, key i ≠ key j → M i j = 0)
    (repIdx : κ → τ) (repDim : τ → Type*)
    (rep : ∀ t, Matrix (repDim t) (repDim t) R)
    (transport : ∀ k : κ, {i : α // key i = k} ≃ repDim (repIdx k))
    (htransport : ∀ k (a b : {i : α // key i = k}),
      M a.1 b.1 = rep (repIdx k) (transport k a) (transport k b))
    (hrep : ∀ t : τ, (rep t).PosSemidef) :
    M.PosSemidef :=
  (posSemidef_iff_forall_fiber_transport key M hsupp repIdx repDim rep transport htransport).mpr
    fun k ↦ hrep (repIdx k)

/-- Restrict a global index equivalence `g : α ≃ α` to an equivalence between two
fibers of `key : α → κ`. -/
def fiberEquivOfGlobalEquiv (key : α → κ) {k k' : κ} (g : α ≃ α)
    (hg : ∀ i : α, key (g i) = k' ↔ key i = k) :
    {i : α // key i = k} ≃ {i : α // key i = k'} where
  toFun a := ⟨g a.1, (hg a.1).mpr a.2⟩
  invFun b := ⟨g.symm b.1, (hg (g.symm b.1)).mp (by simpa using b.2)⟩
  left_inv a := Subtype.ext (g.symm_apply_apply a.1)
  right_inv b := Subtype.ext (g.apply_symm_apply b.1)

@[simp]
theorem fiberEquivOfGlobalEquiv_apply (key : α → κ) {k k' : κ} (g : α ≃ α)
    (hg : ∀ i : α, key (g i) = k' ↔ key i = k) (a : {i : α // key i = k}) :
    (fiberEquivOfGlobalEquiv key g hg a).1 = g a.1 :=
  rfl

/-- Orbit PSD reduction from global index symmetries: if `M` is supported inside
fibers of `key : α → κ`, each fiber `k` is mapped onto a canonical fiber
`canonKey (repIdx k)` by a global equivalence `g k : α ≃ α` that preserves the
entries of `M` on that fiber, and each canonical fiber block is positive
semidefinite, then `M` is positive semidefinite. -/
theorem posSemidef_of_global_orbit_transport
    {τ : Type*} [Finite α] [Finite κ]
    [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    (key : α → κ) (M : Matrix α α R)
    (hsupp : ∀ i j, key i ≠ key j → M i j = 0)
    (repIdx : κ → τ) (canonKey : τ → κ)
    (g : κ → (α ≃ α))
    (hg_fiber : ∀ k i, key (g k i) = canonKey (repIdx k) ↔ key i = k)
    (hg_inv : ∀ k i j, key i = k → key j = k → M i j = M (g k i) (g k j))
    (hrep : ∀ t : τ, (fiberBlock key M (canonKey t)).PosSemidef) :
    M.PosSemidef := by
  refine posSemidef_of_fiber_transport key M hsupp repIdx
    (fun t ↦ {i : α // key i = canonKey t})
    (fun t ↦ fiberBlock key M (canonKey t))
    (fun k ↦ fiberEquivOfGlobalEquiv key (g k) (hg_fiber k))
    (fun k a b ↦ ?_) hrep
  exact hg_inv k a.1 b.1 a.2 b.2

end FiberBlocks

section Congruence

/-- If a matrix factors as a congruence `V * blockDiagonal' B * Vᴴ` of a finite
dependent block-diagonal matrix whose blocks are positive semidefinite, then it is
positive semidefinite. -/
theorem posSemidef_of_mul_blockDiagonal'_conjTranspose
    {ι n R : Type*} [Fintype ι] [DecidableEq ι] [Finite n]
    {m : ι → Type*} [∀ k, Fintype (m k)]
    [CommRing R] [PartialOrder R] [StarRing R] [AddLeftMono R]
    (B : ∀ k, Matrix (m k) (m k) R)
    (V : Matrix n (Σ k, m k) R)
    (hB : ∀ k, (B k).PosSemidef) :
    (V * Matrix.blockDiagonal' B * Vᴴ).PosSemidef :=
  ((posSemidef_blockDiagonal'_iff B).mpr hB).mul_mul_conjTranspose_same V

end Congruence

end Matrix
