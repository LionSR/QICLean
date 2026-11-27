/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.BipartiteCopies

/-!
Adapted from QICLean/Channel/Entanglement/SeparableOperationTensor.lean in the
nptent-operations worktree of QICLean (base commit
8b4c2e43f7df3a62977134e648834b39208b6117, uncommitted completed module;
source SHA-256: 8bd9a16b0931cb6c37bb704ca6b0ace75acc9b33d2cde933dae5c04b927faffe).
The original copyright and authorship are retained. Curation updates documentation
and imports for the foundations branch; no recurrence purification or operational
rate equivalence is added.

# Tensor powers, coordinate reindexing, and binary tree iteration of separable operations

This module provides compositional combinators for finite product-Kraus
`QuantumInfo.SeparableOperation` acting on party-major tensor copies
`QuantumInfo.bipartiteCopies`:

* `QuantumInfo.SeparableOperation.reindex` — reindexing input and output local coordinates
  along equivalences.
* `QuantumInfo.SeparableOperation.tensorCopies` — `n`-fold parallel tensor power of a
  `SeparableOperation` with index type `Fin n → S.Index` and local operators
  `Matrix.piKronecker`, mapping `bipartiteCopies n ρ` to `bipartiteCopies n (S.map ρ)`.
* `QuantumInfo.flattenCopiesEquiv` and `QuantumInfo.SeparableOperation.flattenTensorCopies` —
  regrouping `m * n` copies into `m` blocks of `n` copies via `finProdFinEquiv`.
* `QuantumInfo.SeparableOperation.iterBinary` — iterating any 2-to-1 `SeparableOperation`
  in a balanced binary tree on `2 ^ n` copies.
-/

open Matrix Finset
open scoped BigOperators Kronecker

namespace QuantumInfo

/-! ## Section 1: Coordinate reindexing of separable operations -/

namespace SeparableOperation

section Reindex

variable {A B Aout Bout A' B' Aout' Bout' : Type}

/-- Reindex the local input and output coordinates of a `SeparableOperation` along
equivalences `eA, eB, eAout, eBout`. -/
def reindex (S : SeparableOperation A B Aout Bout)
    (eA : A' ≃ A) (eB : B' ≃ B) (eAout : Aout' ≃ Aout) (eBout : Bout' ≃ Bout) :
    SeparableOperation A' B' Aout' Bout' where
  Index := S.Index
  left i := (S.left i).submatrix eAout eA
  right i := (S.right i).submatrix eBout eB

/-- Action of a reindexed `SeparableOperation` on an arbitrary bipartite matrix. -/
theorem map_reindex [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (S : SeparableOperation A B Aout Bout)
    (eA : A' ≃ A) (eB : B' ≃ B) (eAout : Aout' ≃ Aout) (eBout : Bout' ≃ Bout)
    (ρ : Matrix (A' × B') (A' × B') ℂ) :
    (S.reindex eA eB eAout eBout).map ρ =
      (S.map (ρ.submatrix (Equiv.prodCongr eA.symm eB.symm)
          (Equiv.prodCongr eA.symm eB.symm))).submatrix
        (Equiv.prodCongr eAout eBout) (Equiv.prodCongr eAout eBout) := by
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [map_apply, reindex, Matrix.sum_apply, Matrix.submatrix_apply, Equiv.prodCongr_apply,
    Prod.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.submatrix_apply]
  let eIn : (A' × B') ≃ (A × B) := Equiv.prodCongr eA eB
  refine Fintype.sum_equiv eIn _ _ fun q => ?_
  rcases q with ⟨q₁, q₂⟩
  congr 1
  refine Fintype.sum_equiv eIn _ _ fun p => ?_
  rcases p with ⟨p₁, p₂⟩
  simp [eIn]

/-- Action of a reindexed `SeparableOperation` on a submatrix-reindexed input `σ`. -/
theorem map_reindex_submatrix [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
    (S : SeparableOperation A B Aout Bout)
    (eA : A' ≃ A) (eB : B' ≃ B) (eAout : Aout' ≃ Aout) (eBout : Bout' ≃ Bout)
    (σ : Matrix (A × B) (A × B) ℂ) :
    (S.reindex eA eB eAout eBout).map
        (σ.submatrix (Equiv.prodCongr eA eB) (Equiv.prodCongr eA eB)) =
      (S.map σ).submatrix (Equiv.prodCongr eAout eBout) (Equiv.prodCongr eAout eBout) := by
  rw [map_reindex]
  have hsub :
      (σ.submatrix (Equiv.prodCongr eA eB) (Equiv.prodCongr eA eB)).submatrix
          (Equiv.prodCongr eA.symm eB.symm) (Equiv.prodCongr eA.symm eB.symm) = σ := by
    ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    simp
  rw [hsub]

end Reindex

/-! ## Section 2: Parallel tensor power of a separable operation -/

section TensorCopies

variable {A B Aout Bout : Type}

/-- `n`-fold parallel tensor power of a `SeparableOperation`, acting independently on each
copy with shared outcome tuple `Fin n → S.Index` and local `Matrix.piKronecker` operators. -/
def tensorCopies (n : ℕ) (S : SeparableOperation A B Aout Bout) :
    SeparableOperation (Fin n → A) (Fin n → B) (Fin n → Aout) (Fin n → Bout) where
  Index := Fin n → S.Index
  left α := Matrix.piKronecker (fun k : Fin n => S.left (α k))
  right α := Matrix.piKronecker (fun k : Fin n => S.right (α k))

/-- Applying `S.tensorCopies n` to `bipartiteCopies n ρ` produces `bipartiteCopies n (S.map ρ)`. -/
theorem map_tensorCopies_bipartiteCopies
    [Fintype A] [Fintype B]
    (n : ℕ) (S : SeparableOperation A B Aout Bout)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    (S.tensorCopies n).map (bipartiteCopies n ρ) = bipartiteCopies n (S.map ρ) := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  rw [map_apply, Matrix.sum_apply, bipartiteCopies_apply]
  have hbranch : ∀ α : Fin n → S.Index,
      ((Matrix.piKronecker (fun k : Fin n => S.left (α k)) ⊗ₖ
          Matrix.piKronecker (fun k : Fin n => S.right (α k))) *
        bipartiteCopies n ρ *
        (Matrix.piKronecker (fun k : Fin n => S.left (α k)) ⊗ₖ
          Matrix.piKronecker (fun k : Fin n => S.right (α k)))ᴴ) (xA, xB) (yA, yB) =
      ∏ k : Fin n,
        ((S.left (α k) ⊗ₖ S.right (α k)) * ρ * (S.left (α k) ⊗ₖ S.right (α k))ᴴ)
          (xA k, xB k) (yA k, yB k) := by
    intro α
    let F : (k : Fin n) → ((A × B) × (A × B)) → ℂ := fun k pq =>
      S.left (α k) (xA k) pq.1.1 * S.right (α k) (xB k) pq.1.2 *
        ρ pq.1 pq.2 *
        star (S.left (α k) (yA k) pq.2.1 * S.right (α k) (yB k) pq.2.2)
    have hrhs :
        (∏ k : Fin n,
          ((S.left (α k) ⊗ₖ S.right (α k)) * ρ * (S.left (α k) ⊗ₖ S.right (α k))ᴴ)
            (xA k, xB k) (yA k, yB k)) =
        ∑ p : Fin n → (A × B) × (A × B), ∏ k : Fin n, F k (p k) := by
      rw [← Fintype.prod_sum F]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Fintype.sum_prod_type (F k)]
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
        Finset.sum_mul, F]
      rw [Finset.sum_comm]
    rw [hrhs]
    let e : (((Fin n → A) × (Fin n → B)) × ((Fin n → A) × (Fin n → B))) ≃
        (Fin n → (A × B) × (A × B)) :=
      { toFun := fun q k => ((q.1.1 k, q.1.2 k), (q.2.1 k, q.2.2 k))
        invFun := fun p => ((fun k => (p k).1.1, fun k => (p k).1.2),
                            (fun k => (p k).2.1, fun k => (p k).2.2))
        left_inv := fun ⟨⟨a₁, b₁⟩, ⟨a₂, b₂⟩⟩ => rfl
        right_inv := fun p => rfl }
    rw [← Fintype.sum_equiv e (fun q => ∏ k : Fin n, F k (e q k))
      (fun p => ∏ k : Fin n, F k (p k)) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
      Matrix.piKronecker_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rcases p with ⟨pA, pB⟩
    rcases q with ⟨qA, qB⟩
    simp only [bipartiteCopies_apply, F, e, Equiv.coe_fn_mk, star_mul', star_prod,
      ← Finset.prod_mul_distrib]
  change (∑ α : Fin n → S.Index,
      ((Matrix.piKronecker (fun k : Fin n => S.left (α k)) ⊗ₖ
          Matrix.piKronecker (fun k : Fin n => S.right (α k))) *
        bipartiteCopies n ρ *
        (Matrix.piKronecker (fun k : Fin n => S.left (α k)) ⊗ₖ
          Matrix.piKronecker (fun k : Fin n => S.right (α k)))ᴴ) (xA, xB) (yA, yB)) = _
  simp_rw [hbranch]
  rw [← Fintype.prod_sum (fun (k : Fin n) (i : S.Index) =>
    ((S.left i ⊗ₖ S.right i) * ρ * (S.left i ⊗ₖ S.right i)ᴴ) (xA k, xB k) (yA k, yB k))]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_apply, Matrix.sum_apply]

end TensorCopies

end SeparableOperation

/-! ## Section 3: Copy regrouping, flattening, and binary-tree iteration -/

section CopyRegrouping

/-- Coordinate equivalence casting the copy index along `h : m = n`. -/
def castCopiesEquiv {m n : ℕ} (h : m = n) (X : Type) : (Fin m → X) ≃ (Fin n → X) :=
  Equiv.arrowCongr (finCongr h) (Equiv.refl X)

/-- Casting copy count along `h : m = n` identifies `bipartiteCopies m ρ` with the
submatrix of `bipartiteCopies n ρ`. -/
theorem bipartiteCopies_cast_eq_submatrix {A B : Type} {m n : ℕ} (h : m = n)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    bipartiteCopies m ρ =
      (bipartiteCopies n ρ).submatrix
        (Equiv.prodCongr (castCopiesEquiv h A) (castCopiesEquiv h B))
        (Equiv.prodCongr (castCopiesEquiv h A) (castCopiesEquiv h B)) := by
  subst h
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp [castCopiesEquiv]

/-- Equivalence regrouping `m * n` copies into `m` blocks of `n` copies via `finProdFinEquiv`. -/
def flattenCopiesEquiv (m n : ℕ) (X : Type) :
    (Fin (m * n) → X) ≃ (Fin m → Fin n → X) where
  toFun f i j := f (finProdFinEquiv (i, j))
  invFun g k := g (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv f := by
    funext k
    exact congrArg f (finProdFinEquiv.apply_symm_apply k)
  right_inv g := by
    funext i j
    simp

/-- `bipartiteCopies (m * n) ρ` equals `bipartiteCopies m (bipartiteCopies n ρ)`
reindexed along `flattenCopiesEquiv m n`. -/
theorem bipartiteCopies_mul_eq_submatrix {A B : Type} (m n : ℕ)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    bipartiteCopies (m * n) ρ =
      (bipartiteCopies m (bipartiteCopies n ρ)).submatrix
        (Equiv.prodCongr (flattenCopiesEquiv m n A) (flattenCopiesEquiv m n B))
        (Equiv.prodCongr (flattenCopiesEquiv m n A) (flattenCopiesEquiv m n B)) := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp only [bipartiteCopies_apply, Matrix.submatrix_apply, Equiv.prodCongr_apply,
    Prod.map_apply, flattenCopiesEquiv, Equiv.coe_fn_mk]
  rw [← finProdFinEquiv.prod_comp (fun k : Fin (m * n) => ρ (xA k, xB k) (yA k, yB k))]
  exact Fintype.prod_prod_type _

/-- `bipartiteCopies 1 ρ` equals `ρ` reindexed along `Equiv.funUnique (Fin 1)`. -/
theorem bipartiteCopies_one_eq_submatrix {A B : Type} (ρ : Matrix (A × B) (A × B) ℂ) :
    bipartiteCopies 1 ρ =
      ρ.submatrix
        (Equiv.prodCongr (Equiv.funUnique (Fin 1) A) (Equiv.funUnique (Fin 1) B))
        (Equiv.prodCongr (Equiv.funUnique (Fin 1) A) (Equiv.funUnique (Fin 1) B)) := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp [bipartiteCopies_apply]

end CopyRegrouping

namespace SeparableOperation

/-- Flattened `m`-fold tensor power of an `n`-copy separable operation `S`, acting on
`m * n` copies and producing `m` output copies. -/
def flattenTensorCopies {A B Aout Bout : Type} (m n : ℕ)
    (S : SeparableOperation (Fin n → A) (Fin n → B) Aout Bout) :
    SeparableOperation (Fin (m * n) → A) (Fin (m * n) → B) (Fin m → Aout) (Fin m → Bout) :=
  (S.tensorCopies m).reindex (flattenCopiesEquiv m n A) (flattenCopiesEquiv m n B)
    (Equiv.refl _) (Equiv.refl _)

/-- `S.flattenTensorCopies m n` maps `bipartiteCopies (m * n) ρ` to
`bipartiteCopies m (S.map (bipartiteCopies n ρ))`. -/
theorem map_flattenTensorCopies_bipartiteCopies
    {A B Aout Bout : Type} [Fintype A] [Fintype B]
    (m n : ℕ) (S : SeparableOperation (Fin n → A) (Fin n → B) Aout Bout)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    (S.flattenTensorCopies m n).map (bipartiteCopies (m * n) ρ) =
      bipartiteCopies m (S.map (bipartiteCopies n ρ)) := by
  rw [bipartiteCopies_mul_eq_submatrix m n ρ, flattenTensorCopies, map_reindex_submatrix,
    map_tensorCopies_bipartiteCopies]
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp

/-- Identity separable operation from 1 copy `(Fin 1 → A) × (Fin 1 → B)` to `A × B`. -/
def fromSingleCopy (A B : Type) [DecidableEq A] [DecidableEq B] :
    SeparableOperation (Fin 1 → A) (Fin 1 → B) A B :=
  (SeparableOperation.id A B).reindex
    (Equiv.funUnique (Fin 1) A) (Equiv.funUnique (Fin 1) B)
    (Equiv.refl A) (Equiv.refl B)

/-- `fromSingleCopy A B` maps `bipartiteCopies 1 ρ` back to `ρ`. -/
theorem map_fromSingleCopy_bipartiteCopies {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) :
    (fromSingleCopy A B).map (bipartiteCopies 1 ρ) = ρ := by
  rw [bipartiteCopies_one_eq_submatrix ρ, fromSingleCopy, map_reindex_submatrix, map_id]
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp

/-- Balanced binary-tree iteration of a 2-to-1 separable operation `step` on `2 ^ n` copies. -/
def iterBinary {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (step : SeparableOperation (Fin 2 → A) (Fin 2 → B) A B) :
    (n : ℕ) → SeparableOperation (Fin (2 ^ n) → A) (Fin (2 ^ n) → B) A B
  | 0 => fromSingleCopy A B
  | n + 1 =>
    step.comp
      (((iterBinary step n).flattenTensorCopies 2 (2 ^ n)).reindex
        (castCopiesEquiv (pow_succ' 2 n) A)
        (castCopiesEquiv (pow_succ' 2 n) B)
        (Equiv.refl _) (Equiv.refl _))

/-- Base case of `iterBinary`: 0 rounds on `2 ^ 0 = 1` copy returns `ρ`. -/
theorem map_iterBinary_zero {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (step : SeparableOperation (Fin 2 → A) (Fin 2 → B) A B)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    (iterBinary step 0).map (bipartiteCopies (2 ^ 0) ρ) = ρ :=
  map_fromSingleCopy_bipartiteCopies ρ

/-- Inductive step of `iterBinary`: `n + 1` rounds on `2 ^ (n + 1)` copies equals applying
`step` to 2 copies of the `n`-round output. -/
theorem map_iterBinary_succ {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (step : SeparableOperation (Fin 2 → A) (Fin 2 → B) A B)
    (n : ℕ) (ρ : Matrix (A × B) (A × B) ℂ) :
    (iterBinary step (n + 1)).map (bipartiteCopies (2 ^ (n + 1)) ρ) =
      step.map (bipartiteCopies 2 ((iterBinary step n).map (bipartiteCopies (2 ^ n) ρ))) := by
  rw [iterBinary, map_comp, bipartiteCopies_cast_eq_submatrix (pow_succ' 2 n) ρ,
    map_reindex_submatrix, map_flattenTensorCopies_bipartiteCopies]
  rfl

end SeparableOperation

end QuantumInfo
