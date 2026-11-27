/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity
import QICLean.Algebra.Kronecker.MaximallyEntangled
import QICLean.Algebra.Kronecker.PiKronecker
import QICLean.Algebra.PartialTrace
import QICLean.Channel.Dilation.KrausFamilyTraceNorm
import QICLean.Channel.Entanglement.SeparableOperation
import QICLean.Channel.KrausMap.KrausFamilyProd

/-!
# Party-major bipartite tensor copies and local copy discard

This module defines party-major `n`-copy bipartite operators `bipartiteCopies n ρ` on
`(Fin n → A) × (Fin n → B)` via `Matrix.piKronecker` and `Equiv.arrowProdEquivProdArrow`,
the `k`-ebit target state `bellPairTarget k = bipartiteCopies k (Matrix.omegaProj 2)`,
and the trace-preserving product-Kraus local discard operation `keepCopySepOp` that retains
a single copy `i₀ : Fin k` on both parties and locally traces out all remaining copies.

## Main definitions

* `QuantumInfo.bipartiteCopies` — party-major `n`-copy tensor power of a bipartite operator.
* `QuantumInfo.bellPairTarget` — party-major `k`-copy Bell-pair target `(|Ω₂⟩⟨Ω₂|)^{⊗ k}`.
* `QuantumInfo.splitCopyEquiv` — coordinate equivalence separating copy `i₀ : Fin k` from
  the remaining copies `{j : Fin k // j ≠ i₀}`.
* `QuantumInfo.keepCopyKraus` — local trace-preserving Kraus family keeping copy `i₀`.
* `QuantumInfo.keepCopySepOp` — bipartite trace-preserving product-Kraus `SeparableOperation`
  keeping copy `i₀` on both parties and locally discarding all other copies.
* `QuantumInfo.keepFirstBellPair` — specialization of `keepCopySepOp` keeping the first
  Bell pair out of `k ≥ 1` pairs.

## Main results

* `QuantumInfo.trace_bipartiteCopies`, `QuantumInfo.bipartiteCopies_posSemidef`,
  `QuantumInfo.bipartiteCopies_kronecker`, `QuantumInfo.trace_bellPairTarget`.
* `QuantumInfo.isTP_keepCopySepOp` — local copy discard is trace-preserving.
* `QuantumInfo.rectangularTraceNorm_keepCopySepOp_map_le` — local copy discard contracts
  `Matrix.rectangularTraceNorm`.
* `QuantumInfo.keepCopySepOp_map_bipartiteCopies` — discarding all copies except `i₀` sends
  `bipartiteCopies k ρ` to `ρ.trace ^ (k - 1) • ρ`.
* `QuantumInfo.keepCopySepOp_map_bellPairTarget` — keeping copy `i₀` sends `bellPairTarget k`
  to `Matrix.omegaProj 2`.
* `QuantumInfo.rectangularTraceNorm_keepCopySepOp_sub_omegaProj_le` — keeping copy `i₀`
  does not increase the full trace-norm distance from the Bell target.
-/

open Matrix
open scoped BigOperators Kronecker ComplexOrder

namespace QuantumInfo

section BipartiteCopies

variable {A B : Type}

/-- The party-major `n`-copy tensor power of a bipartite matrix `ρ`, acting on
`(Fin n → A) × (Fin n → B)`. It is obtained from the copy-major tensor power
`Matrix.piKronecker (fun _ : Fin n ↦ ρ)` by regrouping along `Equiv.arrowProdEquivProdArrow`. -/
def bipartiteCopies (n : ℕ) (ρ : Matrix (A × B) (A × B) ℂ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  (Matrix.piKronecker (fun _ : Fin n ↦ ρ)).submatrix
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ A) (fun _ ↦ B)).symm
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ ↦ A) (fun _ ↦ B)).symm

@[simp]
theorem bipartiteCopies_apply (n : ℕ) (ρ : Matrix (A × B) (A × B) ℂ)
    (xA yA : Fin n → A) (xB yB : Fin n → B) :
    bipartiteCopies n ρ (xA, xB) (yA, yB) = ∏ i : Fin n, ρ (xA i, xB i) (yA i, yB i) :=
  rfl

/-- The party-major `n`-copy tensor power of a product matrix `ρA ⊗ₖ ρB` is the Kronecker
product of the two party-local tensor powers. -/
theorem bipartiteCopies_kronecker (n : ℕ) (ρA : Matrix A A ℂ) (ρB : Matrix B B ℂ) :
    bipartiteCopies n (ρA ⊗ₖ ρB) =
      Matrix.piKronecker (fun _ : Fin n ↦ ρA) ⊗ₖ Matrix.piKronecker (fun _ : Fin n ↦ ρB) := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp [bipartiteCopies_apply, Matrix.kroneckerMap_apply, Finset.prod_mul_distrib]

/-- Conjugate transpose commutes with `bipartiteCopies`. -/
theorem conjTranspose_bipartiteCopies (n : ℕ) (ρ : Matrix (A × B) (A × B) ℂ) :
    (bipartiteCopies n ρ)ᴴ = bipartiteCopies n ρᴴ := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp [bipartiteCopies_apply, Matrix.conjTranspose_apply]

/-- The trace of `n` party-major copies of `ρ` is `ρ.trace ^ n`. -/
theorem trace_bipartiteCopies [Fintype A] [Fintype B] (n : ℕ)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    (bipartiteCopies n ρ).trace = ρ.trace ^ n := by
  rw [bipartiteCopies, Matrix.trace_submatrix_equiv, Matrix.trace_piKronecker]
  simp

/-- If `ρ` has trace `1`, then `bipartiteCopies n ρ` has trace `1`. -/
theorem trace_bipartiteCopies_eq_one [Fintype A] [Fintype B] (n : ℕ)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.trace = 1) :
    (bipartiteCopies n ρ).trace = 1 := by
  rw [trace_bipartiteCopies, hρ, one_pow]

/-- Party-major copies of a positive semidefinite matrix are positive semidefinite. -/
theorem bipartiteCopies_posSemidef [Finite A] [Finite B] (n : ℕ)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) :
    (bipartiteCopies n ρ).PosSemidef := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  exact (Matrix.piKronecker_posSemidef (fun _ : Fin n ↦ ρ) (fun _ ↦ hρ)).submatrix _

/-- The party-major `k`-ebit target state `(|Ω₂⟩⟨Ω₂|)^{⊗ k}` on
`(Fin k → Fin 2) × (Fin k → Fin 2)`, using the same explicit regrouping as `bipartiteCopies`. -/
noncomputable def bellPairTarget (k : ℕ) :
    Matrix ((Fin k → Fin 2) × (Fin k → Fin 2)) ((Fin k → Fin 2) × (Fin k → Fin 2)) ℂ :=
  bipartiteCopies k (Matrix.omegaProj 2)

/-- The `k`-ebit target state has trace `1` for every `k : ℕ`. -/
theorem trace_bellPairTarget (k : ℕ) : (bellPairTarget k).trace = 1 :=
  trace_bipartiteCopies_eq_one k (Matrix.trace_omegaProj (d := 2) (by decide))

end BipartiteCopies

section LocalCopyDiscard

/-- Coordinate equivalence separating a chosen copy `i₀ : Fin k` from the remaining
copies `{j : Fin k // j ≠ i₀}`. -/
def splitCopyEquiv {k : ℕ} (i₀ : Fin k) (A : Type) :
    (Fin k → A) ≃ A × ({j : Fin k // j ≠ i₀} → A) where
  toFun f := (f i₀, fun j ↦ f j.1)
  invFun p j := if h : j = i₀ then p.1 else p.2 ⟨j, h⟩
  left_inv f := by
    funext j
    by_cases h : j = i₀
    · subst h; simp
    · simp [h]
  right_inv p := by
    rcases p with ⟨a, g⟩
    apply Prod.ext
    · simp
    · funext j
      simp [j.2]

@[simp]
theorem splitCopyEquiv_symm_apply_self {k : ℕ} (i₀ : Fin k) {A : Type}
    (a : A) (g : {j : Fin k // j ≠ i₀} → A) :
    (splitCopyEquiv i₀ A).symm (a, g) i₀ = a := by
  simp [splitCopyEquiv]

@[simp]
theorem splitCopyEquiv_symm_apply_ne {k : ℕ} (i₀ : Fin k) {A : Type}
    (a : A) (g : {j : Fin k // j ≠ i₀} → A) {j : Fin k} (hj : j ≠ i₀) :
    (splitCopyEquiv i₀ A).symm (a, g) j = g ⟨j, hj⟩ := by
  simp [splitCopyEquiv, hj]

/-- Local Kraus family on `Fin k → A` that keeps copy `i₀` and discards all other copies
`j ≠ i₀`, defined by reindexing `KrausFamily.traceRight` along `splitCopyEquiv`. -/
def keepCopyKraus {k : ℕ} (i₀ : Fin k) (A : Type) [Fintype A] [DecidableEq A] :
    KrausFamily (Fin k → A) A :=
  (KrausFamily.traceRight A ({j : Fin k // j ≠ i₀} → A)).reindex
    (splitCopyEquiv i₀ A) (Equiv.refl A)

/-- Local copy discard is trace-preserving. -/
theorem isTP_keepCopyKraus {k : ℕ} (i₀ : Fin k) (A : Type) [Fintype A] [DecidableEq A] :
    (keepCopyKraus i₀ A).IsTP :=
  KrausFamily.isTP_traceRight.reindex (splitCopyEquiv i₀ A) (Equiv.refl A)

theorem keepCopyKraus_op_apply {k : ℕ} (i₀ : Fin k) (A : Type) [Fintype A] [DecidableEq A]
    (g : {j : Fin k // j ≠ i₀} → A) (a : A) (f : Fin k → A) :
    (keepCopyKraus i₀ A).op g a f = if f = (splitCopyEquiv i₀ A).symm (a, g) then 1 else 0 := by
  change ((KrausFamily.traceRight A ({j : Fin k // j ≠ i₀} → A)).op g).submatrix
      (Equiv.refl A) (splitCopyEquiv i₀ A) a f = _
  simp only [Matrix.submatrix_apply, Equiv.refl_apply, Matrix.conjTranspose_apply,
    Matrix.basisInclusion, Function.Embedding.sectL_apply, Matrix.one_apply]
  have hiff : splitCopyEquiv i₀ A f = (a, g) ↔ f = (splitCopyEquiv i₀ A).symm (a, g) :=
    (Equiv.eq_symm_apply (splitCopyEquiv i₀ A)).symm
  by_cases h : f = (splitCopyEquiv i₀ A).symm (a, g)
  · simp [h]
  · have h' : splitCopyEquiv i₀ A f ≠ (a, g) := fun hEq ↦ h (hiff.mp hEq)
    simp [h, h']

/-- Bipartite product-Kraus separable operation that keeps copy `i₀ : Fin k` on both
parties and locally discards all remaining copies `j ≠ i₀`. -/
def keepCopySepOp {k : ℕ} (i₀ : Fin k) (A B : Type)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    SeparableOperation (Fin k → A) (Fin k → B) A B where
  Index := ({j : Fin k // j ≠ i₀} → A) × ({j : Fin k // j ≠ i₀} → B)
  left g := (keepCopyKraus i₀ A).op g.1
  right g := (keepCopyKraus i₀ B).op g.2

theorem keepCopySepOp_toKrausFamily {k : ℕ} (i₀ : Fin k) (A B : Type)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (keepCopySepOp i₀ A B).toKrausFamily =
      (keepCopyKraus i₀ A).prod (keepCopyKraus i₀ B) :=
  rfl

/-- Bipartite local copy discard is trace-preserving. -/
theorem isTP_keepCopySepOp {k : ℕ} (i₀ : Fin k) (A B : Type)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    (keepCopySepOp i₀ A B).IsTP :=
  (isTP_keepCopyKraus i₀ A).prod (isTP_keepCopyKraus i₀ B)

/-- Bipartite local copy discard contracts the full trace norm `Matrix.rectangularTraceNorm`. -/
theorem rectangularTraceNorm_keepCopySepOp_map_le {k : ℕ} (i₀ : Fin k) (A B : Type)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (X : Matrix ((Fin k → A) × (Fin k → B)) ((Fin k → A) × (Fin k → B)) ℂ) :
    Matrix.rectangularTraceNorm ((keepCopySepOp i₀ A B).map X) ≤
      Matrix.rectangularTraceNorm X :=
  (isTP_keepCopySepOp i₀ A B).rectangularTraceNorm_map_le X

/-- Entrywise formula for the action of `keepCopySepOp` on an arbitrary bipartite matrix. -/
theorem keepCopySepOp_map_apply {k : ℕ} (i₀ : Fin k) {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (M : Matrix ((Fin k → A) × (Fin k → B)) ((Fin k → A) × (Fin k → B)) ℂ)
    (a a' : A) (b b' : B) :
    (keepCopySepOp i₀ A B).map M (a, b) (a', b') =
      ∑ gA : {j : Fin k // j ≠ i₀} → A, ∑ gB : {j : Fin k // j ≠ i₀} → B,
        M ((splitCopyEquiv i₀ A).symm (a, gA), (splitCopyEquiv i₀ B).symm (b, gB))
          ((splitCopyEquiv i₀ A).symm (a', gA), (splitCopyEquiv i₀ B).symm (b', gB)) := by
  rw [SeparableOperation.map_apply, Matrix.sum_apply]
  change (∑ g : ({j : Fin k // j ≠ i₀} → A) × ({j : Fin k // j ≠ i₀} → B), _) = _
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun gA _ ↦ Finset.sum_congr rfl fun gB _ ↦ ?_
  let f1 : (Fin k → A) × (Fin k → B) :=
    ((splitCopyEquiv i₀ A).symm (a, gA), (splitCopyEquiv i₀ B).symm (b, gB))
  let f2 : (Fin k → A) × (Fin k → B) :=
    ((splitCopyEquiv i₀ A).symm (a', gA), (splitCopyEquiv i₀ B).symm (b', gB))
  have hL : ∀ p : (Fin k → A) × (Fin k → B),
      ((keepCopyKraus i₀ A).op gA ⊗ₖ (keepCopyKraus i₀ B).op gB) (a, b) p =
        if p = f1 then 1 else 0 := by
    rintro ⟨pA, pB⟩
    simp only [Matrix.kroneckerMap_apply, keepCopyKraus_op_apply, f1, Prod.mk.injEq]
    split_ifs <;> simp_all
  have hR : ∀ q : (Fin k → A) × (Fin k → B),
      ((keepCopyKraus i₀ A).op gA ⊗ₖ (keepCopyKraus i₀ B).op gB)ᴴ q (a', b') =
        if q = f2 then 1 else 0 := by
    rintro ⟨qA, qB⟩
    simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, keepCopyKraus_op_apply,
      f2, Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [keepCopySepOp, Matrix.mul_apply]
  trans (∑ q : (Fin k → A) × (Fin k → B),
      (∑ p : (Fin k → A) × (Fin k → B), (if p = f1 then (1 : ℂ) else 0) * M p q) *
        (if q = f2 then (1 : ℂ) else 0))
  · refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [hR q]
    congr 1
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [hL p]
  · simp [f1, f2]

/-- Locally discarding all copies except `i₀ : Fin k` sends `bipartiteCopies k ρ` to
`ρ.trace ^ (k - 1) • ρ`. -/
theorem keepCopySepOp_map_bipartiteCopies {k : ℕ} (i₀ : Fin k) {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) :
    (keepCopySepOp i₀ A B).map (bipartiteCopies k ρ) = ρ.trace ^ (k - 1) • ρ := by
  ext ⟨a, b⟩ ⟨a', b'⟩
  rw [keepCopySepOp_map_apply, Matrix.smul_apply, smul_eq_mul]
  have hfactor : ∀ (gA : {j : Fin k // j ≠ i₀} → A) (gB : {j : Fin k // j ≠ i₀} → B),
      bipartiteCopies k ρ
          ((splitCopyEquiv i₀ A).symm (a, gA), (splitCopyEquiv i₀ B).symm (b, gB))
          ((splitCopyEquiv i₀ A).symm (a', gA), (splitCopyEquiv i₀ B).symm (b', gB)) =
        (∏ j : {j : Fin k // j ≠ i₀}, ρ (gA j, gB j) (gA j, gB j)) * ρ (a, b) (a', b') := by
    intro gA gB
    rw [bipartiteCopies_apply]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    rw [splitCopyEquiv_symm_apply_self, splitCopyEquiv_symm_apply_self,
      splitCopyEquiv_symm_apply_self, splitCopyEquiv_symm_apply_self, mul_comm]
    congr 1
    trans (∏ j : {j : Fin k // j ≠ i₀},
      ρ ((splitCopyEquiv i₀ A).symm (a, gA) j.1, (splitCopyEquiv i₀ B).symm (b, gB) j.1)
        ((splitCopyEquiv i₀ A).symm (a', gA) j.1, (splitCopyEquiv i₀ B).symm (b', gB) j.1))
    · exact Finset.prod_subtype (Finset.univ.erase i₀) (fun j ↦ by simp) _
    · refine Finset.prod_congr rfl fun j _ ↦ ?_
      simp [splitCopyEquiv_symm_apply_ne i₀ _ _ j.2]
  simp_rw [hfactor, ← Finset.sum_mul]
  congr 1
  let e := Equiv.arrowProdEquivProdArrow {j : Fin k // j ≠ i₀} (fun _ ↦ A) (fun _ ↦ B)
  have hsum :
      (∑ gA : {j : Fin k // j ≠ i₀} → A, ∑ gB : {j : Fin k // j ≠ i₀} → B,
          ∏ j : {j : Fin k // j ≠ i₀}, ρ (gA j, gB j) (gA j, gB j)) =
        ∑ g : {j : Fin k // j ≠ i₀} → A × B,
          ∏ j : {j : Fin k // j ≠ i₀}, ρ (g j) (g j) := by
    rw [← Fintype.sum_prod_type (fun p : ({j : Fin k // j ≠ i₀} → A) × ({j : Fin k // j ≠ i₀} → B) ↦
      ∏ j : {j : Fin k // j ≠ i₀}, ρ (p.1 j, p.2 j) (p.1 j, p.2 j))]
    exact (Fintype.sum_equiv e _ _ (fun g ↦ rfl)).symm
  rw [hsum, (Fintype.prod_sum fun (_ : {j : Fin k // j ≠ i₀}) (p : A × B) ↦ ρ p p).symm]
  change (∏ _ : {j : Fin k // j ≠ i₀}, ρ.trace) = ρ.trace ^ (k - 1)
  rw [Finset.prod_const, Finset.card_univ]
  have hcard : Fintype.card {j : Fin k // j ≠ i₀} = k - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  rw [hcard]

/-- For a unit-trace bipartite matrix `ρ`, locally discarding all copies except `i₀` maps
`bipartiteCopies k ρ` back to `ρ`. -/
theorem keepCopySepOp_map_bipartiteCopies_of_trace_eq_one {k : ℕ} (i₀ : Fin k) {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.trace = 1) :
    (keepCopySepOp i₀ A B).map (bipartiteCopies k ρ) = ρ := by
  rw [keepCopySepOp_map_bipartiteCopies, hρ, one_pow, one_smul]

/-- Locally discarding all Bell pairs except `i₀ : Fin k` sends `bellPairTarget k` to the
single two-qubit Bell projector `Matrix.omegaProj 2`. -/
theorem keepCopySepOp_map_bellPairTarget {k : ℕ} (i₀ : Fin k) :
    (keepCopySepOp i₀ (Fin 2) (Fin 2)).map (bellPairTarget k) = Matrix.omegaProj 2 :=
  keepCopySepOp_map_bipartiteCopies_of_trace_eq_one i₀ (Matrix.trace_omegaProj (d := 2) (by decide))

/-- Locally keeping one Bell pair `i₀ : Fin k` does not increase the full trace-norm error
relative to the Bell target. -/
theorem rectangularTraceNorm_keepCopySepOp_sub_omegaProj_le {k : ℕ} (i₀ : Fin k)
    (σ : Matrix ((Fin k → Fin 2) × (Fin k → Fin 2))
      ((Fin k → Fin 2) × (Fin k → Fin 2)) ℂ) :
    Matrix.rectangularTraceNorm ((keepCopySepOp i₀ (Fin 2) (Fin 2)).map σ - Matrix.omegaProj 2) ≤
      Matrix.rectangularTraceNorm (σ - bellPairTarget k) := by
  rw [← keepCopySepOp_map_bellPairTarget i₀, ← map_sub]
  exact rectangularTraceNorm_keepCopySepOp_map_le i₀ (Fin 2) (Fin 2) (σ - bellPairTarget k)

/-- Convenience specialization keeping the first Bell pair `⟨0, hk⟩` out of `k ≥ 1` pairs. -/
abbrev keepFirstBellPair {k : ℕ} (hk : 1 ≤ k) :
    SeparableOperation (Fin k → Fin 2) (Fin k → Fin 2) (Fin 2) (Fin 2) :=
  keepCopySepOp ⟨0, hk⟩ (Fin 2) (Fin 2)

theorem isTP_keepFirstBellPair {k : ℕ} (hk : 1 ≤ k) : (keepFirstBellPair hk).IsTP :=
  isTP_keepCopySepOp ⟨0, hk⟩ (Fin 2) (Fin 2)

theorem keepFirstBellPair_map_bellPairTarget {k : ℕ} (hk : 1 ≤ k) :
    (keepFirstBellPair hk).map (bellPairTarget k) = Matrix.omegaProj 2 :=
  keepCopySepOp_map_bellPairTarget ⟨0, hk⟩

theorem rectangularTraceNorm_keepFirstBellPair_sub_omegaProj_le {k : ℕ} (hk : 1 ≤ k)
    (σ : Matrix ((Fin k → Fin 2) × (Fin k → Fin 2))
      ((Fin k → Fin 2) × (Fin k → Fin 2)) ℂ) :
    Matrix.rectangularTraceNorm ((keepFirstBellPair hk).map σ - Matrix.omegaProj 2) ≤
      Matrix.rectangularTraceNorm (σ - bellPairTarget k) :=
  rectangularTraceNorm_keepCopySepOp_sub_omegaProj_le ⟨0, hk⟩ σ

end LocalCopyDiscard

end QuantumInfo
