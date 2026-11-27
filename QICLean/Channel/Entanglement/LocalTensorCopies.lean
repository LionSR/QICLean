/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Kronecker.TensorMap
import QICLean.Algebra.Kronecker.Vectors
import QICLean.Algebra.Matrix.KroneckerEmbed
import QICLean.Algebra.Matrix.MatrixTracePairing
import QICLean.Channel.Entanglement.BipartiteCopies
import QICLean.Channel.Entanglement.ReverseBlockCriterion

/-!
# Party-major local tensor copies, trace-adjoint pullbacks, and rank-one multiplicativity

This file provides reusable infrastructure connecting party-major `N`-copy tensor products
of local rectangular maps `L ⊗ M` to copy-major `Matrix.piTensorMap` and
`QuantumInfo.bipartiteCopies`, together with trace-adjoint pullbacks and exact
multiplicativity of rank-one matrix elements under tensor powers.

## Main definitions

* `Matrix.vecKronecker` — Kronecker product of two vectors `(i, j) ↦ a i * b j`.
* `QuantumInfo.localTensorCopies` — party-major `N`-copy map `L^{⊗ N} ⊗ M^{⊗ N}`
  built from `Matrix.piTensorMap`, `Matrix.tensorMapIdLM`, and `Matrix.idTensorMapLM`.
* `QuantumInfo.bipartiteVecCopies` — party-major `N`-copy tensor power of a bipartite
  vector `u : A × B → ℂ`.
* `QuantumInfo.vecPower` — `t`-fold tensor power of a vector `(Fin N → α) → ℂ` on
  `Fin (N * t) → α`.

## Main results

* `IsKrausCP.traceAdjointMap_isKrausCP` — the trace-pairing adjoint of a rectangular
  Kraus-CP map is Kraus-CP.
* `QuantumInfo.localTensorCopies_eq_piTensorMap_reindex` — party-major `L^{⊗ N} ⊗ M^{⊗ N}`
  equals `Matrix.piTensorMap (fun _ : Fin N => C)` reindexed by `Equiv.arrowProdEquivProdArrow`.
* `QuantumInfo.trace_kronecker_mul_localTensorCopies` — trace-adjoint pullback identity
  for `localTensorCopies N L M`.
* `QuantumInfo.isKrausCP_localTensorCopies` — complete positivity of `localTensorCopies N L M`.
* `QuantumInfo.localTensorCopies_vecMulVec_eq_bipartiteCopies` — action on `|u^{⊗ N}⟩⟨u^{⊗ N}|`.
* `QuantumInfo.quad_bipartiteCopies_mul_vecPower` — exact `t`-th power multiplicativity of
  rank-one matrix elements under `bipartiteCopies (N * t)`.
-/

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

/-! ## Section 1: Vector Kronecker products and trace-adjoint complete positivity -/



/-! ## Section 2: Party-major local tensor copies -/

section LocalTensorCopies

/-- Party-major `N`-copy map built from two local maps `L` and `M` via `Matrix.piTensorMap`. -/
noncomputable def QuantumInfo.localTensorCopies
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    (N : ℕ)
    (L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ)
    (M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ) :
    Matrix ((Fin N → A_in) × (Fin N → B_in)) ((Fin N → A_in) × (Fin N → B_in)) ℂ →ₗ[ℂ]
      Matrix ((Fin N → A_out) × (Fin N → B_out)) ((Fin N → A_out) × (Fin N → B_out)) ℂ :=
  (Matrix.tensorMapIdLM (Matrix.piTensorMap (fun _ : Fin N => L))).comp
    (Matrix.idTensorMapLM (Matrix.piTensorMap (fun _ : Fin N => M)))

/-- Action of `localTensorCopies` on a Kronecker product `X ⊗ₖ Y`. -/
theorem QuantumInfo.localTensorCopies_kronecker
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    (N : ℕ)
    (L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ)
    (M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ)
    (X : Matrix (Fin N → A_in) (Fin N → A_in) ℂ)
    (Y : Matrix (Fin N → B_in) (Fin N → B_in) ℂ) :
    QuantumInfo.localTensorCopies N L M (X ⊗ₖ Y) =
      Matrix.piTensorMap (fun _ : Fin N => L) X ⊗ₖ
        Matrix.piTensorMap (fun _ : Fin N => M) Y := by
  simp only [QuantumInfo.localTensorCopies, LinearMap.comp_apply,
    Matrix.idTensorMapLM_apply, Matrix.tensorMapIdLM_apply,
    Matrix.idTensorMap_kronecker, Matrix.tensorMapId_kronecker]

/-- `localTensorCopies N L M` is the party-major reindexing of
`Matrix.piTensorMap (fun _ : Fin N => C)` whenever `C (X ⊗ₖ Y) = L X ⊗ₖ M Y`. -/
theorem QuantumInfo.localTensorCopies_eq_piTensorMap_reindex
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    (N : ℕ)
    (L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ)
    (M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ)
    (C : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (Z : Matrix ((Fin N → A_in) × (Fin N → B_in)) ((Fin N → A_in) × (Fin N → B_in)) ℂ) :
    QuantumInfo.localTensorCopies N L M Z =
      (Matrix.piTensorMap (fun _ : Fin N => C)
        (Z.submatrix
          (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_in) (fun _ => B_in))
          (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_in) (fun _ => B_in)))).submatrix
        (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_out) (fun _ => B_out)).symm
        (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_out) (fun _ => B_out)).symm := by
  let eIn := Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_in) (fun _ => B_in)
  let eOut := Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_out) (fun _ => B_out)
  let rhsLM :
      Matrix ((Fin N → A_in) × (Fin N → B_in)) ((Fin N → A_in) × (Fin N → B_in)) ℂ →ₗ[ℂ]
        Matrix ((Fin N → A_out) × (Fin N → B_out)) ((Fin N → A_out) × (Fin N → B_out)) ℂ :=
    { toFun := fun W =>
        (Matrix.piTensorMap (fun _ : Fin N => C) (W.submatrix eIn eIn)).submatrix
          eOut.symm eOut.symm
      map_add' := fun W₁ W₂ => by
        ext p q
        simp [Matrix.submatrix_apply, Matrix.submatrix_add, map_add]
      map_smul' := fun c W => by
        ext p q
        simp [Matrix.submatrix_apply, Matrix.submatrix_smul, map_smul] }
  change QuantumInfo.localTensorCopies N L M Z = rhsLM Z
  have hlin : QuantumInfo.localTensorCopies N L M = rhsLM := by
    refine Matrix.linearMap_ext_kronecker fun X Y => ?_
    rw [QuantumInfo.localTensorCopies_kronecker]
    ext ⟨aA, aB⟩ ⟨bA, bB⟩
    simp only [rhsLM, LinearMap.coe_mk, AddHom.coe_mk, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Matrix.piTensorMap_apply]
    have hsingle : ∀ (i : Fin N) (p q : A_in × B_in),
        C (Matrix.single p q (1 : ℂ)) (aA i, aB i) (bA i, bB i) =
          L (Matrix.single p.1 q.1 (1 : ℂ)) (aA i) (bA i) *
            M (Matrix.single p.2 q.2 (1 : ℂ)) (aB i) (bB i) := by
      intro i ⟨p₁, p₂⟩ ⟨q₁, q₂⟩
      have hkron : Matrix.single (p₁, p₂) (q₁, q₂) (1 : ℂ) =
          Matrix.single p₁ q₁ (1 : ℂ) ⊗ₖ Matrix.single p₂ q₂ (1 : ℂ) := by
        ext ⟨r₁, r₂⟩ ⟨c₁, c₂⟩
        simp only [Matrix.single_apply, Matrix.kroneckerMap_apply, Prod.mk.injEq]
        by_cases h1 : p₁ = r₁ <;> by_cases h2 : p₂ = r₂ <;>
          by_cases h3 : q₁ = c₁ <;> by_cases h4 : q₂ = c₂ <;> simp [h1, h2, h3, h4]
      rw [hkron, hC, Matrix.kroneckerMap_apply]
    have hlhs :
        (∑ xA : Fin N → A_in, ∑ yA : Fin N → A_in,
            X xA yA * ∏ k : Fin N, L (Matrix.single (xA k) (yA k) 1) (aA k) (bA k)) *
          (∑ xB : Fin N → B_in, ∑ yB : Fin N → B_in,
            Y xB yB * ∏ k : Fin N, M (Matrix.single (xB k) (yB k) 1) (aB k) (bB k)) =
          ∑ p : (Fin N → A_in × B_in) × (Fin N → A_in × B_in),
            (X (eIn p.1).1 (eIn p.2).1 * Y (eIn p.1).2 (eIn p.2).2) *
              ((∏ k : Fin N, L (Matrix.single (p.1 k).1 (p.2 k).1 1) (aA k) (bA k)) *
               (∏ k : Fin N, M (Matrix.single (p.1 k).2 (p.2 k).2 1) (aB k) (bB k))) := by
      have h1 :
          (∑ xA : Fin N → A_in, ∑ yA : Fin N → A_in,
              X xA yA * ∏ k : Fin N, L (Matrix.single (xA k) (yA k) 1) (aA k) (bA k)) =
            ∑ pA : (Fin N → A_in) × (Fin N → A_in),
              X pA.1 pA.2 * ∏ k : Fin N, L (Matrix.single (pA.1 k) (pA.2 k) 1) (aA k) (bA k) :=
        (Fintype.sum_prod_type (fun pA : (Fin N → A_in) × (Fin N → A_in) =>
          X pA.1 pA.2 * ∏ k : Fin N, L (Matrix.single (pA.1 k) (pA.2 k) 1) (aA k) (bA k))).symm
      have h2 :
          (∑ xB : Fin N → B_in, ∑ yB : Fin N → B_in,
              Y xB yB * ∏ k : Fin N, M (Matrix.single (xB k) (yB k) 1) (aB k) (bB k)) =
            ∑ pB : (Fin N → B_in) × (Fin N → B_in),
              Y pB.1 pB.2 * ∏ k : Fin N, M (Matrix.single (pB.1 k) (pB.2 k) 1) (aB k) (bB k) :=
        (Fintype.sum_prod_type (fun pB : (Fin N → B_in) × (Fin N → B_in) =>
          Y pB.1 pB.2 * ∏ k : Fin N, M (Matrix.single (pB.1 k) (pB.2 k) 1) (aB k) (bB k))).symm
      rw [h1, h2, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
      let e4 : (((Fin N → A_in) × (Fin N → A_in)) × ((Fin N → B_in) × (Fin N → B_in))) ≃
          ((Fin N → A_in × B_in) × (Fin N → A_in × B_in)) :=
        { toFun := fun q => (eIn.symm (q.1.1, q.2.1), eIn.symm (q.1.2, q.2.2))
          invFun := fun p => (((eIn p.1).1, (eIn p.2).1), ((eIn p.1).2, (eIn p.2).2))
          left_inv := fun q => by simp
          right_inv := fun p => by simp }
      refine Fintype.sum_equiv e4 _ _ fun q => ?_
      simp only [e4, eIn, Equiv.coe_fn_mk, Equiv.apply_symm_apply,
        Equiv.arrowProdEquivProdArrow_symm_apply]
      ring
    have hrhs :
        (∑ x : Fin N → A_in × B_in, ∑ y : Fin N → A_in × B_in,
            (X (eIn x).1 (eIn y).1 * Y (eIn x).2 (eIn y).2) *
              ∏ k : Fin N, C (Matrix.single (x k) (y k) 1)
                (eOut.symm (aA, aB) k) (eOut.symm (bA, bB) k)) =
          ∑ p : (Fin N → A_in × B_in) × (Fin N → A_in × B_in),
            (X (eIn p.1).1 (eIn p.2).1 * Y (eIn p.1).2 (eIn p.2).2) *
              ((∏ k : Fin N, L (Matrix.single (p.1 k).1 (p.2 k).1 1) (aA k) (bA k)) *
               (∏ k : Fin N, M (Matrix.single (p.1 k).2 (p.2 k).2 1) (aB k) (bB k))) := by
      rw [← Fintype.sum_prod_type (fun p : (Fin N → A_in × B_in) × (Fin N → A_in × B_in) =>
        (X (eIn p.1).1 (eIn p.2).1 * Y (eIn p.1).2 (eIn p.2).2) *
          ∏ k : Fin N, C (Matrix.single (p.1 k) (p.2 k) 1)
            (eOut.symm (aA, aB) k) (eOut.symm (bA, bB) k))]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      simpa [eOut] using hsingle k (p.1 k) (p.2 k)
    exact hlhs.trans hrhs.symm
  exact congrArg (fun f => f Z) hlin

/-- Trace-adjoint pullback identity for `localTensorCopies N L M`:
`tr((X ⊗ₖ Y) * localTensorCopies N L M Z) = tr((L_N* X ⊗ₖ M_N* Y) * Z)`. -/
theorem QuantumInfo.trace_kronecker_mul_localTensorCopies
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [Fintype B_out]
    (N : ℕ)
    (L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ)
    (M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ)
    (X : Matrix (Fin N → A_out) (Fin N → A_out) ℂ)
    (Y : Matrix (Fin N → B_out) (Fin N → B_out) ℂ)
    (Z : Matrix ((Fin N → A_in) × (Fin N → B_in)) ((Fin N → A_in) × (Fin N → B_in)) ℂ) :
    ((X ⊗ₖ Y) * QuantumInfo.localTensorCopies N L M Z).trace =
      ((Matrix.traceAdjointMap (Matrix.piTensorMap (fun _ : Fin N => L)) X ⊗ₖ
        Matrix.traceAdjointMap (Matrix.piTensorMap (fun _ : Fin N => M)) Y) * Z).trace := by
  let lhsLM :
      Matrix ((Fin N → A_in) × (Fin N → B_in)) ((Fin N → A_in) × (Fin N → B_in)) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun W => ((X ⊗ₖ Y) * QuantumInfo.localTensorCopies N L M W).trace
      map_add' := fun W₁ W₂ => by simp [map_add, Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c W => by simp [map_smul, Matrix.trace_smul] }
  let rhsLM :
      Matrix ((Fin N → A_in) × (Fin N → B_in)) ((Fin N → A_in) × (Fin N → B_in)) ℂ →ₗ[ℂ] ℂ :=
    { toFun := fun W =>
        ((Matrix.traceAdjointMap (Matrix.piTensorMap (fun _ : Fin N => L)) X ⊗ₖ
          Matrix.traceAdjointMap (Matrix.piTensorMap (fun _ : Fin N => M)) Y) * W).trace
      map_add' := fun W₁ W₂ => by simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c W => by simp [Matrix.trace_smul] }
  change lhsLM Z = rhsLM Z
  have hlin : lhsLM = rhsLM := by
    refine Matrix.linearMap_ext_kronecker fun A B => ?_
    simp only [lhsLM, rhsLM, LinearMap.coe_mk, AddHom.coe_mk,
      QuantumInfo.localTensorCopies_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.trace_kronecker, Matrix.trace_traceAdjointMap_mul]
  exact congrArg (fun f => f Z) hlin

/-- `localTensorCopies N L M` is completely positive whenever `L` and `M` are. -/
theorem QuantumInfo.isKrausCP_localTensorCopies
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    [Fintype A_out] [DecidableEq A_out] [Fintype B_out] [DecidableEq B_out]
    (N : ℕ)
    {L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ}
    {M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ}
    (hL : IsKrausCP L) (hM : IsKrausCP M) :
    IsKrausCP (QuantumInfo.localTensorCopies N L M) := by
  have hLN : IsKrausCP (Matrix.piTensorMap (fun _ : Fin N => L)) :=
    Matrix.isKrausCP_piTensorMap (fun _ => hL)
  have hMN : IsKrausCP (Matrix.piTensorMap (fun _ : Fin N => M)) :=
    Matrix.isKrausCP_piTensorMap (fun _ => hM)
  obtain ⟨rL, KL, hKL⟩ := hLN
  obtain ⟨rM, KM, hKM⟩ := hMN
  let e : Fin (rL * rM) ≃ Fin rL × Fin rM := finProdFinEquiv.symm
  refine ⟨rL * rM, fun idx => KL (e idx).1 ⊗ₖ KM (e idx).2, fun Z => ?_⟩
  let rhsLM :
      Matrix ((Fin N → A_in) × (Fin N → B_in)) ((Fin N → A_in) × (Fin N → B_in)) ℂ →ₗ[ℂ]
        Matrix ((Fin N → A_out) × (Fin N → B_out)) ((Fin N → A_out) × (Fin N → B_out)) ℂ :=
    { toFun := fun W =>
        ∑ idx : Fin (rL * rM),
          (KL (e idx).1 ⊗ₖ KM (e idx).2) * W * (KL (e idx).1 ⊗ₖ KM (e idx).2)ᴴ
      map_add' := fun W₁ W₂ => by
        simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := fun c W => by
        simp [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum] }
  change QuantumInfo.localTensorCopies N L M Z = rhsLM Z
  have hlin : QuantumInfo.localTensorCopies N L M = rhsLM := by
    refine Matrix.linearMap_ext_kronecker fun X Y => ?_
    simp only [rhsLM, LinearMap.coe_mk, AddHom.coe_mk, QuantumInfo.localTensorCopies_kronecker,
      hKL, hKM]
    rw [e.sum_comp (fun p : Fin rL × Fin rM =>
      (KL p.1 ⊗ₖ KM p.2) * (X ⊗ₖ Y) * (KL p.1 ⊗ₖ KM p.2)ᴴ)]
    rw [Fintype.sum_prod_type]
    ext ⟨a, b⟩ ⟨a', b'⟩
    simp only [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul_sum]
  exact congrArg (fun f => f Z) hlin

/-- Party-major `N`-copy tensor power of a bipartite vector `u : A × B → ℂ`. -/
def QuantumInfo.bipartiteVecCopies {A B : Type} (N : ℕ) (u : A × B → ℂ) :
    (Fin N → A) × (Fin N → B) → ℂ :=
  fun p => ∏ i : Fin N, u (p.1 i, p.2 i)

/-- `localTensorCopies N L M` maps `|u^{⊗ N}⟩⟨u^{⊗ N}|` to `bipartiteCopies N (C(|u⟩⟨u|))`. -/
theorem QuantumInfo.localTensorCopies_vecMulVec_eq_bipartiteCopies
    {A_in B_in A_out B_out : Type}
    [Fintype A_in] [DecidableEq A_in] [Fintype B_in] [DecidableEq B_in]
    (N : ℕ)
    (L : Matrix A_in A_in ℂ →ₗ[ℂ] Matrix A_out A_out ℂ)
    (M : Matrix B_in B_in ℂ →ₗ[ℂ] Matrix B_out B_out ℂ)
    (C : Matrix (A_in × B_in) (A_in × B_in) ℂ →ₗ[ℂ] Matrix (A_out × B_out) (A_out × B_out) ℂ)
    (hC : ∀ X Y, C (X ⊗ₖ Y) = L X ⊗ₖ M Y)
    (u : A_in × B_in → ℂ) :
    QuantumInfo.localTensorCopies N L M
        (Matrix.vecMulVec (QuantumInfo.bipartiteVecCopies N u)
          (star (QuantumInfo.bipartiteVecCopies N u))) =
      QuantumInfo.bipartiteCopies N (C (Matrix.vecMulVec u (star u))) := by
  rw [QuantumInfo.localTensorCopies_eq_piTensorMap_reindex N L M C hC]
  have hsub :
      (Matrix.vecMulVec (QuantumInfo.bipartiteVecCopies N u)
          (star (QuantumInfo.bipartiteVecCopies N u))).submatrix
        (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_in) (fun _ => B_in))
        (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => A_in) (fun _ => B_in)) =
      Matrix.piKronecker (fun _ : Fin N => Matrix.vecMulVec u (star u)) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.vecMulVec_apply, QuantumInfo.bipartiteVecCopies,
      Pi.star_apply, star_prod, Matrix.piKronecker_apply, Finset.prod_mul_distrib,
      Equiv.arrowProdEquivProdArrow_apply]
  rw [hsub, Matrix.piTensorMap_piKronecker]
  rfl

/-- **Scaling invariance:** `bipartiteCopies N (c • R) = (c ^ N) • bipartiteCopies N R`. -/
theorem QuantumInfo.bipartiteCopies_smul {A B : Type} (N : ℕ) (c : ℂ)
    (R : Matrix (A × B) (A × B) ℂ) :
    QuantumInfo.bipartiteCopies N (c • R) = (c ^ N) • QuantumInfo.bipartiteCopies N R := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp [QuantumInfo.bipartiteCopies_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib]

end LocalTensorCopies

/-! ## Section 3: Exact tensor-power multiplicativity of rank-one matrix elements -/

section RankOneMultiplicativity

/-- `t`-fold tensor power of a vector `f : (Fin N → α) → ℂ`, indexed on `Fin (N * t) → α`
via `finProdFinEquiv : Fin N × Fin t ≃ Fin (N * t)`. -/
def QuantumInfo.vecPower {α : Type} {N : ℕ} (t : ℕ) (f : (Fin N → α) → ℂ) :
    (Fin (N * t) → α) → ℂ :=
  fun x => ∏ r : Fin t, f (fun i : Fin N => x (finProdFinEquiv (i, r)))

/-- **Exact multiplicativity of rank-one matrix elements under `bipartiteCopies (N * t)`.**
For any bipartite matrix `R` and any local filter vectors `fA, gA, fB, gB` on `N` copies,
the matrix element of `bipartiteCopies (N * t) R` between `vecPower t` product vectors is
the exact `t`-th power of the `N`-copy matrix element. -/
theorem QuantumInfo.quad_bipartiteCopies_mul_vecPower
    {A B : Type} [Fintype A] [Fintype B]
    (R : Matrix (A × B) (A × B) ℂ) (N t : ℕ)
    (fA gA : (Fin N → A) → ℂ) (fB gB : (Fin N → B) → ℂ) :
    star (Matrix.vecKronecker (QuantumInfo.vecPower t fA) (QuantumInfo.vecPower t fB)) ⬝ᵥ
        QuantumInfo.bipartiteCopies (N * t) R *ᵥ
          Matrix.vecKronecker (QuantumInfo.vecPower t gA) (QuantumInfo.vecPower t gB) =
      (star (Matrix.vecKronecker fA fB) ⬝ᵥ
        QuantumInfo.bipartiteCopies N R *ᵥ Matrix.vecKronecker gA gB) ^ t := by
  let eA : (Fin (N * t) → A) ≃ (Fin t → Fin N → A) :=
    { toFun := fun x r i => x (finProdFinEquiv (i, r))
      invFun := fun g k => g (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
      left_inv := fun x => by funext k; exact congrArg x (finProdFinEquiv.apply_symm_apply k)
      right_inv := fun g => by funext r i; simp }
  let eB : (Fin (N * t) → B) ≃ (Fin t → Fin N → B) :=
    { toFun := fun x r i => x (finProdFinEquiv (i, r))
      invFun := fun g k => g (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1
      left_inv := fun x => by funext k; exact congrArg x (finProdFinEquiv.apply_symm_apply k)
      right_inv := fun g => by funext r i; simp }
  let Q := ((Fin N → A) × (Fin N → B)) × ((Fin N → A) × (Fin N → B))
  let F : Q → ℂ := fun q =>
    star (fA q.1.1 * fB q.1.2) *
      QuantumInfo.bipartiteCopies N R q.1 q.2 *
      (gA q.2.1 * gB q.2.2)
  have hrhs :
      (star (Matrix.vecKronecker fA fB) ⬝ᵥ
          QuantumInfo.bipartiteCopies N R *ᵥ Matrix.vecKronecker gA gB) ^ t =
        ∑ p : Fin t → Q, ∏ r : Fin t, F (p r) := by
    have hterm :
        star (Matrix.vecKronecker fA fB) ⬝ᵥ
            QuantumInfo.bipartiteCopies N R *ᵥ Matrix.vecKronecker gA gB =
          ∑ q : Q, F q := by
      rw [Fintype.sum_prod_type F]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rcases x with ⟨xA, xB⟩
      rcases y with ⟨yA, yB⟩
      simp only [F, Matrix.vecKronecker_apply, mul_assoc]
    rw [hterm]
    calc
      (∑ q : Q, F q) ^ t = ∏ _r : Fin t, ∑ q : Q, F q := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∑ p : Fin t → Q, ∏ r : Fin t, F (p r) := Fintype.prod_sum (fun _ q => F q)
  have hlhs :
      star (Matrix.vecKronecker (QuantumInfo.vecPower t fA) (QuantumInfo.vecPower t fB)) ⬝ᵥ
          QuantumInfo.bipartiteCopies (N * t) R *ᵥ
            Matrix.vecKronecker (QuantumInfo.vecPower t gA) (QuantumInfo.vecPower t gB) =
        ∑ q : (((Fin (N * t) → A) × (Fin (N * t) → B)) ×
               ((Fin (N * t) → A) × (Fin (N * t) → B))),
          ∏ r : Fin t, F ((eA q.1.1 r, eB q.1.2 r), (eA q.2.1 r, eB q.2.2 r)) := by
    rw [Fintype.sum_prod_type (fun q : (((Fin (N * t) → A) × (Fin (N * t) → B)) ×
        ((Fin (N * t) → A) × (Fin (N * t) → B))) =>
      ∏ r : Fin t, F ((eA q.1.1 r, eB q.1.2 r), (eA q.2.1 r, eB q.2.2 r)))]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rcases x with ⟨xA, xB⟩
    rcases y with ⟨yA, yB⟩
    have hRprod :
        QuantumInfo.bipartiteCopies (N * t) R (xA, xB) (yA, yB) =
          ∏ r : Fin t, QuantumInfo.bipartiteCopies N R
            (eA xA r, eB xB r) (eA yA r, eB yB r) := by
      rw [QuantumInfo.bipartiteCopies_apply]
      rw [← finProdFinEquiv.prod_comp (fun k : Fin (N * t) => R (xA k, xB k) (yA k, yB k))]
      rw [Fintype.prod_prod_type_right]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [QuantumInfo.bipartiteCopies_apply]
      rfl
    simp only [Matrix.vecKronecker_apply, hRprod, QuantumInfo.vecPower,
      star_mul', star_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    simp only [F, eA, eB, Equiv.coe_fn_mk, star_mul']
    ring
  rw [hlhs, hrhs]
  let eDir :
      ((((Fin (N * t) → A) × (Fin (N * t) → B)) ×
        ((Fin (N * t) → A) × (Fin (N * t) → B)))) ≃
      (Fin t → Q) :=
    { toFun := fun q r => ((eA q.1.1 r, eB q.1.2 r), (eA q.2.1 r, eB q.2.2 r))
      invFun := fun p =>
        ((eA.symm (fun r => (p r).1.1), eB.symm (fun r => (p r).1.2)),
         (eA.symm (fun r => (p r).2.1), eB.symm (fun r => (p r).2.2)))
      left_inv := fun q => by
        rcases q with ⟨⟨xA, xB⟩, ⟨yA, yB⟩⟩
        simp
      right_inv := fun p => by
        funext r
        simp }
  exact Fintype.sum_equiv eDir _ _ fun q => rfl

end RankOneMultiplicativity
