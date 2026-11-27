/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap.KrausFamily

/-!
# Finite product-Kraus operations

Adapted from `NPTEnt/Quantum/SeparableOperation.lean` in the uncommitted NPTEnt
working copy (no source commit available; SHA-256
`1e490b23dfd630dd3471f001adf03ebefca41741e77e88473a18ca66a6da9278`).
Changes: QICLean header and source notice only; the `QuantumInfo` API is retained.

`QuantumInfo.SeparableOperation` records rectangular local operators with a shared finite
outcome index. Its associated KrausFamily has operators left i ⊗ₖ right i.
This is an unrestricted algebraic CP operation: neither trace preservation nor trace
nonincrease is part of the structure. Physical channels and postselection branches require
IsTP and IsTraceNonincreasing, respectively. In particular, the trace of an unrestricted
output is not asserted to be a probability.

The input and output coordinates are party-major product bases. No identification with
LOCC (finite-round or otherwise) is made here.
-/

open Matrix
open scoped Kronecker

namespace QuantumInfo

/-- A finite shared-index product-Kraus presentation, with no normalization imposed. -/
structure SeparableOperation (A B Aout Bout : Type) : Type 1 where
  /-- The common outcome index for both parties; it may be empty. -/
  Index : Type
  [fintype : Fintype Index]
  /-- Alice's rectangular local operators. -/
  left : Index → Matrix Aout A ℂ
  /-- Bob's rectangular local operators. -/
  right : Index → Matrix Bout B ℂ

attribute [instance] SeparableOperation.fintype

namespace SeparableOperation

variable {A B Aout Bout : Type}

/-- Forget the factorization, retaining the shared outcome index. -/
def toKrausFamily (S : SeparableOperation A B Aout Bout) :
    KrausFamily (A × B) (Aout × Bout) :=
  ⟨S.Index, fun i ↦ S.left i ⊗ₖ S.right i⟩

@[simp] theorem toKrausFamily_op (S : SeparableOperation A B Aout Bout)
    (i : S.Index) : S.toKrausFamily.op i = S.left i ⊗ₖ S.right i := rfl

/-- The one-outcome operation with local operators L and R. -/
def single (L : Matrix Aout A ℂ) (R : Matrix Bout B ℂ) :
    SeparableOperation A B Aout Bout :=
  ⟨Unit, fun _ ↦ L, fun _ ↦ R⟩

/-- The identity product operation. -/
def id (A B : Type) [DecidableEq A] [DecidableEq B] : SeparableOperation A B A B :=
  single 1 1

section Map

variable [Fintype A] [Fintype B] [Fintype Aout] [Fintype Bout]

/-- The linear CP map induced by the product Kraus operators. -/
noncomputable def map (S : SeparableOperation A B Aout Bout) :
    Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (Aout × Bout) (Aout × Bout) ℂ :=
  S.toKrausFamily.map

omit [Fintype Aout] [Fintype Bout] in
/-- The correlated sum formula: both local factors use the same index. -/
theorem map_apply (S : SeparableOperation A B Aout Bout)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    S.map ρ = ∑ i, (S.left i ⊗ₖ S.right i) * ρ * (S.left i ⊗ₖ S.right i)ᴴ := rfl

omit [Fintype Aout] [Fintype Bout] in
/-- A single product operator acts by a product sandwich on arbitrary bipartite input. -/
theorem map_single (L : Matrix Aout A ℂ) (R : Matrix Bout B ℂ)
    (ρ : Matrix (A × B) (A × B) ℂ) :
    (single L R).map ρ = (L ⊗ₖ R) * ρ * (L ⊗ₖ R)ᴴ := by
  exact KrausFamily.map_single (L ⊗ₖ R) ρ

omit [Fintype Aout] [Fintype Bout] in
/-- On product inputs, each branch is the product of the two local sandwiches.
The shared sum cannot in general be replaced by a product of two independent sums. -/
theorem map_kronecker (S : SeparableOperation A B Aout Bout)
    (ρ : Matrix A A ℂ) (σ : Matrix B B ℂ) :
    S.map (ρ ⊗ₖ σ) = ∑ i,
      (S.left i * ρ * (S.left i)ᴴ) ⊗ₖ (S.right i * σ * (S.right i)ᴴ) := by
  simp only [map_apply, conjTranspose_kronecker, ← mul_kronecker_mul]

@[simp] theorem map_id [DecidableEq A] [DecidableEq B]
    (ρ : Matrix (A × B) (A × B) ℂ) : (id A B).map ρ = ρ := by
  simp [id, map_single]

/-- Complete positivity does not require any normalization hypothesis. -/
theorem isKrausCP_map [DecidableEq A] [DecidableEq B]
    [DecidableEq Aout] [DecidableEq Bout] (S : SeparableOperation A B Aout Bout) :
    IsKrausCP S.map :=
  Matrix.rectangularKrausMap_isKrausCP S.toKrausFamily.op

variable [DecidableEq A] [DecidableEq B]

/-- Trace preservation is an additional condition on the product-Kraus presentation. -/
def IsTP (S : SeparableOperation A B Aout Bout) : Prop := S.toKrausFamily.IsTP

/-- Physical postselection branches additionally satisfy trace nonincrease. -/
def IsTraceNonincreasing (S : SeparableOperation A B Aout Bout) : Prop :=
  S.toKrausFamily.IsTraceNonincreasing

omit [Fintype A] [Fintype B] in
/-- A channel is also an admissible trace-nonincreasing branch. -/
theorem IsTP.isTraceNonincreasing {S : SeparableOperation A B Aout Bout} (h : S.IsTP) :
    S.IsTraceNonincreasing := KrausFamily.IsTP.isTraceNonincreasing h

/-- Trace preservation for normalized presentations. -/
theorem trace_map {S : SeparableOperation A B Aout Bout} (h : S.IsTP)
    (ρ : Matrix (A × B) (A × B) ℂ) : (S.map ρ).trace = ρ.trace :=
  KrausFamily.trace_map h ρ

open scoped ComplexOrder MatrixOrder in
/-- A physical branch decreases trace on positive semidefinite inputs. -/
theorem trace_map_le {S : SeparableOperation A B Aout Bout} (h : S.IsTraceNonincreasing)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) :
    (S.map ρ).trace ≤ ρ.trace :=
  KrausFamily.trace_map_le h hρ

end Map

section Composition

variable {Amid Bmid : Type}
variable [Fintype Amid] [Fintype Bmid]

/-- Sequential composition, with paired outcomes (later, earlier) and local matrix products. -/
def comp (T : SeparableOperation Amid Bmid Aout Bout)
    (S : SeparableOperation A B Amid Bmid) : SeparableOperation A B Aout Bout :=
  ⟨T.Index × S.Index, fun i ↦ T.left i.1 * S.left i.2,
    fun i ↦ T.right i.1 * S.right i.2⟩

/-- Product factorization is retained branchwise under composition. -/
theorem toKrausFamily_comp_op (T : SeparableOperation Amid Bmid Aout Bout)
    (S : SeparableOperation A B Amid Bmid) (i : T.Index × S.Index) :
    (T.comp S).toKrausFamily.op i = T.toKrausFamily.op i.1 * S.toKrausFamily.op i.2 := by
  simp only [toKrausFamily_op, comp, mul_kronecker_mul]

variable [Fintype A] [Fintype B] [Fintype Aout] [Fintype Bout]

omit [Fintype Aout] [Fintype Bout] in
/-- The product-Kraus presentation of composition induces sequential application. -/
theorem map_comp (T : SeparableOperation Amid Bmid Aout Bout)
    (S : SeparableOperation A B Amid Bmid)
    (ρ : Matrix (A × B) (A × B) ℂ) : (T.comp S).map ρ = T.map (S.map ρ) := by
  change (∑ i : T.Index × S.Index, _) = _
  rw [Fintype.sum_prod_type]
  simp only [map, KrausFamily.map_apply, toKrausFamily_comp_op,
    Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  rfl

omit [Fintype Aout] [Fintype Bout] in
/-- Composition closure as an equality of linear maps. -/
theorem map_comp_eq (T : SeparableOperation Amid Bmid Aout Bout)
    (S : SeparableOperation A B Amid Bmid) :
    (T.comp S).map = T.map.comp S.map := by
  apply LinearMap.ext
  intro ρ
  exact map_comp T S ρ

end Composition

end SeparableOperation
end QuantumInfo
