/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Kraus.Blocking
import QICLean.Channel.KrausMap.KrausAction
import QICLean.Channel.Irreducible.InvariantProjection

/-!
# Transfer maps of blocked and relabelled families

Blocking a finite family $A = (A_i)_{i}$ at length $L$ replaces it by the family of
products $A_{i_1} \cdots A_{i_L}$ indexed by words of length $L$. Its transfer map is the
$L$-th power $E_A^L$ of the transfer map of $A$, and it is trace-preserving when $A$ is.
Relabelling the index set by a bijection changes neither the transfer map nor trace
preservation.

## Main results

* `Kraus.transferMap_reindexPhysical_equiv`, `Kraus.isTP_reindexPhysical_iff`: relabelling
  by a bijection preserves the transfer map and trace preservation.
* `Kraus.hasInvariantProj_reindexPhysical_equiv`, `Kraus.isIrreducibleFamily_reindexPhysical_equiv`:
  relabelling by a bijection preserves invariant projections and irreducibility.
* `Kraus.sum_evalWord_conjTranspose_mul_evalWord`, `Kraus.IsTP.block`: blocking
  preserves trace preservation.
* `Kraus.transferMap_blockTensor`, `Kraus.transferMap_blockTensor_apply`: the transfer map
  of the blocked family is $E_A^L$.
* `Kraus.transferMap_blockTensor_fixedPoint`: fixed points of $E_A$ are fixed by the
  transfer map of every blocked family.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435.
* J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, arXiv:1606.00608, Section 2.3.
-/

open scoped Matrix BigOperators
open Matrix

namespace Kraus

section Relabel

variable {ι ι' n : Type*} [Fintype ι] [Fintype ι'] [Fintype n] [DecidableEq n]

/-- Relabelling the index set of a finite family by a bijection does not change its
transfer map. -/
theorem transferMap_reindexPhysical_equiv (e : ι' ≃ ι) (A : ι → Matrix n n ℂ) :
    transferMap (reindexPhysical e A) = transferMap A := by
  ext X : 1
  simp only [transferMap_apply, reindexPhysical]
  exact e.sum_comp fun i => A i * X * (A i)ᴴ

/-- Relabelling the index set of a finite family by a bijection preserves trace
preservation $\sum_i A_i^\dagger A_i = 1$. -/
theorem isTP_reindexPhysical_iff (e : ι' ≃ ι) (A : ι → Matrix n n ℂ) :
    IsTP (reindexPhysical e A) ↔ IsTP A := by
  simp only [IsTP, reindexPhysical]
  rw [e.sum_comp fun i => (A i)ᴴ * A i]

end Relabel

section RelabelInvariantProjection

variable {ι ι' n : Type*} [Fintype n] [DecidableEq n]

/-- Relabelling the index set of a finite family by a bijection preserves invariant
projections. -/
theorem hasInvariantProj_reindexPhysical_equiv (e : ι' ≃ ι) (A : ι → Matrix n n ℂ) :
    HasInvariantProj (reindexPhysical e A) ↔ HasInvariantProj A := by
  constructor
  · rintro ⟨P, hPproj, hP0, hP1, hLower⟩
    refine ⟨P, hPproj, hP0, hP1, ?_⟩
    intro i
    simpa [reindexPhysical] using hLower (e.symm i)
  · rintro ⟨P, hPproj, hP0, hP1, hLower⟩
    exact ⟨P, hPproj, hP0, hP1, fun i => hLower (e i)⟩

/-- Relabelling the index set of a finite family by a bijection preserves irreducibility. -/
theorem isIrreducibleFamily_reindexPhysical_equiv (e : ι' ≃ ι) (A : ι → Matrix n n ℂ) :
    IsIrreducibleFamily (reindexPhysical e A) ↔ IsIrreducibleFamily A := by
  rw [IsIrreducibleFamily, IsIrreducibleFamily, hasInvariantProj_reindexPhysical_equiv e A]

end RelabelInvariantProjection

section Blocking

/-- Trace preservation passes from a family to its products along words of every fixed
length: $\sum_{|w| = L} A_w^\dagger A_w = 1$. -/
theorem sum_evalWord_conjTranspose_mul_evalWord {ι n : Type*} [Fintype ι] [Fintype n]
    [DecidableEq n] (A : ι → Matrix n n ℂ) (hA : IsTP A) :
    ∀ L : ℕ,
      ∑ σ : Fin L → ι, (evalWord A (List.ofFn σ))ᴴ * evalWord A (List.ofFn σ) = 1 := by
  classical
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
      unfold IsTP at hA
      rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => ι)).sum_comp, Fintype.sum_prod_type,
        Finset.sum_comm, ← ih]
      refine Finset.sum_congr rfl fun w _ => ?_
      calc
        _ = (evalWord A (List.ofFn w))ᴴ * (∑ j, (A j)ᴴ * A j) * evalWord A (List.ofFn w) := by
          simp [Fin.consEquiv, List.ofFn_succ, conjTranspose_mul, Finset.mul_sum,
            Finset.sum_mul, Matrix.mul_assoc]
        _ = _ := by rw [hA, Matrix.mul_one]

variable {d : ℕ} {n : Type*} [Fintype n] [DecidableEq n]

/-- Blocking at any length preserves trace preservation. -/
theorem IsTP.block {ι : Type*} [Fintype ι] {A : ι → Matrix n n ℂ} (hA : IsTP A) (L : ℕ) :
    IsTP (Kraus.block A L) :=
  sum_evalWord_conjTranspose_mul_evalWord A hA L

/-- The transfer map of the family blocked at length `L` is the `L`-th power of the
transfer map. -/
theorem transferMap_blockTensor (A : Fin d → Matrix n n ℂ) (L : ℕ) :
    transferMap (blockTensor A L) = transferMap A ^ L := by
  rw [blockTensor, transferMap_reindexPhysical_equiv, transferMap_block]

/-- The transfer map of the family blocked at length `L` is the `L`-th power of the
transfer map, applied to a matrix. -/
theorem transferMap_blockTensor_apply (A : Fin d → Matrix n n ℂ) (L : ℕ)
    (X : Matrix n n ℂ) :
    transferMap (blockTensor A L) X = (transferMap A ^ L) X := by
  rw [transferMap_blockTensor]

/-- A fixed point of the transfer map is a fixed point of the transfer map of every
blocked family. -/
theorem transferMap_blockTensor_fixedPoint (A : Fin d → Matrix n n ℂ) (L : ℕ)
    (X : Matrix n n ℂ) (hX : transferMap A X = X) :
    transferMap (blockTensor A L) X = X := by
  rw [transferMap_blockTensor_apply, Module.End.pow_apply, Function.iterate_fixed hX]

end Blocking

end Kraus
