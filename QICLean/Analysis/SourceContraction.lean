/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Multilinear.Basic
import QICLean.Analysis.RectangularTraceNormAlgebra

/-!
# Corrected-position expansion of a finite source contraction

An actual finite coefficient contraction is multilinear in its rectangular source
matrices. Replacing sources by exact sources plus corrections therefore expands
over subsets of source positions. The empty subset is the exact contraction.
Branch choices are fixed coefficient data; they do not change the position set.

The coefficient array is supplied data. Identifying it with an actual distributed
circuit and proving the dimension-free separated error estimate remain separate
obligations. No norm bound on that array is assumed or asserted here.

Mathematical source: polynomial PEPS manuscript, September 24, 2026, Theorem 5.2,
the corrected-position expansion in Section 5. No upstream Lean proof text reused.
-/

open scoped BigOperators

namespace Matrix

variable {P : Type*} [Fintype P] [DecidableEq P] {R C : P → Type*}
  [∀ p, Fintype (R p)] [∀ p, Fintype (C p)] {m n : Type*}

/-- Contract a finite coefficient array with all source entries. Each source position
has its own arbitrary rectangular row and column spaces. -/
noncomputable def sourceContraction
    (coeff : ((p : P) → R p × C p) → Matrix m n ℂ) :
    MultilinearMap ℂ (fun p => Matrix (R p) (C p) ℂ) (Matrix m n ℂ) :=
  ∑ x, ((MultilinearMap.mkPiAlgebra ℂ P ℂ).compLinearMap fun p =>
    { toFun := fun X => X (x p).1 (x p).2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).smulRight (coeff x)

/-- The construction evaluates to the literal sum of products of source entries. -/
theorem sourceContraction_apply
    (coeff : ((p : P) → R p × C p) → Matrix m n ℂ)
    (X : (p : P) → Matrix (R p) (C p) ℂ) :
    sourceContraction coeff X = ∑ x, (∏ p, X p (x p).1 (x p).2) • coeff x := by
  simp only [sourceContraction, _root_.sum_apply, MultilinearMap.smulRight_apply,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  rfl

/-- Entrywise form of the actual contraction; the coefficients are deterministic. -/
theorem sourceContraction_apply_apply
    (coeff : ((p : P) → R p × C p) → Matrix m n ℂ)
    (X : (p : P) → Matrix (R p) (C p) ℂ) (a : m) (b : n) :
    sourceContraction coeff X a b =
      ∑ x, coeff x a b * ∏ p, X p (x p).1 (x p).2 := by
  rw [sourceContraction_apply]
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  change (∏ p, X p (x p).1 (x p).2) * coeff x a b =
    coeff x a b * (∏ p, X p (x p).1 (x p).2)
  exact mul_comm _ _

/-- Expand corrections at a specified finite set of positions, leaving every other
source exact. This is an identity of actual matrix contractions. -/
theorem sourceContraction_piecewise_add
    (coeff : ((p : P) → R p × C p) → Matrix m n ℂ)
    (X E : (p : P) → Matrix (R p) (C p) ℂ) (T : Finset P) :
    sourceContraction coeff (T.piecewise (E + X) X) =
      ∑ S ∈ T.powerset, sourceContraction coeff (S.piecewise E X) :=
  (sourceContraction coeff).map_piecewise_add E X T

/-- Replacing every source by an exact source plus a correction expands over the
subsets of positions, independently of the number of branch labels. -/
theorem sourceContraction_add
    (coeff : ((p : P) → R p × C p) → Matrix m n ℂ)
    (X E : (p : P) → Matrix (R p) (C p) ℂ) :
    sourceContraction coeff (E + X) =
      ∑ S : Finset P, sourceContraction coeff (S.piecewise E X) :=
  (sourceContraction coeff).map_add_univ E X

/-- Subtracting the exact contraction removes exactly the empty correction subset. -/
theorem sourceContraction_piecewise_sub
    (coeff : ((p : P) → R p × C p) → Matrix m n ℂ)
    (X E : (p : P) → Matrix (R p) (C p) ℂ) (T : Finset P) :
    sourceContraction coeff (T.piecewise (E + X) X) - sourceContraction coeff X =
      ∑ S ∈ T.powerset.erase ∅, sourceContraction coeff (S.piecewise E X) := by
  classical
  rw [sourceContraction_piecewise_add]
  simp

/-- The complete sampled-minus-exact contraction is its nonempty-position expansion. -/
theorem sourceContraction_sub
    (coeff : ((p : P) → R p × C p) → Matrix m n ℂ)
    (X E : (p : P) → Matrix (R p) (C p) ℂ) :
    sourceContraction coeff (E + X) - sourceContraction coeff X =
      ∑ S ∈ (Finset.univ : Finset (Finset P)).erase ∅,
        sourceContraction coeff (S.piecewise E X) := by
  simpa using sourceContraction_piecewise_sub coeff X E Finset.univ

variable [Fintype m] [Fintype n] [DecidableEq n]

/-- Bound the actual error by the nuclear errors of its nonempty-position terms;
the matrices may be rectangular, non-Hermitian and nonpositive. -/
theorem rectangularTraceNorm_sourceContraction_sub_le
    (coeff : ((p : P) → R p × C p) → Matrix m n ℂ)
    (X E : (p : P) → Matrix (R p) (C p) ℂ) :
    rectangularTraceNorm (sourceContraction coeff (E + X) - sourceContraction coeff X) ≤
      ∑ S ∈ (Finset.univ : Finset (Finset P)).erase ∅,
        rectangularTraceNorm (sourceContraction coeff (S.piecewise E X)) := by
  rw [sourceContraction_sub]
  exact rectangularTraceNorm_sum_le _ _

end Matrix
