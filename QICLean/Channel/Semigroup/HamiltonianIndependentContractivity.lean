/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Semigroup.RelaxationConditions
import QICLean.Channel.Semigroup.LindbladForm.GKSLTheorem
import QICLean.Channel.Semigroup.ReducibleQDS.Equivalence

/-!
# Algebraic companion to the Hamiltonian-independent contractivity conjecture

This file kernel-checks algebraic and finite-dimensional pieces surrounding the
conjecture posed by Wolff--Malz--Trivedi, arXiv:2602.16067v1, Section "Outlook
and open questions", lines 853--855 of the source.  It does **not** formalize or
claim the full analytic Hamiltonian-independent contractivity conjecture.

The invariant-subspace statements below formalize the Outlook observation on
source line 855: full adjoint-free jump algebra generation makes every frozen
driven Lindbladian irreducible.  The explicit four-dimensional computation is
relevant to the trace-norm right-derivative formula of Proposition 19 (source
lines 615--635): full generation does not by itself make every instantaneous
witness strictly decreasing.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace
open Matrix Finset Module

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Full adjoint-free jump generation leaves no nontrivial orthogonal
projection invariant under every jump.  This is the algebraic mechanism behind
the frozen-Hamiltonian observation in arXiv:2602.16067v1, Outlook, lines
853--855. -/
theorem full_jump_algebra_projection_eq_zero_or_one
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ (Set.range F.L) = ⊤)
    (P : Mat) (hP : IsOrthogonalProjection P)
    (hInv : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0) :
    P = 0 ∨ P = 1 := by
  have hAdjoin : ∀ A : Mat, A ∈ Algebra.adjoin ℂ (Set.range F.L) →
      (1 - P) * A * P = 0 := by
    apply lower_left_block_vanishes_on_adjoin hP
    rintro A ⟨j, rfl⟩
    exact hInv j
  apply proj_zero_or_one_of_sandwich P
  intro A
  exact hAdjoin A (hGen ▸ Algebra.mem_top)

/-- Full generation by the jumps alone excludes a block-upper-triangular
Lindblad decomposition for every choice of the frozen Hamiltonian encoded in
`F`.  Compare arXiv:2602.16067v1, Outlook, line 855. -/
theorem full_jump_algebra_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ (Set.range F.L) = ⊤) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  apply full_algebra_generation_implies_no_blockUpperTriangular F
  apply top_unique
  rw [← hGen]
  exact Algebra.adjoin_mono Set.subset_union_left

namespace HICFourDimensionalExample

abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ

/-- The standard matrix unit $E_{ij}$, with zero-based Lean indices. -/
def e (i j : Fin 4) : Mat4 := Matrix.single i j 1

/-- $A=E_{21}+E_{32}+E_{14}$ in one-based mathematical notation. -/
def A : Mat4 := e 1 0 + e 2 1 + e 0 3

/-- $B=E_{43}$ in one-based mathematical notation. -/
def B : Mat4 := e 3 2

private lemma A_cube : A ^ 3 = e 2 3 := by
  simp [A, e, pow_succ, Matrix.mul_add, Matrix.add_mul]

/-- The traceless Hermitian witness $x=E_{11}-E_{33}$. -/
def x : Mat4 := e 0 0 - e 2 2

end HICFourDimensionalExample

end
