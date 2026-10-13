/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.KroneckerFactorPositivity

/-!
# Order of finite Kronecker products

Tensoring with a positive semidefinite matrix preserves matrix order on either
side. This gives a two-factor comparison and, by induction, monotonicity of
finite Kronecker products whose lower factors are positive semidefinite.
The finite factors may have different, possibly empty, index types, and the
number of factors may be zero.

The two-factor comparison also applies when the lower first factor is
indefinite, as needed for the scalar bound in `Entropy.RestoringNorm`.

## References

The finite comparison is the tensor-order step in OpenAI,
*A two-dimensional area law from a global spectral gap*, September 24, 2026,
`07-comparators.tex`, proof of `comparator:sharp-upper`, lines 405–412,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped ComplexOrder MatrixOrder

/-- Kronecker products preserve the two factor comparisons when the fixed
upper first factor and fixed lower second factor are positive semidefinite.
The lower first factor need not be positive semidefinite. -/
theorem Matrix.kronecker_mono_of_posSemidef
    {m n : Type*} [Finite m] [Finite n]
    {A B : Matrix m m ℂ} {C D : Matrix n n ℂ}
    (hAB : A ≤ B) (hCD : C ≤ D) (hB : B.PosSemidef) (hC : C.PosSemidef) :
    Matrix.kronecker A C ≤ Matrix.kronecker B D := by
  exact
    (OrderHomClass.monotone
      (PositiveLinearMap.mk₀
        ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)
          (l := m) (m := m) (n := n) (p := n)).flip C)
        (fun X hX ↦ ((Matrix.nonneg_iff_posSemidef.mp hX).kronecker hC).nonneg))
      hAB).trans
      (OrderHomClass.monotone
        (PositiveLinearMap.mk₀
          ((Matrix.kroneckerBilinear (R := ℂ) (α := ℂ)
            (l := m) (m := m) (n := n) (p := n)) B)
          (fun X hX ↦ (hB.kronecker (Matrix.nonneg_iff_posSemidef.mp hX)).nonneg))
        hCD)

/-- Finite Kronecker products preserve positive-semidefinite order when
every lower factor is positive semidefinite. The factors may have different
finite index types, including empty types; the number of factors may be zero.

This is the tensor-order step used to pass from one-copy selected-marginal
domination to independent copies in the September 24, 2026 area-law
manuscript, `07-comparators.tex`, proof of `comparator:sharp-upper`.
-/
theorem Matrix.finKronecker_mono
    {N : ℕ} {I : Fin N → Type*} [∀ i, Fintype (I i)]
    (A B : (i : Fin N) → Matrix (I i) (I i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hAB : ∀ i, A i ≤ B i) :
    Matrix.finKronecker A ≤ Matrix.finKronecker B := by
  revert I
  induction N
  case succ N ih =>
    intro I _ A B hA hAB
    have htail := ih (Fin.tail A) (Fin.tail B)
      (fun i ↦ hA i.succ) (fun i ↦ hAB i.succ)
    have htailPSD := Matrix.finKronecker_posSemidef
      (Fin.tail A) (fun i ↦ hA i.succ)
    have hB₀ : (B 0).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp ((hA 0).nonneg.trans (hAB 0))
    have heq (M : (i : Fin (N + 1)) → Matrix (I i) (I i) ℂ) :
        (Matrix.finKronecker M).submatrix (Fin.consEquiv I) (Fin.consEquiv I) =
          Matrix.kronecker (M 0) (Matrix.finKronecker (Fin.tail M)) := by
      ext ⟨a, x⟩ ⟨b, y⟩
      rw [Matrix.submatrix_apply, Matrix.finKronecker_apply,
        Matrix.kronecker, Matrix.kroneckerMap_apply, Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ, Matrix.finKronecker_apply, Fin.tail]
    rw [Matrix.le_iff,
      ← Matrix.posSemidef_submatrix_equiv
        (M := Matrix.finKronecker B - Matrix.finKronecker A) (Fin.consEquiv I),
      Matrix.submatrix_sub, Pi.sub_apply, Pi.sub_apply, heq B, heq A, ← Matrix.le_iff]
    exact Matrix.kronecker_mono_of_posSemidef (hAB 0) htail hB₀ htailPSD
  case zero =>
    intro I _ A B _ _
    exact le_of_eq (congrArg Matrix.finKronecker (Subsingleton.elim A B))
