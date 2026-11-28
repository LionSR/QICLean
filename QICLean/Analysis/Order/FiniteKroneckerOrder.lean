/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Kronecker.KroneckerFactorPositivity

/-!
# Order of finite Kronecker products

Tensoring with a positive semidefinite matrix preserves matrix order on either
side. This gives a two-factor comparison and, by induction, monotonicity of
finite Kronecker products whose lower factors are positive semidefinite.
The finite factors may have different, possibly empty, index types, and the
number of factors may be zero. `Matrix.prod_le_one_of_injective` applies the comparison to
positive contractions restricted along an injective map of configuration bases.

The two-factor comparison also applies when the lower first factor is
indefinite, as needed for the scalar bound in `Entropy.RestoringNorm`.

Two-sided PSD domination is also stable under tensor products, without
positivity of the dominated factors. The binary and finite results
are stated in terms of positivity of both the sum and the difference.

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
theorem Matrix.piKronecker_mono
    {N : ℕ} {I : Fin N → Type*} [∀ i, Finite (I i)]
    (A B : (i : Fin N) → Matrix (I i) (I i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hAB : ∀ i, A i ≤ B i) :
    Matrix.piKronecker A ≤ Matrix.piKronecker B := by
  revert I
  induction N
  case succ N ih =>
    intro I _ A B hA hAB
    have htail := ih (Fin.tail A) (Fin.tail B)
      (fun i ↦ hA i.succ) (fun i ↦ hAB i.succ)
    have htailPSD := Matrix.piKronecker_posSemidef
      (Fin.tail A) (fun i ↦ hA i.succ)
    have hB₀ : (B 0).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp ((hA 0).nonneg.trans (hAB 0))
    rw [Matrix.le_iff,
      ← Matrix.posSemidef_submatrix_equiv
        (M := Matrix.piKronecker B - Matrix.piKronecker A) (Fin.consEquiv I),
      Matrix.submatrix_sub, Pi.sub_apply, Pi.sub_apply, Matrix.piKronecker_submatrix_cons,
      Matrix.piKronecker_submatrix_cons, ← Matrix.le_iff]
    exact Matrix.kronecker_mono_of_posSemidef (hAB 0) htail hB₀ htailPSD
  case zero =>
    intro I _ A B _ _
    exact le_of_eq (congrArg Matrix.piKronecker (Subsingleton.elim A B))

/-- A product of positive contractions, pulled back along an injective configuration map,
is a positive contraction. Empty factors and empty index types are allowed. -/
theorem Matrix.prod_le_one_of_injective
    {B α : Type*} [Fintype B] [Finite α] [DecidableEq α]
    {I : B → Type*} [∀ b, Finite (I b)] [∀ b, DecidableEq (I b)]
    (A : (b : B) → Matrix (I b) (I b) ℂ)
    (hA : ∀ b, (A b).PosSemidef) (hAle : ∀ b, A b ≤ 1)
    (f : α → ((b : B) → I b)) (hf : Function.Injective f) :
    (Matrix.of fun x y ↦ ∏ b, A b (f x b) (f y b)) ≤ 1 := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let (b : B) : Fintype (I b) := Fintype.ofFinite (I b)
  let e := Fintype.equivFin B
  let g : α → ((i : Fin (Fintype.card B)) → I (e.symm i)) := fun x i ↦ f x (e.symm i)
  have hg : Function.Injective g := by
    intro x y h
    apply hf
    funext b
    obtain ⟨i, rfl⟩ := e.symm.surjective b
    exact congrFun h i
  have h := Matrix.piKronecker_mono (fun i ↦ A (e.symm i)) (fun _ ↦ 1)
    (fun i ↦ hA (e.symm i)) (fun i ↦ hAle (e.symm i))
  have hs := (Matrix.le_iff.mp h).submatrix g
  apply Matrix.le_iff.mpr
  convert hs using 1
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.piKronecker_apply, Matrix.of_apply]
  have hp : (∏ i, A (e.symm i) (g x i) (g y i)) = ∏ b, A b (f x b) (f y b) :=
    e.symm.prod_comp (fun b ↦ A b (f x b) (f y b))
  rw [hp]
  congr 1
  simp only [Matrix.one_apply]
  by_cases hxy : x = y
  · simp [hxy]
  · have hne : g x ≠ g y := fun h ↦ hxy (hg h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    simp only [hxy, ↓reduceIte]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm

/-- Two-sided PSD domination is stable under a binary Kronecker product.
Neither `B` nor `D` is required to be PSD. The conclusions are averages of
same-sign and opposite-sign products of A ± B and C ± D, respectively. -/
theorem Matrix.kronecker_add_sub_posSemidef
    {m n : Type*} [Finite m] [Finite n]
    {A B : Matrix m m ℂ} {C D : Matrix n n ℂ}
    (hABadd : (A + B).PosSemidef) (hABsub : (A - B).PosSemidef)
    (hCDadd : (C + D).PosSemidef) (hCDsub : (C - D).PosSemidef) :
    (Matrix.kronecker A C + Matrix.kronecker B D).PosSemidef ∧
      (Matrix.kronecker A C - Matrix.kronecker B D).PosSemidef := by
  have half : (0 : ℂ) ≤ 1 / 2 := by
    rw [Complex.nonneg_iff]
    norm_num
  constructor
  · convert ((hABadd.kronecker hCDadd).add
      (hABsub.kronecker hCDsub)).smul half using 1
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply,
        Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring
  · convert ((hABadd.kronecker hCDsub).add
      (hABsub.kronecker hCDadd)).smul half using 1
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply,
        Matrix.kronecker, Matrix.kroneckerMap_apply]
    ring

/-- Two-sided PSD domination is stable under finite heterogeneous Kronecker
products. The number of factors may be zero and each finite local basis may
be empty. The dominated factors need not be PSD.

This generalizes arXiv:2611.34921, Lemma 4 (lem:reverse), proof item (iii):
simultaneous induction on both signs replaces the expansion over sign strings. -/
theorem Matrix.piKronecker_add_sub_posSemidef
    {N : ℕ} {I : Fin N → Type*} [∀ i, Finite (I i)]
    (A B : (i : Fin N) → Matrix (I i) (I i) ℂ)
    (hadd : ∀ i, (A i + B i).PosSemidef)
    (hsub : ∀ i, (A i - B i).PosSemidef) :
    (Matrix.piKronecker A + Matrix.piKronecker B).PosSemidef ∧
      (Matrix.piKronecker A - Matrix.piKronecker B).PosSemidef := by
  revert I
  induction N with
  | zero =>
    intro I _ A B _ _
    have hEq : Matrix.piKronecker B = Matrix.piKronecker A :=
      congrArg Matrix.piKronecker (Subsingleton.elim B A)
    have hpos := Matrix.piKronecker_posSemidef A (fun i ↦ Fin.elim0 i)
    rw [hEq, sub_self]
    exact ⟨hpos.add hpos, Matrix.PosSemidef.zero⟩
  | succ N ih =>
    intro I _ A B hadd hsub
    obtain ⟨htadd, htsub⟩ := ih (Fin.tail A) (Fin.tail B)
      (fun i ↦ hadd i.succ) (fun i ↦ hsub i.succ)
    have h := Matrix.kronecker_add_sub_posSemidef (hadd 0) (hsub 0) htadd htsub
    constructor
    · rw [← Matrix.posSemidef_submatrix_equiv
        (M := Matrix.piKronecker A + Matrix.piKronecker B) (Fin.consEquiv I),
        Matrix.submatrix_add, Pi.add_apply, Pi.add_apply, Matrix.piKronecker_submatrix_cons,
        Matrix.piKronecker_submatrix_cons]
      exact h.1
    · rw [← Matrix.posSemidef_submatrix_equiv
        (M := Matrix.piKronecker A - Matrix.piKronecker B) (Fin.consEquiv I),
        Matrix.submatrix_sub, Pi.sub_apply, Pi.sub_apply, Matrix.piKronecker_submatrix_cons,
        Matrix.piKronecker_submatrix_cons]
      exact h.2

/-- Tensor-copy specialization of two-sided PSD domination, including zero copies. -/
theorem Matrix.piKronecker_const_add_sub_posSemidef
    {n : Type*} [Finite n] (N : ℕ) {A B : Matrix n n ℂ}
    (hadd : (A + B).PosSemidef) (hsub : (A - B).PosSemidef) :
    (Matrix.piKronecker (fun _ : Fin N ↦ A) +
      Matrix.piKronecker (fun _ : Fin N ↦ B)).PosSemidef ∧
    (Matrix.piKronecker (fun _ : Fin N ↦ A) -
      Matrix.piKronecker (fun _ : Fin N ↦ B)).PosSemidef :=
  Matrix.piKronecker_add_sub_posSemidef _ _ (fun _ ↦ hadd) (fun _ ↦ hsub)
