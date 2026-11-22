/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Real orthogonal complex structures and the skew-orthogonal normal form

An isometry `J` with `J (J x) = -x` is skew-adjoint. Every unit vector `x`
therefore gives an orthonormal pair `![x, -J x]`. Its span and orthogonal
complement are invariant. In this order the action on the pair is the matrix
`!![0, 1; -1, 0]`, rather than its negative.

The matrix dictionary below identifies interleaved copies of that matrix with
the negative of Mathlib's split-index `Matrix.J`. These are ingredients for
the real skew-unitary normal form used in CPSV17.

A real linear isometry whose square is minus the identity then admits an
orthonormal basis in pairs `x, -J x` (`LinearIsometry.exists_paired_orthonormalBasis`), and a
real orthogonal skew-symmetric matrix is orthogonally congruent to the interleaved normal form
(`Matrix.exists_orthogonal_congruence_interleavedSkewForm`).

## References

* Cirac, Pérez-García, Schuch and Verstraete, arXiv:1703.09188, proof of
  `corconj`, lines 1129–1140. That passage asserts the orthogonal normal form;
  it does not supply the invariant-plane construction proved here.

Moved from TNLean, `TNLean/Algebra/OrthogonalComplexStructure.lean`,
`TNLean/Algebra/OrthogonalComplexStructureBasis.lean` and
`TNLean/Algebra/OrthogonalSkewNormalForm.lean` at commit `49b78ed821` (Apache-2.0),
merged into one file.
-/

open scoped InnerProductSpace Matrix Kronecker

namespace LinearIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A real isometry whose square is minus the identity is skew-adjoint. -/
theorem inner_right_eq_neg_inner_left_of_sq_eq_neg
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = -x) (x y : E) :
    ⟪x, J y⟫_ℝ = -⟪J x, y⟫_ℝ := by
  calc
    ⟪x, J y⟫_ℝ = ⟪J x, J (J y)⟫_ℝ := (J.inner_map_map x (J y)).symm
    _ = -⟪J x, y⟫_ℝ := by rw [hJ, inner_neg_right]

/-- A vector is orthogonal to its image under a real isometry squaring to minus one. -/
theorem inner_self_apply_eq_zero_of_sq_eq_neg
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = -x) (x : E) :
    ⟪x, J x⟫_ℝ = 0 := by
  have h := J.inner_right_eq_neg_inner_left_of_sq_eq_neg hJ x x
  rw [real_inner_comm x (J x)] at h
  linarith

/-- The ordered pair `x, -J x` has the orientation of the source matrix
`!![0, 1; -1, 0]`. -/
theorem orthonormal_pair_of_sq_eq_neg
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = -x) {x : E} (hx : ‖x‖ = 1) :
    Orthonormal ℝ ![x, -J x] := by
  have horth := J.inner_self_apply_eq_zero_of_sq_eq_neg hJ x
  have horth' : ⟪J x, x⟫_ℝ = 0 := (real_inner_comm x (J x)).trans horth
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [horth, horth', inner_self_eq_norm_sq_to_K, hx, J.norm_map]

/-- The columns of `!![0, 1; -1, 0]` give the action in the ordered pair
`x, -J x`, including the source's sign convention. -/
theorem apply_pair_eq_standardSkew_sum
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = -x) (x : E) (i : Fin 2) :
    J (![x, -J x] i) =
      ∑ k : Fin 2, (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) k i •
        ![x, -J x] k := by
  fin_cases i <;> simp [Fin.sum_univ_two, hJ]

/-- The span of the pair `x, -J x` is invariant under `J`; no normalization of
`x` is needed for invariance. -/
theorem mapsTo_span_pair_of_sq_eq_neg
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = -x) (x : E) :
    Set.MapsTo J (Submodule.span ℝ (Set.range ![x, -J x]))
      (Submodule.span ℝ (Set.range ![x, -J x])) := by
  let W := Submodule.span ℝ (Set.range ![x, -J x])
  change W ≤ W.comap J.toLinearMap
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change J (![x, -J x] i) ∈ W
  fin_cases i
  · change J x ∈ W
    have hmem : -J x ∈ W := Submodule.subset_span ⟨1, rfl⟩
    simpa using W.neg_mem hmem
  · change J (-J x) ∈ W
    rw [map_neg, hJ, neg_neg]
    exact Submodule.subset_span ⟨0, rfl⟩

/-- The orthogonal complement of a `J`-invariant subspace is again invariant. -/
theorem mapsTo_orthogonal_of_sq_eq_neg
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = -x)
    (W : Submodule ℝ E) (hW : Set.MapsTo J W W) :
    Set.MapsTo J Wᗮ Wᗮ := by
  intro x hx
  apply (W.mem_orthogonal (J x)).mpr
  intro y hy
  rw [J.inner_right_eq_neg_inner_left_of_sq_eq_neg hJ y x]
  exact neg_eq_zero.mpr ((W.mem_orthogonal x).mp hx (J y) (hW hy))

/-- Restrict a real isometry squaring to minus one to the orthogonal complement
of an invariant subspace. This is the operator needed for dimension induction. -/
def restrictInvariantOrthogonal
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = -x)
    (W : Submodule ℝ E) (hW : Set.MapsTo J W W) : Wᗮ →ₗᵢ[ℝ] Wᗮ where
  toFun x := ⟨J x, J.mapsTo_orthogonal_of_sq_eq_neg hJ W hW x.property⟩
  map_add' x y := Subtype.ext (map_add J (x : E) (y : E))
  map_smul' c x := Subtype.ext (map_smul J c (x : E))
  norm_map' x := J.norm_map (x : E)

/-- The restricted isometry retains the square-minus-one identity. -/
theorem restrictInvariantOrthogonal_sq
    (J : E →ₗᵢ[ℝ] E) (hJ : ∀ x, J (J x) = -x)
    (W : Submodule ℝ E) (hW : Set.MapsTo J W W) (x : Wᗮ) :
    J.restrictInvariantOrthogonal hJ W hW
      (J.restrictInvariantOrthogonal hJ W hW x) = -x := by
  apply Subtype.ext
  exact hJ x

end LinearIsometry

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real skew-symmetric orthogonal matrix squares to minus the identity. -/
theorem mul_self_eq_neg_one_of_orthogonal_of_transpose_eq_neg
    {A : Matrix ι ι ℝ} (hA : A ∈ orthogonalGroup ι ℝ) (hskew : Aᵀ = -A) :
    A * A = -1 := by
  have h := (mem_orthogonalGroup_iff _ _).mp hA
  rw [hskew, mul_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- The actual Euclidean action of a real orthogonal matrix, bundled as a
linear isometry through Mathlib's matrix-to-operator star algebra equivalence. -/
noncomputable def orthogonalLinearIsometry
    (A : Matrix ι ι ℝ) (hA : A ∈ orthogonalGroup ι ℝ) :
    EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  (Matrix.toEuclideanLin A).isometryOfInner fun x y ↦
    ContinuousLinearMap.inner_map_map_of_mem_unitary
      (Unitary.map_mem (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) hA) x y

/-- The bundled isometry is the original matrix action, not a separate model. -/
@[simp] theorem orthogonalLinearIsometry_apply
    (A : Matrix ι ι ℝ) (hA : A ∈ orthogonalGroup ι ℝ) (x : EuclideanSpace ℝ ι) :
    orthogonalLinearIsometry A hA x = Matrix.toEuclideanLin A x :=
  rfl

/-- The Euclidean isometry of a real skew-orthogonal matrix squares to minus
the identity, supplying the hypotheses of the invariant-plane construction. -/
theorem orthogonalLinearIsometry_sq
    {A : Matrix ι ι ℝ} (hA : A ∈ orthogonalGroup ι ℝ) (hskew : Aᵀ = -A)
    (x : EuclideanSpace ℝ ι) :
    orthogonalLinearIsometry A hA (orthogonalLinearIsometry A hA x) = -x := by
  change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A)
    ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A) x) = -x
  have h := congrArg
    (fun M : Matrix ι ι ℝ ↦ Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) M x)
    (mul_self_eq_neg_one_of_orthogonal_of_transpose_eq_neg hA hskew)
  simpa only [map_mul, map_neg, map_one, mul_apply_eq_comp,
    _root_.neg_apply, one_apply_eq_self] using h

/-- One copy of the source's `Y` for every finite index, in paired coordinates. -/
def interleavedSkewForm (ι : Type*) [DecidableEq ι] :
    Matrix (ι × Fin 2) (ι × Fin 2) ℝ :=
  (1 : Matrix ι ι ℝ) ⊗ₖ !![0, 1; -1, 0]

/-- Paired coordinates `(i,0),(i,1)` correspond to the two copies of `i` in
Mathlib's split-index symplectic matrix. -/
def pairedSkewIndexEquiv (ι : Type*) : ι × Fin 2 ≃ ι ⊕ ι where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun
    | Sum.inl i => (i, 0)
    | Sum.inr i => (i, 1)
  left_inv p := by rcases p with ⟨i, a⟩; fin_cases a <;> rfl
  right_inv p := by cases p <;> rfl

omit [Fintype ι] in
/-- The paper's interleaved `Y` form is the reindexing of **minus** Mathlib's
`J`. The minus sign fixes the opposite orientation of the two conventions. -/
theorem interleavedSkewForm_eq_neg_J_submatrix :
    interleavedSkewForm ι =
      (-J ι ℝ).submatrix (pairedSkewIndexEquiv ι) (pairedSkewIndexEquiv ι) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [interleavedSkewForm, pairedSkewIndexEquiv, J]

/-- The paired-coordinate order transported to the paper's `Fin (2*m)` index. -/
def interleavedSkewFinEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))

/-- The source's standard skew form on `Fin (2*m)`, retaining the interleaved
ordering rather than the split ordering of Mathlib's `J`. -/
def interleavedSkewFormFin (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  Matrix.reindex (interleavedSkewFinEquiv m) (interleavedSkewFinEquiv m)
    (interleavedSkewForm (Fin m))

/-- The finite reindexing preserves each ordered `Y` block. -/
theorem interleavedSkewFormFin_apply (m : ℕ) (i j : Fin m × Fin 2) :
    interleavedSkewFormFin m (interleavedSkewFinEquiv m i)
      (interleavedSkewFinEquiv m j) = interleavedSkewForm (Fin m) i j := by
  simp [interleavedSkewFormFin, Matrix.reindex_apply]

end Matrix

/-!
## Paired orthonormal bases for real orthogonal complex structures

A real linear isometry whose square is minus the identity admits an
orthonormal basis in pairs `x, -J x`. The proof removes the invariant plane
generated by a unit vector and applies induction to its orthogonal complement.
Thus the action on every ordered pair is `!![0, 1; -1, 0]`.

## References

* Cirac, Pérez-García, Schuch and Verstraete, arXiv:1703.09188, proof of
  `corconj`, lines 1129–1140: the real skew-unitary orthogonal normal form.
  The paired basis below proves the existence needed for that normal form.
-/

open scoped InnerProductSpace Matrix

namespace LinearIsometry

universe u

/-- A real orthogonal complex structure in dimension `2*m` admits an
orthonormal basis on which each ordered pair has action `!![0, 1; -1, 0]`.
This supplies the basis-existence step in arXiv:1703.09188, proof of `corconj`,
lines 1129–1140. No paired basis or invariant decomposition is assumed. -/
theorem exists_paired_orthonormalBasis (m : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (J : E →ₗᵢ[ℝ] E)
      (_hJ : ∀ x, J (J x) = -x) (_hdim : Module.finrank ℝ E = 2 * m),
      ∃ B : OrthonormalBasis (Fin m × Fin 2) ℝ E,
        ∀ i, J (B (i, 0)) = -B (i, 1) ∧ J (B (i, 1)) = B (i, 0) := by
  classical
  induction m with
  | zero =>
      intro E _ _ _ J hJ hdim
      let v : Fin 0 × Fin 2 → E := fun p ↦ Fin.elim0 p.1
      have hv : Orthonormal ℝ v := by
        rw [orthonormal_iff_ite]
        intro i
        exact Fin.elim0 i.1
      have hspan := hv.linearIndependent.span_eq_top_of_card_eq_finrank'
        (by simpa using hdim.symm)
      refine ⟨OrthonormalBasis.mk hv hspan.ge, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ m ih =>
      intro E _ _ _ J hJ hdim
      let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
      obtain ⟨x, hx⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
      let w : Fin 2 → E := ![x, -J x]
      have hw : Orthonormal ℝ w := J.orthonormal_pair_of_sq_eq_neg hJ hx
      let W : Submodule ℝ E := Submodule.span ℝ (Set.range w)
      have hWdim : Module.finrank ℝ W = 2 := by
        simpa only [W, Fintype.card_fin] using finrank_span_eq_card hw.linearIndependent
      have hperp : Module.finrank ℝ Wᗮ = 2 * m := by
        have h := W.finrank_add_finrank_orthogonal
        rw [hWdim, hdim] at h
        omega
      have hW : Set.MapsTo J W W := J.mapsTo_span_pair_of_sq_eq_neg hJ x
      let J' := J.restrictInvariantOrthogonal hJ W hW
      have hJ' : ∀ z : Wᗮ, J' (J' z) = -z :=
        J.restrictInvariantOrthogonal_sq hJ W hW
      obtain ⟨B, hB⟩ := ih (Wᗮ) J' hJ' hperp
      let v : Fin (m + 1) × Fin 2 → E := fun p ↦
        Fin.cases (w p.2) (fun i ↦ (B (i, p.2) : E)) p.1
      have hwmem (a : Fin 2) : w a ∈ W := Submodule.subset_span ⟨a, rfl⟩
      have hv : Orthonormal ℝ v := by
        rw [orthonormal_iff_ite]
        rintro ⟨i, a⟩ ⟨j, b⟩
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · refine Fin.cases ?_ (fun j ↦ ?_) j
          · simpa [v] using (orthonormal_iff_ite.mp hw a b)
          · change ⟪w a, (B (j, b) : E)⟫_ℝ =
              if ((0 : Fin (m + 1)), a) = (j.succ, b) then 1 else 0
            have hzero : (0 : Fin (m + 1)) ≠ j.succ := (Fin.succ_ne_zero j).symm
            simpa only [Prod.mk.injEq, hzero, false_and, ↓reduceIte] using
              W.inner_right_of_mem_orthogonal (hwmem a) (B (j, b)).property
        · refine Fin.cases ?_ (fun j ↦ ?_) j
          · change ⟪(B (i, a) : E), w b⟫_ℝ =
              if (i.succ, a) = ((0 : Fin (m + 1)), b) then 1 else 0
            simpa only [Prod.mk.injEq, Fin.succ_ne_zero, false_and, ↓reduceIte] using
              W.inner_left_of_mem_orthogonal (hwmem b) (B (i, a)).property
          · change ⟪B (i, a), B (j, b)⟫_ℝ =
              if (i.succ, a) = (j.succ, b) then 1 else 0
            simpa only [Prod.mk.injEq, Fin.succ_inj] using B.inner_eq_ite (i, a) (j, b)
      have hspan := hv.linearIndependent.span_eq_top_of_card_eq_finrank'
        (by simp [hdim, Nat.mul_comm])
      refine ⟨OrthonormalBasis.mk hv hspan.ge, ?_⟩
      simp only [OrthonormalBasis.coe_mk]
      intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simp [v, w, hJ]
      · constructor
        · change J (B (i, 0) : E) = -(B (i, 1) : E)
          exact congrArg Subtype.val (hB i).1
        · change J (B (i, 1) : E) = (B (i, 0) : E)
          exact congrArg Subtype.val (hB i).2

end LinearIsometry

/-!
## Orthogonal congruence of real skew-orthogonal matrices

The paired orthonormal basis of an orthogonal complex structure gives the
source's interleaved normal form, with the exact orientation `Oᵀ * Σ * O = A`.
The construction includes dimension zero and assumes no preselected invariant
planes or paired basis.

## References

* Cirac, Pérez-García, Schuch and Verstraete, arXiv:1703.09188, proof of
  `corconj`, lines 1129–1140.
-/

open scoped InnerProductSpace Matrix Kronecker

namespace Matrix

/-- In an orthonormal paired basis, an orthogonal complex structure has the
source's interleaved `Y` matrix. This is the coordinate computation underlying
arXiv:1703.09188, proof of `corconj`, lines 1129–1140. -/
theorem toMatrix_paired_orthonormalBasis
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J : E →ₗᵢ[ℝ] E) (B : OrthonormalBasis (Fin m × Fin 2) ℝ E)
    (hB : ∀ i, J (B (i, 0)) = -B (i, 1) ∧ J (B (i, 1)) = B (i, 0)) :
    LinearMap.toMatrix (B.reindex (interleavedSkewFinEquiv m)).toBasis
        (B.reindex (interleavedSkewFinEquiv m)).toBasis J.toLinearMap =
      interleavedSkewFormFin m := by
  classical
  ext i j
  obtain ⟨⟨k, a⟩, rfl⟩ := (interleavedSkewFinEquiv m).surjective i
  obtain ⟨⟨l, b⟩, rfl⟩ := (interleavedSkewFinEquiv m).surjective j
  rw [interleavedSkewFormFin_apply]
  simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]
  fin_cases a <;> fin_cases b <;>
    simp [hB, B.inner_eq_ite, interleavedSkewForm, Matrix.one_apply, eq_comm]

/-- A real skew-symmetric orthogonal matrix is orthogonally congruent to the
interleaved sum of `!![0, 1; -1, 0]` blocks, with the source's orientation.
This is the real normal form asserted in arXiv:1703.09188, proof of `corconj`,
lines 1129–1140. No paired basis is added as a hypothesis. -/
theorem exists_orthogonal_congruence_interleavedSkewForm
    (m : ℕ) (A : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hA : A ∈ orthogonalGroup (Fin (2 * m)) ℝ) (hskew : Aᵀ = -A) :
    ∃ O : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ,
      O ∈ orthogonalGroup (Fin (2 * m)) ℝ ∧
        Oᵀ * interleavedSkewFormFin m * O = A := by
  classical
  let J := orthogonalLinearIsometry A hA
  obtain ⟨B, hB⟩ := LinearIsometry.exists_paired_orthonormalBasis m
    (EuclideanSpace ℝ (Fin (2 * m))) J
    (orthogonalLinearIsometry_sq hA hskew) (by simp)
  let b := B.reindex (interleavedSkewFinEquiv m)
  let e := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  let O := b.toBasis.toMatrix e.toBasis
  have hO : O ∈ orthogonalGroup (Fin (2 * m)) ℝ :=
    b.toMatrix_orthonormalBasis_mem_orthogonal e
  have hCO : e.toBasis.toMatrix b.toBasis * O = 1 :=
    e.toBasis.toMatrix_mul_toMatrix_flip b.toBasis
  have hCOt : e.toBasis.toMatrix b.toBasis = Oᵀ := by
    calc
      e.toBasis.toMatrix b.toBasis =
          e.toBasis.toMatrix b.toBasis * (O * Oᵀ) := by
            rw [(mem_orthogonalGroup_iff _ _).mp hO, mul_one]
      _ = (e.toBasis.toMatrix b.toBasis * O) * Oᵀ := (mul_assoc _ _ _).symm
      _ = Oᵀ := by rw [hCO, one_mul]
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis J.toLinearMap =
      interleavedSkewFormFin m := toMatrix_paired_orthonormalBasis J B hB
  have hchange : e.toBasis.toMatrix b.toBasis *
        LinearMap.toMatrix b.toBasis b.toBasis J.toLinearMap * O =
      LinearMap.toMatrix e.toBasis e.toBasis J.toLinearMap :=
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      (b := e.toBasis) (b' := b.toBasis) (c := e.toBasis) (c' := b.toBasis)
      (f := J.toLinearMap)
  refine ⟨O, hO, ?_⟩
  rw [hCOt, hmat] at hchange
  exact hchange.trans (by
    change LinearMap.toMatrix e.toBasis e.toBasis (Matrix.toEuclideanLin A) = A
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact LinearMap.toMatrix_toLin e.toBasis e.toBasis A)

end Matrix
