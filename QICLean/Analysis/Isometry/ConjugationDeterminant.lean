/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Algebra.Unitary.SymplecticOrthogonalFour
import QICLean.Analysis.Isometry.ConjugationCovariantGauge
import QICLean.Analysis.Topology.OrthogonalGroupJoined

/-!
# Strict equivalence under conjugation

The "if" directions of Theorems `conjphs` and `prop:conjsym-strict-equiv` of
arXiv:1703.09188 (lines 1406--1446 and 1480--1546): two MPUs whose
standard-form gates have the same determinant invariants are strictly
equivalent under complex conjugation.

The determinant of `u v` reads the composite
`ℂ^r ⊗ ℂ^ℓ → ℂ^ℓ ⊗ ℂ^r` on `ℂ^ℓ ⊗ ℂ^r` through the swap of the two factors;
it is invariant under the gauge `u ↦ (x ⊗ y) u`, `v ↦ v (y† ⊗ x†)` of the
standard form, as computed at line 1416 of the source
(`det_gauge_mul_swap`).

The "only if" direction of Theorem `conjphs` is
`MPOTensor.StrictlyEquivalentUnderSymmetry.det_mul_eq_of_conjugation`, in
`TNLean.MPS.MPU.ConjugationDeterminantInvariant`. That of Theorem
`prop:conjsym-strict-equiv` rests on the forward direction of Lemma
`lem:equivalent-symmetry`, which is available only after blocking, where the
determinant invariants are trivial; it remains open, see
`docs/paper-gaps/mpu_symmetry_path_criterion_blocking.tex`.

## Main results

* `Matrix.det_gauge_mul_swap`: gauge invariance of `det(u v)`.
* `MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_reindexPhysical_of_gate_path`: gate
  paths satisfying the local conjugation equations give strict equivalence.
* `MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_reindexPhysical_of_det_mul_eq`: the
  "if" direction of Theorem `conjphs`, for any standard forms of tensors in canonical form.
* `MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_reindexPhysical_of_det_eq_of_even`:
  the "if" direction of Theorem `prop:conjsym-strict-equiv`, likewise.
* `MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_of_det_mul_eq`,
  `MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_of_det_eq_of_even`: the same for the
  two-site blocks of tensors in canonical form II.

The standard forms need not come from canonical form II: the statements only use the
standard-form data and the canonical form of the endpoints, which strict equivalence requires.

Moved from TNLean, `TNLean/MPS/MPU/Symmetry/Phases/ConjugationStrictEquivalence.lean` at commit
`021ba0bd19` (Apache-2.0).
-/

section

open scoped Matrix Kronecker

namespace Matrix

variable {ℓ r : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

omit [DecidableEq P] in
/-- The determinant of `u v` read on `ℂ^ℓ ⊗ ℂ^r` through the swap is invariant
under the gauge of the standard form. Source: arXiv:1703.09188, the remark after
Theorem `conjphs`, line 1416:
`det((x ⊗ y) u v (y† ⊗ x†)) = det(x ⊗ y) det(u v) det(y† ⊗ x†) = det(u v)`. -/
theorem det_gauge_mul_swap (u : Matrix (Fin ℓ × Fin r) P ℂ) (v : Matrix P (Fin r × Fin ℓ) ℂ)
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y : Matrix (Fin r) (Fin r) ℂ}
    (hx : x ∈ unitaryGroup (Fin ℓ) ℂ) (hy : y ∈ unitaryGroup (Fin r) ℂ) :
    ((((x ⊗ₖ y) * u) * (v * (star y ⊗ₖ star x))).submatrix id
        (Equiv.prodComm (Fin ℓ) (Fin r))).det =
      ((u * v).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det := by
  set e := Equiv.prodComm (Fin ℓ) (Fin r)
  have hsplit : (((x ⊗ₖ y) * u) * (v * (star y ⊗ₖ star x))).submatrix id e =
      (x ⊗ₖ y) * (u * v).submatrix id e * (star y ⊗ₖ star x).submatrix e e := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (x ⊗ₖ y) u v,
      ← Matrix.submatrix_mul_equiv _ _ id e e,
      ← Matrix.submatrix_mul_equiv (x ⊗ₖ y) (u * v) id (Equiv.refl _) e]
    simp
  have hx1 : star x * x = 1 := (Matrix.mem_unitaryGroup_iff'.mp hx)
  have hy1 : star y * y = 1 := (Matrix.mem_unitaryGroup_iff'.mp hy)
  rw [hsplit, det_mul, det_mul, det_submatrix_equiv_self, det_kronecker, det_kronecker]
  have hdx : (star x).det * x.det = 1 := by rw [← det_mul, hx1, det_one]
  have hdy : (star y).det * y.det = 1 := by rw [← det_mul, hy1, det_one]
  calc x.det ^ Fintype.card (Fin r) * y.det ^ Fintype.card (Fin ℓ) *
        ((u * v).submatrix id e).det *
        ((star y).det ^ Fintype.card (Fin ℓ) * (star x).det ^ Fintype.card (Fin r))
      = ((star x).det * x.det) ^ Fintype.card (Fin r) *
          ((star y).det * y.det) ^ Fintype.card (Fin ℓ) * ((u * v).submatrix id e).det := by
        ring
    _ = _ := by rw [hdx, hdy, one_pow, one_pow, one_mul, one_mul]

omit [Fintype P] [DecidableEq P] in
/-- Multiplying a gate on the left by a square matrix multiplies its
determinant, read through any identification of the coordinate spaces. -/
theorem det_mul_submatrix {m : Type*} [Fintype m] [DecidableEq m] (X : Matrix m m ℂ)
    (u : Matrix m P ℂ) (e : m ≃ P) :
    ((X * u).submatrix id e).det = X.det * (u.submatrix id e).det := by
  rw [← Matrix.submatrix_mul_equiv X u id (Equiv.refl _) e, det_mul]
  simp

/-- Multiplying a gate on the right by a square matrix multiplies its
determinant, read through any identification of the coordinate spaces. -/
theorem det_submatrix_mul {Q : Type*} [Fintype Q] [DecidableEq Q] (v : Matrix P Q ℂ)
    (Y : Matrix Q Q ℂ) (f : P ≃ Q) :
    ((v * Y).submatrix id f).det = (v.submatrix id f).det * Y.det := by
  rw [← Matrix.submatrix_mul_equiv v Y id f f, det_mul, det_submatrix_equiv_self]

/-- The determinant of `u v` read through the swap is the product of the
determinants of `u` and `v`, read through one identification `e`. -/
theorem det_mul_swap_eq (u : Matrix (Fin ℓ × Fin r) P ℂ) (v : Matrix P (Fin r × Fin ℓ) ℂ)
    (e : Fin ℓ × Fin r ≃ P) :
    ((u * v).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det =
      (u.submatrix id e).det *
        (v.submatrix id (e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r)))).det := by
  classical
  rw [← Matrix.submatrix_mul_equiv u v id e, det_mul]
  congr 1
  rw [← det_submatrix_equiv_self e]
  congr 1
  ext i j
  simp

/-- A unitary matrix with real entries has determinant `1` or `-1`. -/
theorem det_eq_one_or_neg_one_of_map_star_eq {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A ∈ unitaryGroup m ℂ) (hr : A.map (starRingEnd ℂ) = A) :
    A.det = 1 ∨ A.det = -1 := by
  have h := congrArg det (mem_unitaryGroup_iff'.mp hA)
  have hs : star A = Aᵀ := by
    ext i j
    simpa [star_apply] using congrFun (congrFun hr j) i
  rw [hs, det_mul, det_transpose, det_one, ← sq] at h
  exact sq_eq_one_iff.mp h

/-- The diagonal sign flip of the coordinate `i₀`, a real orthogonal matrix of
determinant `-1`. -/
def coordinateFlip {n : ℕ} (i₀ : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i ↦ if i = i₀ then -1 else 1

theorem coordinateFlip_mem_unitaryGroup {n : ℕ} (i₀ : Fin n) :
    coordinateFlip i₀ ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff, coordinateFlip, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  by_cases h : i = i₀ <;> simp [h]

theorem map_star_coordinateFlip {n : ℕ} (i₀ : Fin n) :
    (coordinateFlip i₀).map (starRingEnd ℂ) = coordinateFlip i₀ := by
  ext i j
  simp only [coordinateFlip, map_apply, diagonal_apply]
  split_ifs <;> simp

theorem star_coordinateFlip {n : ℕ} (i₀ : Fin n) :
    star (coordinateFlip i₀) = coordinateFlip i₀ := by
  rw [coordinateFlip, star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i = i₀ <;> simp [h]

theorem det_coordinateFlip {n : ℕ} (i₀ : Fin n) : (coordinateFlip i₀).det = -1 := by
  rw [coordinateFlip, det_diagonal, Finset.prod_ite_eq' Finset.univ i₀]
  simp

end Matrix

namespace Matrix

variable {ℓ r : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

theorem map_star_mul_of_real {m n o : Type*} [Fintype n] {A : Matrix m n ℂ} {B : Matrix n o ℂ}
    (hA : A.map (starRingEnd ℂ) = A) (hB : B.map (starRingEnd ℂ) = B) :
    (A * B).map (starRingEnd ℂ) = A * B := by
  rw [Matrix.map_mul, hA, hB]

theorem map_star_kronecker_of_real {m n m' n' : Type*} {A : Matrix m n ℂ}
    {B : Matrix m' n' ℂ} (hA : A.map (starRingEnd ℂ) = A) (hB : B.map (starRingEnd ℂ) = B) :
    (A ⊗ₖ B).map (starRingEnd ℂ) = A ⊗ₖ B := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  have h₁ := congrFun (congrFun hA i) j
  have h₂ := congrFun (congrFun hB i') j'
  simp only [map_apply, kroneckerMap_apply] at h₁ h₂ ⊢
  rw [map_mul, h₁, h₂]

/-- **Sign change of the determinants by a real gauge.** If one of `ℓ, r` is
odd, a real orthogonal gauge `(x ⊗ y)` with `x` or `y` a coordinate flip
changes the signs of both determinants of real gates. Source: arXiv:1703.09188,
proof of Theorem `conjphs`, lines 1431--1437. -/
theorem exists_sign_flip_gauge (hℓ : 0 < ℓ) (hr : 0 < r) (hodd : Odd ℓ ∨ Odd r)
    (e : Fin ℓ × Fin r ≃ P) {u : Matrix (Fin ℓ × Fin r) P ℂ}
    {v : Matrix P (Fin r × Fin ℓ) ℂ}
    (hur : u.map (starRingEnd ℂ) = u) (hvr : v.map (starRingEnd ℂ) = v) :
    ∃ (x : unitaryGroup (Fin ℓ) ℂ) (y : unitaryGroup (Fin r) ℂ),
      (((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u).map
          (starRingEnd ℂ) = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u ∧
      (v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))).map
          (starRingEnd ℂ) =
        v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)) ∧
      ((((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u).submatrix
          id e).det = -(u.submatrix id e).det ∧
      ((v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))).submatrix
          id (e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r)))).det =
        -(v.submatrix id (e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r)))).det := by
  have h1r : (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1ℓ : (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ).map (starRingEnd ℂ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rcases hodd with hodd | hodd
  · let y : unitaryGroup (Fin r) ℂ := ⟨coordinateFlip ⟨0, hr⟩, coordinateFlip_mem_unitaryGroup _⟩
    refine ⟨1, y, ?_, ?_, ?_, ?_⟩
    · exact map_star_mul_of_real (map_star_kronecker_of_real h1ℓ (map_star_coordinateFlip _)) hur
    · simp only [y, OneMemClass.coe_one, star_one, star_coordinateFlip]
      exact map_star_mul_of_real hvr (map_star_kronecker_of_real (map_star_coordinateFlip _) h1ℓ)
    · rw [det_mul_submatrix, det_kronecker]
      simp [y, det_coordinateFlip, hodd.neg_one_pow]
    · rw [det_submatrix_mul, det_kronecker]
      simp [y, star_coordinateFlip, det_coordinateFlip, hodd.neg_one_pow]
  · let x : unitaryGroup (Fin ℓ) ℂ := ⟨coordinateFlip ⟨0, hℓ⟩, coordinateFlip_mem_unitaryGroup _⟩
    refine ⟨x, 1, ?_, ?_, ?_, ?_⟩
    · exact map_star_mul_of_real (map_star_kronecker_of_real (map_star_coordinateFlip _) h1r) hur
    · simp only [x, OneMemClass.coe_one, star_one, star_coordinateFlip]
      exact map_star_mul_of_real hvr (map_star_kronecker_of_real h1r (map_star_coordinateFlip _))
    · rw [det_mul_submatrix, det_kronecker]
      simp [x, det_coordinateFlip, hodd.neg_one_pow]
    · rw [det_submatrix_mul, det_kronecker]
      simp [x, star_coordinateFlip, det_coordinateFlip, hodd.neg_one_pow]

/-- **Symplectic gates with the same determinant are joined.** Let `A, B`
be unitary between `P` and `ℂ^ℓ ⊗ ℂ^r`, with `conj(A) = (Σ_ℓ ⊗ Σ_r) A` and
`conj(B) = (Σ_ℓ ⊗ Σ_r) B`. If their determinants agree through `e`, they are
joined by a path of such matrices. Write them as `(1 ⊗ R) a` and `(1 ⊗ R) b`
with `a, b` real (`exists_real_of_map_star_eq_sourceSkewForm_mul`) and join
`a` to `b` by real unitary gates. Source: arXiv:1703.09188, proof of Theorem
`prop:conjsym-strict-equiv`, "if" direction, Case II, lines 1540--1546. -/
theorem IsUnitaryBetween.joinedIn_symplectic_of_det_eq (hℓ : Even ℓ) (hr : Even r)
    (e : Fin ℓ × Fin r ≃ P) {A B : Matrix (Fin ℓ × Fin r) P ℂ}
    (hA : A.IsUnitaryBetween) (hB : B.IsUnitaryBetween)
    (hAc : A.map (starRingEnd ℂ) = (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * A)
    (hBc : B.map (starRingEnd ℂ) = (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * B)
    (hdet : (A.submatrix id e).det = (B.submatrix id e).det) :
    JoinedIn {X : Matrix (Fin ℓ × Fin r) P ℂ | X.IsUnitaryBetween ∧
      X.map (starRingEnd ℂ) = (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * X} A B := by
  set g := evenPairRegroupEquiv hℓ hr
  set K₂ := sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr
  obtain ⟨a, har, hAeq, hAu⟩ := exists_real_of_map_star_eq_sourceSkewForm_mul hℓ hr hAc
  obtain ⟨b, hbr, hBeq, hBu⟩ := exists_real_of_map_star_eq_sourceSkewForm_mul hℓ hr hBc
  set M := (1 : Matrix (Fin (ℓ / 2) × Fin (r / 2)) (Fin (ℓ / 2) × Fin (r / 2)) ℂ) ⊗ₖ
    symplecticOrthogonalR
  have hRu : symplecticOrthogonalR ∈ unitaryGroup (Fin 2 × Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
    exact symplecticOrthogonalR_aux.1
  have hMu : M ∈ unitaryGroup _ ℂ := kronecker_mem_unitary (one_mem _) hRu
  have hMdet : M.det ≠ 0 := by
    intro h0
    have := congrArg det (mem_unitaryGroup_iff.mp hMu)
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have ha := hAu hA
  have hb := hBu hB
  -- The determinants of the real parts agree.
  set e' := g.symm.trans e
  have hdetR : ∀ {X : Matrix (Fin ℓ × Fin r) P ℂ} {x : Matrix _ P ℂ},
      Matrix.reindex g (Equiv.refl P) X = M * x →
        (X.submatrix id e).det = M.det * (x.submatrix id e').det := by
    intro X x hX
    rw [← det_mul_submatrix, ← hX, ← det_submatrix_equiv_self g.symm]
    congr 1
  have hdet' : (a.submatrix id e').det = (b.submatrix id e').det :=
    mul_left_cancel₀ hMdet ((hdetR hAeq).symm.trans (hdet.trans (hdetR hBeq)))
  obtain ⟨γ, hγ⟩ := IsUnitaryBetween.joinedIn_real_of_det_eq e' ha hb har hbr hdet'
  -- Conjugating `M` multiplies it by the regrouped skew form.
  have hK : Matrix.reindex g g K₂ * Matrix.reindex g (Equiv.refl P) A =
      Matrix.reindex g (Equiv.refl P) (K₂ * A) := by
    simp only [Matrix.reindex_apply, submatrix_mul_equiv]
  have hM : M.map (starRingEnd ℂ) = Matrix.reindex g g K₂ * M := by
    have h1 : M.map (starRingEnd ℂ) * a = Matrix.reindex g g K₂ * M * a := by
      rw [Matrix.mul_assoc, ← hAeq, hK, ← hAc]
      conv_lhs => rw [← har]
      rw [← Matrix.map_mul, ← hAeq]
      ext i j
      simp [Matrix.reindex_apply, g]
    have h2 := congrArg (· * aᴴ) h1
    have ha2 : a * aᴴ = 1 := ha.2
    simp only [Matrix.mul_assoc, ha2, Matrix.mul_one] at h2
    exact h2
  let F : Matrix _ P ℂ → Matrix (Fin ℓ × Fin r) P ℂ := fun x ↦
    Matrix.reindex g.symm (Equiv.refl P) (M * x)
  have hF : Continuous F := (continuous_const.matrix_mul continuous_id).matrix_submatrix _ _
  have hFA : F a = A := by
    change Matrix.reindex g.symm (Equiv.refl P) (M * a) = A
    rw [← hAeq]
    ext i j
    simp [Matrix.reindex_apply, g]
  have hFB : F b = B := by
    change Matrix.reindex g.symm (Equiv.refl P) (M * b) = B
    rw [← hBeq]
    ext i j
    simp [Matrix.reindex_apply, g]
  refine ⟨(γ.map hF).cast hFA.symm hFB.symm, fun t ↦ ⟨?_, ?_⟩⟩
  · change (F (γ t)).IsUnitaryBetween
    exact (((isUnitaryBetween_iff_mem_unitaryGroup M).mpr hMu).mul _ _ (hγ t).1).reindex _ _ _
  · change (F (γ t)).map (starRingEnd ℂ) = K₂ * F (γ t)
    have hY : (M * γ t).map (starRingEnd ℂ) = Matrix.reindex g g K₂ * (M * γ t) := by
      rw [Matrix.map_mul, hM, (hγ t).2, Matrix.mul_assoc]
    have hmap : (F (γ t)).map (starRingEnd ℂ) =
        Matrix.reindex g.symm (Equiv.refl P) ((M * γ t).map (starRingEnd ℂ)) := by
      ext i j
      rfl
    rw [hmap, hY]
    simp only [F, Matrix.reindex_apply, Equiv.symm_symm, Equiv.refl_symm]
    rw [← submatrix_mul_equiv _ _ _ g]
    simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
    rfl

/-- The transpose of a matrix unitary between two coordinate spaces is unitary
between them. -/
private theorem isUnitaryBetween_transpose {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] {A : Matrix m n ℂ} (hA : A.IsUnitaryBetween) :
    Aᵀ.IsUnitaryBetween := by
  have h := hA.conjTranspose.map_star
  rwa [conjTranspose, Matrix.map_map, show (starRingEnd ℂ ∘ star) = id from
    funext fun z ↦ by simp, Matrix.map_id] at h

private theorem transpose_sourceSkewForm_kronecker {p q : ℕ} (hp : Even p) (hq : Even q) :
    (sourceSkewForm hp ⊗ₖ sourceSkewForm hq)ᵀ = sourceSkewForm hp ⊗ₖ sourceSkewForm hq := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  have h₁ := congrFun (congrFun (transpose_sourceSkewForm hp) j) i
  have h₂ := congrFun (congrFun (transpose_sourceSkewForm hq) j') i'
  simp only [transpose_apply, neg_apply] at h₁ h₂
  simp only [transpose_apply, kroneckerMap_apply, h₁, h₂, neg_mul_neg]

/-- **Symplectic right gates with the same determinant are joined.** The
form of `IsUnitaryBetween.joinedIn_symplectic_of_det_eq` for gates `v` with
`conj(v) = v (Σ_r ⊗ Σ_ℓ)`, obtained by transposition. Source:
arXiv:1703.09188, proof of Theorem `prop:conjsym-strict-equiv`, "if" direction,
Case II, lines 1540--1546. -/
theorem IsUnitaryBetween.joinedIn_symplectic_right_of_det_eq (hℓ : Even ℓ) (hr : Even r)
    (f : P ≃ Fin r × Fin ℓ) {A B : Matrix P (Fin r × Fin ℓ) ℂ}
    (hA : A.IsUnitaryBetween) (hB : B.IsUnitaryBetween)
    (hAc : A.map (starRingEnd ℂ) = A * (sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ))
    (hBc : B.map (starRingEnd ℂ) = B * (sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ))
    (hdet : (A.submatrix id f).det = (B.submatrix id f).det) :
    JoinedIn {X : Matrix P (Fin r × Fin ℓ) ℂ | X.IsUnitaryBetween ∧
      X.map (starRingEnd ℂ) = X * (sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ)} A B := by
  set K := sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ
  have hKT : Kᵀ = K := transpose_sourceSkewForm_kronecker hr hℓ
  have htc : ∀ {X : Matrix P (Fin r × Fin ℓ) ℂ}, X.map (starRingEnd ℂ) = X * K →
      Xᵀ.map (starRingEnd ℂ) = K * Xᵀ := fun hX ↦ by
    rw [transpose_map, hX, transpose_mul, hKT]
  have hdetT : ∀ X : Matrix P (Fin r × Fin ℓ) ℂ,
      (Xᵀ.submatrix id f.symm).det = (X.submatrix id f).det := fun X ↦ by
    rw [← det_transpose (X.submatrix id f), ← det_submatrix_equiv_self f.symm]
    congr 1
    ext i j
    simp
  obtain ⟨γ, hγ⟩ := IsUnitaryBetween.joinedIn_symplectic_of_det_eq hr hℓ f.symm
    (isUnitaryBetween_transpose hA) (isUnitaryBetween_transpose hB) (htc hAc) (htc hBc)
    (by rw [hdetT, hdetT, hdet])
  refine ⟨(γ.map continuous_id.matrix_transpose).cast (transpose_transpose A).symm
    (transpose_transpose B).symm, fun t ↦ ⟨?_, ?_⟩⟩
  · exact isUnitaryBetween_transpose (hγ t).1
  · change (γ t)ᵀ.map (starRingEnd ℂ) = (γ t)ᵀ * K
    rw [transpose_map, (hγ t).2, transpose_mul, hKT]

end Matrix

end
