/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.MatrixAlgebra.BlockPermutation
import QICLean.Algebra.Unitary.MatrixGramUnitary
import QICLean.Algebra.Matrix.MatrixReindex
import QICLean.Algebra.MatrixAlgebra.SkolemNoether
import Mathlib.Algebra.Central.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import QICLean.Algebra.Hermitian.CornerCompression

/-!
# Unitary Skolem--Noether theorem for complex matrices

A star-algebra automorphism of a nonzero full complex matrix algebra is
conjugation by a unitary matrix.  This is the simple-summand implementation
step used in CPSV16, arXiv:1606.00608, Appendix C.4, line 1997, following
Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8, source lines 322--324.

It also contains the following results.

* `Matrix.exists_partial_isometry_transporting_compressions`,
  `Matrix.exists_partial_isometry_implementing_corner_linearEquiv`: spatial implementation of
  isomorphisms between matrix corners.
-/

open scoped Matrix ComplexOrder

section SkolemNoetherUnitary

open TwoSidedIdeal (blockIdeal blockComponentMap_bijective)

namespace Matrix

/-- A star-algebra automorphism of a nonzero full complex matrix algebra is
implemented by unitary conjugation.

Source: CPSV16, arXiv:1606.00608, Appendix C.4, line 1997; the argument cited
there is Wolf--Perez-Garcia, arXiv:1005.4545, Theorem 8, source lines
322--324. -/
theorem exists_unitary_conj_of_starAlgEquiv_matrix
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (f : Matrix n n ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ) :
    ∃ U : Matrix.unitaryGroup n ℂ, ∀ M : Matrix n n ℂ,
      f M = (U : Matrix n n ℂ) * M * (U : Matrix n n ℂ)ᴴ := by
  classical
  obtain ⟨P, hP⟩ := skolemNoether_matrix f.toAlgEquiv
  have hPinvP :
      (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) * (↑P : Matrix n n ℂ) = 1 :=
    congrArg Units.val (inv_mul_cancel P)
  have hPPinv :
      (↑P : Matrix n n ℂ) * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) = 1 :=
    congrArg Units.val (mul_inv_cancel P)
  have hstar_inner : ∀ X : Matrix n n ℂ,
      (↑P : Matrix n n ℂ) * Xᴴ * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) =
        (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * Xᴴ * (↑P : Matrix n n ℂ)ᴴ := by
    intro X
    have h := map_star f X
    rw [Matrix.star_eq_conjTranspose,
      show f Xᴴ = (↑P : Matrix n n ℂ) * Xᴴ *
        (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) from hP Xᴴ,
      show f X = (↑P : Matrix n n ℂ) * X *
        (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) from hP X] at h
    simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_assoc, Matrix.conjTranspose_mul] using h
  have hPstarPinvstar :
      (↑P : Matrix n n ℂ)ᴴ * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hPinvP, Matrix.conjTranspose_one]
  have hP_star_comm : ∀ Y : Matrix n n ℂ,
      (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) * Y =
        Y * ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)) := by
    intro Y
    specialize hstar_inner Yᴴ
    simp only [Matrix.conjTranspose_conjTranspose] at hstar_inner
    calc
      (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) * Y
          = (↑P : Matrix n n ℂ)ᴴ *
              ((↑P : Matrix n n ℂ) * Y * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)) *
              (↑P : Matrix n n ℂ) := by
            simp only [Matrix.mul_assoc, hPinvP, Matrix.mul_one]
      _ = (↑P : Matrix n n ℂ)ᴴ *
            ((↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ * Y *
              (↑P : Matrix n n ℂ)ᴴ) *
            (↑P : Matrix n n ℂ) := by
            exact congrArg (fun Z : Matrix n n ℂ ↦
              (↑P : Matrix n n ℂ)ᴴ * Z * (↑P : Matrix n n ℂ)) hstar_inner
      _ = ((↑P : Matrix n n ℂ)ᴴ *
              (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)ᴴ) * Y *
            ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)) := by
            simp only [Matrix.mul_assoc]
      _ = Y * ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)) := by
            rw [Matrix.mul_assoc, hPstarPinvstar, Matrix.one_mul]
  have hPHP_center :
      (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) ∈
        Set.range (Matrix.scalar n : ℂ →+* Matrix n n ℂ) := by
    rw [← Matrix.center_eq_range, Semigroup.mem_center_iff]
    exact fun Y ↦ (hP_star_comm Y).symm
  obtain ⟨c, hc_eq⟩ := hPHP_center
  rw [Matrix.scalar_apply] at hc_eq
  have hPHP_smul :
      (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) = c • (1 : Matrix n n ℂ) := by
    rw [← hc_eq, ← Matrix.smul_one_eq_diagonal]
  have hPHP_psd :
      ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self _
  let i : n := Classical.choice (inferInstance : Nonempty n)
  have hc_nonneg : 0 ≤ c := by
    have hdiag :
        ((↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ)) i i = c := by
      rw [hPHP_smul]
      simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    simpa only [hdiag] using hPHP_psd.diag_nonneg (i := i)
  have hc_ne : c ≠ 0 := by
    intro hc0
    have h0 : (↑P : Matrix n n ℂ)ᴴ * (↑P : Matrix n n ℂ) = 0 := by
      rw [hPHP_smul, hc0, zero_smul]
    have hPH_zero : (↑P : Matrix n n ℂ)ᴴ = 0 := by
      have h := congrArg (· * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)) h0
      simp only [Matrix.zero_mul, Matrix.mul_assoc] at h
      rwa [hPPinv, Matrix.mul_one] at h
    have hP_zero : (↑P : Matrix n n ℂ) = 0 := by
      rw [← Matrix.conjTranspose_conjTranspose (↑P : Matrix n n ℂ),
        hPH_zero, Matrix.conjTranspose_zero]
    exact one_ne_zero (show (1 : Matrix n n ℂ) = 0 by
      rw [← hPPinv, hP_zero, Matrix.zero_mul])
  have hc_re_nonneg : 0 ≤ c.re := (RCLike.nonneg_iff.mp hc_nonneg).1
  have hc_im_zero : c.im = 0 := (RCLike.nonneg_iff.mp hc_nonneg).2
  have hc_re_pos : 0 < c.re := by
    rcases lt_or_eq_of_le hc_re_nonneg with h | h
    · exact h
    · exact absurd (Complex.ext h.symm (by simpa using hc_im_zero)) hc_ne
  have hc_eq_re : (c.re : ℂ) = c :=
    Complex.ext (Complex.ofReal_re _) (by simpa using hc_im_zero.symm)
  let V : Matrix n n ℂ := ((Real.sqrt c.re : ℂ))⁻¹ • (↑P : Matrix n n ℂ)
  have hV_mem : V ∈ Matrix.unitaryGroup n ℂ := by
    apply Matrix.smul_mem_unitaryGroup_of_conjTranspose_mul_self_eq_smul_one hc_re_pos
    rw [hc_eq_re, hPHP_smul]
  have hVHV : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp hV_mem)
  have hr_ne : (Real.sqrt c.re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hc_re_pos).ne'
  have hPm_eq :
      (↑P : Matrix n n ℂ) = (Real.sqrt c.re : ℂ) • V := by
    simp only [V, smul_smul, mul_inv_cancel₀ hr_ne, one_smul]
  have hVPinv :
      V * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) =
        (Real.sqrt c.re : ℂ)⁻¹ • (1 : Matrix n n ℂ) := by
    rw [show V = (Real.sqrt c.re : ℂ)⁻¹ • (↑P : Matrix n n ℂ) from rfl,
      smul_mul_assoc, hPPinv]
  have hPinvm_eq :
      (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) =
        (Real.sqrt c.re : ℂ)⁻¹ • Vᴴ := by
    calc
      (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)
          = 1 * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) :=
              (Matrix.one_mul _).symm
      _ = (Vᴴ * V) * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) := by rw [hVHV]
      _ = Vᴴ * (V * (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ)) := by
            rw [Matrix.mul_assoc]
      _ = Vᴴ * ((Real.sqrt c.re : ℂ)⁻¹ • (1 : Matrix n n ℂ)) := by
            rw [hVPinv]
      _ = (Real.sqrt c.re : ℂ)⁻¹ • Vᴴ := by
            rw [mul_smul_comm, Matrix.mul_one]
  refine ⟨⟨V, hV_mem⟩, fun M ↦ ?_⟩
  change f M = V * M * Vᴴ
  rw [show f M = (↑P : Matrix n n ℂ) * M *
      (↑(P⁻¹ : GL n ℂ) : Matrix n n ℂ) from hP M,
    hPm_eq, hPinvm_eq, smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
    inv_mul_cancel₀ hr_ne, one_smul]

section PairedBlocks

variable {I J : Type*} [Finite I] [DecidableEq I] [Finite J] [DecidableEq J]
variable {d : I → ℕ} {e : J → ℕ}
variable [∀ i, NeZero (d i)] [∀ j, NeZero (e j)]

/-- The star-algebra equivalence obtained by restricting a product equivalence
to a supplied pair of simple matrix summands.

The supplied pairing is the relabeling fixed in arXiv:1606.00608,
Appendix C.4, line 1997. -/
noncomputable def blockComponentStarAlgEquiv
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (sigma : I ≃ J)
    (hsigma : ∀ i, T.toRingEquiv.mapTwoSidedIdeal
      (blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
        blockIdeal (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (sigma i))
    (i : I) :
    Matrix (Fin (d i)) (Fin (d i)) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ := by
  classical
  let phi : Matrix (Fin (d i)) (Fin (d i)) ℂ →⋆ₙₐ[ℂ]
      Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ :=
    { toFun := fun M ↦ T (Pi.single i M) (sigma i)
      map_zero' := by simp only [Pi.single_zero, map_zero, Pi.zero_apply]
      map_add' := by
        intro M N
        simp only [Pi.single_add, map_add, Pi.add_apply]
      map_mul' := by
        intro M N
        simp only [Pi.single_mul, map_mul, Pi.mul_apply]
      map_smul' := by
        intro c M
        simp only [Pi.single_smul, map_smul, Pi.smul_apply, MonoidHom.id_apply]
      map_star' := by
        intro M
        rw [Pi.single_star, map_star, Pi.star_apply] }
  exact StarAlgEquiv.ofBijective phi
    (blockComponentMap_bijective T.toRingEquiv sigma hsigma i)

/-- The established name for `reindexStarAlgEquiv`, retained for downstream users. -/
noncomputable abbrev matrixReindexStarAlgEquiv
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (p : m ≃ n) : Matrix m m ℂ ≃⋆ₐ[ℂ] Matrix n n ℂ :=
  reindexStarAlgEquiv p

/-- The restriction of a product star-algebra equivalence to each supplied
pair of equally sized simple matrix summands is implemented by a unitary.

This is the unitary implementation step in arXiv:1606.00608,
Appendix C.4, line 1997. The statement retains the supplied summand pairing
and dimension equalities rather than selecting new witnesses. -/
theorem exists_unitary_block_implementers_of_starAlgEquiv_pi_matrix
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) ≃⋆ₐ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (sigma : I ≃ J)
    (hsigma : ∀ i, T.toRingEquiv.mapTwoSidedIdeal
      (blockIdeal (fun k ↦ Matrix (Fin (d k)) (Fin (d k)) ℂ) i) =
        blockIdeal (fun k ↦ Matrix (Fin (e k)) (Fin (e k)) ℂ) (sigma i))
    (hDim : ∀ i, d i = e (sigma i)) :
    ∃ U : ∀ i, Matrix.unitaryGroup (Fin (e (sigma i))) ℂ,
      ∀ (i : I) (M : Matrix (Fin (d i)) (Fin (d i)) ℂ),
        T (Pi.single i M) (sigma i) =
          (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
            Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
              (U i : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ := by
  classical
  have hImplementer (i : I) :
      ∃ U : Matrix.unitaryGroup (Fin (e (sigma i))) ℂ,
        ∀ M : Matrix (Fin (d i)) (Fin (d i)) ℂ,
          T (Pi.single i M) (sigma i) =
            (U : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (hDim i)) M *
                (U : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ := by
    let reindexEquiv := reindexStarAlgEquiv (finCongr (hDim i))
    let componentEquiv := blockComponentStarAlgEquiv T sigma hsigma i
    let automorphism := reindexEquiv.symm.trans componentEquiv
    obtain ⟨U, hU⟩ := exists_unitary_conj_of_starAlgEquiv_matrix automorphism
    refine ⟨U, fun M ↦ ?_⟩
    change componentEquiv M =
      (U : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ) *
        reindexEquiv M *
          (U : Matrix (Fin (e (sigma i))) (Fin (e (sigma i))) ℂ)ᴴ
    have hComponent : componentEquiv M = automorphism (reindexEquiv M) := by
      simp only [automorphism, StarAlgEquiv.trans_apply, StarAlgEquiv.symm_apply_apply]
    rw [hComponent, hU]
  exact ⟨fun i ↦ (hImplementer i).choose,
    fun i ↦ (hImplementer i).choose_spec⟩

end PairedBlocks

end Matrix

end SkolemNoetherUnitary

section CornerSkolemNoether

/-!
## Spatial implementation of isomorphisms between matrix corners

This file proves that a multiplicative, adjoint-preserving linear equivalence
between two corners of a full complex matrix algebra is implemented by an
ambient partial isometry.

### Main results

* `exists_partial_isometry_implementing_corner_linearEquiv`
* `exists_partial_isometry_transporting_compressions`
-/

namespace Matrix

/-- A unitary conjugation between two compressed matrix algebras extends to an
ambient partial isometry, and conjugation by this partial isometry transports
the two compression maps.

Source: arXiv:1708.00029, Appendix A, lines 985–1002. -/
theorem exists_partial_isometry_transporting_compressions
    {D n : ℕ} (P Q : MatrixAlg D)
    (φP : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule P)
    (φQ : Matrix (Fin n) (Fin n) ℂ ≃ₗ[ℂ] cornerSubmodule Q)
    (VP VQ : Matrix (Fin D) (Fin n) ℂ)
    (hVP_iso : VPᴴ * VP = 1) (hVP_range : VP * VPᴴ = P)
    (hVQ_iso : VQᴴ * VQ = 1) (hVQ_range : VQ * VQᴴ = Q)
    (hφP : ∀ X : Matrix (Fin n) (Fin n) ℂ, (φP X).1 = VP * X * VPᴴ)
    (hφQ : ∀ X : Matrix (Fin n) (Fin n) ℂ, (φQ X).1 = VQ * X * VQᴴ)
    (W : Matrix.unitaryGroup (Fin n) ℂ) :
    ∃ U : MatrixAlg D,
      U = P * U * Q ∧
      Uᴴ * U = Q ∧
      U * Uᴴ = P ∧
      ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (φP ((W : Matrix (Fin n) (Fin n) ℂ) * X *
          (W : Matrix (Fin n) (Fin n) ℂ)ᴴ)).1 =
            U * (φQ X).1 * Uᴴ := by
  let Wmat : Matrix (Fin n) (Fin n) ℂ := W
  let U : MatrixAlg D := VP * Wmat * VQᴴ
  have hWstarW : Wmatᴴ * Wmat = 1 := by
    simpa [Wmat, Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self W
  have hWWstar : Wmat * Wmatᴴ = 1 := by
    simpa [Wmat, Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem W.prop
  have hPVP : P * VP = VP := by
    rw [← hVP_range, Matrix.mul_assoc, hVP_iso, Matrix.mul_one]
  have hVQstarQ : VQᴴ * Q = VQᴴ := by
    rw [← hVQ_range, ← Matrix.mul_assoc, hVQ_iso, Matrix.one_mul]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · symm
    calc
      P * U * Q = (P * VP) * Wmat * (VQᴴ * Q) := by
        simp only [U, Matrix.mul_assoc]
      _ = U := by rw [hPVP, hVQstarQ]
  · rw [show Uᴴ * U = (VP * Wmat * VQᴴ)ᴴ * (VP * Wmat * VQᴴ) from rfl]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc VPᴴ VP, hVP_iso, Matrix.one_mul,
      ← Matrix.mul_assoc Wmatᴴ Wmat, hWstarW, Matrix.one_mul, hVQ_range]
  · rw [show U * Uᴴ = (VP * Wmat * VQᴴ) * (VP * Wmat * VQᴴ)ᴴ from rfl]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc VQᴴ VQ, hVQ_iso, Matrix.one_mul,
      ← Matrix.mul_assoc Wmat Wmatᴴ, hWWstar, Matrix.one_mul, hVP_range]
  · intro X
    rw [hφP, hφQ]
    change VP * (Wmat * X * Wmatᴴ) * VPᴴ =
      (VP * Wmat * VQᴴ) * (VQ * X * VQᴴ) * (VP * Wmat * VQᴴ)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc VQᴴ VQ, hVQ_iso, Matrix.one_mul,
      ← Matrix.mul_assoc VQᴴ VQ, hVQ_iso, Matrix.one_mul]

/-- A multiplicative, adjoint-preserving linear equivalence between two
corners of a full complex matrix algebra is implemented by an ambient partial
isometry whose initial and final projections are the corner units.

Source: arXiv:1708.00029, Appendix A, lines 985–1002. -/
theorem exists_partial_isometry_implementing_corner_linearEquiv
    {D : ℕ} (P Q : MatrixAlg D)
    (hP : IsOrthogonalProjection P) (hQ : IsOrthogonalProjection Q)
    (f : cornerSubmodule Q ≃ₗ[ℂ] cornerSubmodule P)
    (hMul : ∀ X Y : cornerSubmodule Q, (f ⟨X.1 * Y.1, by
      have hQX : Q * X.1 = X.1 := by
        calc
          Q * X.1 = Q * (Q * X.1 * Q) := by rw [X.2]
          _ = (Q * Q) * X.1 * Q := by simp only [Matrix.mul_assoc]
          _ = X.1 := by rw [hQ.2, X.2]
      have hYQ : Y.1 * Q = Y.1 := by
        calc
          Y.1 * Q = (Q * Y.1 * Q) * Q := by rw [Y.2]
          _ = Q * Y.1 * (Q * Q) := by simp only [Matrix.mul_assoc]
          _ = Y.1 := by rw [hQ.2, Y.2]
      calc
        Q * (X.1 * Y.1) * Q = (Q * X.1) * (Y.1 * Q) := by
          simp only [Matrix.mul_assoc]
        _ = X.1 * Y.1 := by rw [hQX, hYQ]⟩).1 = (f X).1 * (f Y).1)
    (hStar : ∀ X : cornerSubmodule Q, (f ⟨X.1ᴴ, by
      change Q * X.1ᴴ * Q = X.1ᴴ
      rw [Matrix.mul_assoc]
      simpa only [Matrix.conjTranspose_mul, hQ.1.eq,
        Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose X.2⟩).1 =
          (f X).1ᴴ) :
    ∃ U : MatrixAlg D,
      U = P * U * Q ∧
      Uᴴ * U = Q ∧
      U * Uᴴ = P ∧
      ∀ X : cornerSubmodule Q, (f X).1 = U * X.1 * Uᴴ := by
  classical
  obtain ⟨UP, SP, TP, nP, -, eSTP, eSP, hUPUP, hUPstarUP, hPdiag_std,
    hP_decomp, hPdiag_back, hPtrace, -⟩ :=
    ProjectionSpectralSplit.ofOrthogonalProjection P hP
  obtain ⟨UQ, SQ, TQ, nQ, -, eSTQ, eSQ, hUQUQ, hUQstarUQ, hQdiag_std,
    hQ_decomp, hQdiag_back, hQtrace, -⟩ :=
    ProjectionSpectralSplit.ofOrthogonalProjection Q hQ
  let P0 : Matrix (SP ⊕ TP) (SP ⊕ TP) ℂ :=
    Matrix.fromBlocks (1 : Matrix SP SP ℂ) 0 0 (0 : Matrix TP TP ℂ)
  let Q0 : Matrix (SQ ⊕ TQ) (SQ ⊕ TQ) ℂ :=
    Matrix.fromBlocks (1 : Matrix SQ SQ ℂ) 0 0 (0 : Matrix TQ TQ ℂ)
  let φP : Matrix (Fin nP) (Fin nP) ℂ ≃ₗ[ℂ] cornerSubmodule P :=
    cornerCompressionLinearEquiv (P := P) (Pdiag := UPᴴ * P * UP) UP eSTP eSP
      P0 rfl hP_decomp rfl hPdiag_std hPdiag_back hUPstarUP hUPUP
  let φQ : Matrix (Fin nQ) (Fin nQ) ℂ ≃ₗ[ℂ] cornerSubmodule Q :=
    cornerCompressionLinearEquiv (P := Q) (Pdiag := UQᴴ * Q * UQ) UQ eSTQ eSQ
      Q0 rfl hQ_decomp rfl hQdiag_std hQdiag_back hUQstarUQ hUQUQ
  let VP : Matrix (Fin D) (Fin nP) ℂ := cornerCompressionIsometry UP eSTP eSP
  let VQ : Matrix (Fin D) (Fin nQ) ℂ := cornerCompressionIsometry UQ eSTQ eSQ
  let gLinear : Matrix (Fin nQ) (Fin nQ) ℂ ≃ₗ[ℂ]
      Matrix (Fin nP) (Fin nP) ℂ :=
    φQ.trans (f.trans φP.symm)
  have hfinrank := LinearEquiv.finrank_eq gLinear
  have hsq : nQ ^ 2 = nP ^ 2 := by
    simpa [Module.finrank_matrix, Fintype.card_fin, pow_two] using hfinrank
  have hRank : nQ = nP := Nat.pow_left_injective (by norm_num) hsq
  subst nP
  have hφP_mul (X Y : Matrix (Fin nQ) (Fin nQ) ℂ) :
      (φP (X * Y)).1 = (φP X).1 * (φP Y).1 := by
    exact cornerCompressionExpand_mul UP eSTP eSP hUPstarUP X Y
  have hφQ_mul (X Y : Matrix (Fin nQ) (Fin nQ) ℂ) :
      (φQ (X * Y)).1 = (φQ X).1 * (φQ Y).1 := by
    exact cornerCompressionExpand_mul UQ eSTQ eSQ hUQstarUQ X Y
  have hφP_star (X : Matrix (Fin nQ) (Fin nQ) ℂ) :
      (φP Xᴴ).1 = (φP X).1ᴴ := by
    exact (cornerCompressionExpand_conjTranspose UP eSTP eSP X).symm
  have hφQ_star (X : Matrix (Fin nQ) (Fin nQ) ℂ) :
      (φQ Xᴴ).1 = (φQ X).1ᴴ := by
    exact (cornerCompressionExpand_conjTranspose UQ eSTQ eSQ X).symm
  let g : Matrix (Fin nQ) (Fin nQ) ℂ →⋆ₙₐ[ℂ]
      Matrix (Fin nQ) (Fin nQ) ℂ :=
    { toFun := gLinear
      map_zero' := gLinear.map_zero
      map_add' := gLinear.map_add
      map_smul' := gLinear.map_smul
      map_mul' := by
        intro X Y
        apply φP.injective
        apply Subtype.ext
        simp only [gLinear, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
        rw [hφP_mul]
        simp only [LinearEquiv.apply_symm_apply]
        have hprod : φQ (X * Y) = ⟨(φQ X).1 * (φQ Y).1, by
            rw [← hφQ_mul X Y]
            exact (φQ (X * Y)).2⟩ :=
          Subtype.ext (hφQ_mul X Y)
        rw [hprod]
        exact hMul (φQ X) (φQ Y)
      map_star' := by
        intro X
        apply φP.injective
        apply Subtype.ext
        simp only [gLinear, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
        simp only [Matrix.star_eq_conjTranspose]
        rw [hφP_star]
        simp only [LinearEquiv.apply_symm_apply]
        have hstarQ : φQ Xᴴ = ⟨(φQ X).1ᴴ, by
            rw [← hφQ_star X]
            exact (φQ Xᴴ).2⟩ :=
          Subtype.ext (hφQ_star X)
        rw [hstarQ]
        exact hStar (φQ X) }
  let gEquiv : Matrix (Fin nQ) (Fin nQ) ℂ ≃⋆ₐ[ℂ]
      Matrix (Fin nQ) (Fin nQ) ℂ :=
    StarAlgEquiv.ofBijective g gLinear.bijective
  cases nQ with
  | zero =>
      have hQzero : Q = 0 := by
        apply (isOrthogonalProjection_posSemidef hQ).trace_eq_zero_iff.mp
        simpa using hQtrace.symm
      have hPzero : P = 0 := by
        apply (isOrthogonalProjection_posSemidef hP).trace_eq_zero_iff.mp
        simpa using hPtrace.symm
      refine ⟨0, by simp [hPzero, hQzero], by simp [hQzero],
        by simp [hPzero], ?_⟩
      intro X
      have hXzero : X.1 = 0 := by simpa [hQzero] using X.2.symm
      have hfXzero : (f X).1 = 0 := by simpa [hPzero] using (f X).2.symm
      simp [hXzero, hfXzero]
  | succ n =>
      obtain ⟨W, hW⟩ := Matrix.exists_unitary_conj_of_starAlgEquiv_matrix gEquiv
      have hVP_iso : VPᴴ * VP = 1 :=
        cornerCompressionIsometry_conjTranspose_mul UP eSTP eSP hUPstarUP
      have hVQ_iso : VQᴴ * VQ = 1 :=
        cornerCompressionIsometry_conjTranspose_mul UQ eSTQ eSQ hUQstarUQ
      have hVP_range : VP * VPᴴ = P := by
        rw [show VP * VPᴴ =
          cornerCompressionExpand UP eSTP eSP 1 by
            simpa [VP] using
              (cornerCompressionExpand_eq_isometry UP eSTP eSP
                (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).symm]
        exact cornerCompressionExpand_one P (UPᴴ * P * UP) UP eSTP eSP P0 rfl
          hP_decomp hPdiag_back
      have hVQ_range : VQ * VQᴴ = Q := by
        rw [show VQ * VQᴴ =
          cornerCompressionExpand UQ eSTQ eSQ 1 by
            simpa [VQ] using
              (cornerCompressionExpand_eq_isometry UQ eSTQ eSQ
                (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).symm]
        exact cornerCompressionExpand_one Q (UQᴴ * Q * UQ) UQ eSTQ eSQ Q0 rfl
          hQ_decomp hQdiag_back
      have hφP_apply (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
          (φP X).1 = VP * X * VPᴴ := by
        exact cornerCompressionExpand_eq_isometry UP eSTP eSP X
      have hφQ_apply (X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
          (φQ X).1 = VQ * X * VQᴴ := by
        exact cornerCompressionExpand_eq_isometry UQ eSTQ eSQ X
      obtain ⟨U, hUsupp, hUstarU, hUUstar, hTransport⟩ :=
        exists_partial_isometry_transporting_compressions P Q φP φQ VP VQ
          hVP_iso hVP_range hVQ_iso hVQ_range hφP_apply hφQ_apply W
      refine ⟨U, hUsupp, hUstarU, hUUstar, ?_⟩
      intro X
      let M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := φQ.symm X
      have hφQM : φQ M = X := LinearEquiv.apply_symm_apply φQ X
      have hgM : gEquiv M = (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * M *
          (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ := hW M
      have hfX :
          f X = φP ((W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) * M *
            (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ᴴ) := by
        rw [← hgM]
        change f X = φP (φP.symm (f (φQ M)))
        rw [hφQM, LinearEquiv.apply_symm_apply]
      rw [congrArg Subtype.val hfX, hTransport M, congrArg Subtype.val hφQM]

end Matrix

end CornerSkolemNoether
