/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Complex.Module
import QICLean.Analysis.LowEnergyBasis.SpectralSplit
import QICLean.ManyBody.Hamiltonian.LowEnergyCommutatorSum

/-!
# A ground-space basis with summable off-diagonal parts

Hastings, arXiv:cond-mat/0508554v3, lines 1678–1708, chooses a basis of the ground space in
which the compressions of the filtered terms have summable off-diagonal parts.

* `exists_orthonormalBasis_joint_eigenvectors`, `exists_orthonormalBasis_norm_inner_le_commutators`:
  bases from commuting families and from the commutator map, with the condition number
  `compressionConditionNumber`.
* `groundSpaceCompression` and `exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le`.
* `twoDimensionalSpectralSpread` and the basis of a two-dimensional ground space
  (`exists_twoDimensional_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le`).

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyBasisConstruction.lean`,
`LowEnergyBasisTwoDimensional.lean` and `LowEnergyBasisUniform.lean`. Changes as in
`LowEnergyCommutator`.
-/

noncomputable section

open LowEnergyBasis
open scoped InnerProductSpace

namespace ManyBody

section NormComparison

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
  [FiniteDimensional ℝ F]

/-- The norm of the inverse of the commutator map on the quotient by its kernel. With the
quotient norm this is the reciprocal of its lower norm. It records the conditioning that
replaces the spectral denominators in Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1683–1708. It need not be bounded uniformly along a sequence of systems. -/
noncomputable def quotientConditionNumber (τ : F →ₗ[ℝ] G) : ℝ :=
  letI : IsClosed (τ.ker : Set F) := τ.ker.closed_of_finiteDimensional
  ‖τ.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap‖

theorem quotientConditionNumber_nonneg (τ : F →ₗ[ℝ] G) :
    0 ≤ quotientConditionNumber τ := by
  let : IsClosed (τ.ker : Set F) := τ.ker.closed_of_finiteDimensional
  change 0 ≤ ‖τ.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap‖
  exact norm_nonneg (τ.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap :
    τ.range →L[ℝ] F ⧸ τ.ker)

/-- A contraction vanishing on the kernel of `τ` is bounded by the explicit quotient
conditioning of `τ`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem norm_le_quotientConditionNumber_mul (τ : F →ₗ[ℝ] G) (S : F →ₗ[ℝ] H)
    (hker : τ.ker ≤ S.ker) (hS : ∀ x, ‖S x‖ ≤ ‖x‖) (x : F) :
    ‖S x‖ ≤ quotientConditionNumber τ * ‖τ x‖ := by
  let : IsClosed (τ.ker : Set F) := τ.ker.closed_of_finiteDimensional
  let U := τ.ker.liftQ S hker
  have hU (q : F ⧸ τ.ker) : ‖U q‖ ≤ ‖q‖ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y, hy, hnorm⟩ := Submodule.Quotient.norm_mk_lt q hε
    calc ‖U q‖ = ‖S y‖ := by rw [← hy]; rfl
      _ ≤ ‖q‖ + ε := (hS y).trans hnorm.le
  calc ‖S x‖ = ‖U (τ.ker.mkQ x)‖ := rfl
    _ ≤ ‖τ.ker.mkQ x‖ := hU _
    _ = ‖τ.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap
        ⟨τ x, τ.mem_range_self x⟩‖ := by
      congr 1
      exact (τ.quotKerEquivRange_symm_apply_image x _).symm
    _ ≤ quotientConditionNumber τ * ‖τ x‖ :=
      τ.quotKerEquivRange.symm.toLinearMap.toContinuousLinearMap.le_opNorm _

end NormComparison

section JointBasis

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- Every commuting family of self-adjoint operators on a finite-dimensional complex inner
product space has a common orthonormal eigenbasis. No simplicity of the joint eigenvalues is
required. This supplies the terminal scalar subspaces in Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_joint_eigenvectors (τ : V → E →L[ℂ] E)
    (hT : ∀ i, IsSelfAdjoint (τ i)) (hcomm : ∀ i j, Commute (τ i) (τ j)) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      ∀ i a, ∃ c : ℂ, τ i (b a) = c • b a := by
  classical
  let A : V → Module.End ℂ E := fun i => (τ i).toLinearMap
  have hA : ∀ i, (A i).IsSymmetric := fun i => (hT i).isSymmetric
  have hAA : Pairwise fun i j => Commute (A i) (A j) := fun i j _ => by
    ext x
    exact congrArg (fun U : E →L[ℂ] E => U x) (hcomm i j).eq
  let V : (V → ℂ) → Submodule ℂ E := fun c => ⨅ i, Module.End.eigenspace (A i) (c i)
  have hOrth : OrthogonalFamily ℂ (fun c => V c) fun c => (V c).subtypeₗᵢ :=
    LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces hA
  have hTop : (⨆ c, V c) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hA hAA
  have hInt : DirectSum.IsInternal V := hOrth.isInternal_iff.mpr (by
    rw [hTop, Submodule.top_orthogonal_eq_bot])
  let := hInt.submodule_iSupIndep.fintypeNeBotOfFiniteDimensional
  have hInt' := (DirectSum.isInternal_ne_bot_iff (A := V)).mpr hInt
  have hOrth' := hOrth.comp (Subtype.val_injective (p := fun c => V c ≠ ⊥))
  let b := hInt'.subordinateOrthonormalBasis rfl hOrth'
  refine ⟨b, fun i a => ?_⟩
  let c := hInt'.subordinateOrthonormalBasisIndex rfl a hOrth'
  have hm : b a ∈ V c.val := hInt'.subordinateOrthonormalBasis_subordinate rfl a hOrth'
  exact ⟨c.val i, Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hm i)⟩

end JointBasis

section CompressionSpan

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

noncomputable local instance {m : ℕ} : NormedSpace ℝ (Fin m → E →L[ℂ] E) := Pi.normedSpace

/-- The real dimension of the self-adjoint endomorphisms of an `n`-dimensional complex inner
product space is `n²`. Thus at most `n²` original compressions suffice in the construction of
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem finrank_selfAdjoint_continuousLinearMap :
    Module.finrank ℝ (selfAdjoint (E →L[ℂ] E)) = (Module.finrank ℂ E) ^ 2 := by
  have h := (imaginaryPart (A := E →L[ℂ] E)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr imaginaryPart_surjective, finrank_top,
    ker_imaginaryPart] at h
  have hd : Module.finrank ℝ (E →L[ℂ] E) = 2 * (Module.finrank ℂ E) ^ 2 := by
    rw [finrank_real_of_complex,
      ← (LinearMap.toContinuousLinearMap : (E →ₗ[ℂ] E) ≃ₗ[ℂ] (E →L[ℂ] E)).finrank_eq,
      Module.finrank_linearMap]
    ring
  change Module.finrank ℝ (selfAdjoint (E →L[ℂ] E)) +
    Module.finrank ℝ (selfAdjoint (E →L[ℂ] E)) = _ at h
  omega

/-- The commutator map of a selected finite family, restricted to a real subspace of
endomorphisms. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1708. -/
def compressionCommutatorMap {m : ℕ} (V : Submodule ℝ (E →L[ℂ] E))
    (A : Fin m → E →L[ℂ] E) : V →ₗ[ℝ] (Fin m → E →L[ℂ] E) where
  toFun x i := A i * x.val - x.val * A i
  map_add' x y := by ext i u; simp [mul_add, add_mul]; abel
  map_smul' c x := by ext i u; simp [smul_sub]

set_option backward.isDefEq.respectTransparency false in
/-- The quotient conditioning of the selected compression commutator map, with the
operator norm on the real compression span and the maximum norm on the commutators.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
noncomputable def compressionConditionNumber {m : ℕ} (V : Submodule ℝ (E →L[ℂ] E))
    (A : Fin m → E →L[ℂ] E) : ℝ :=
  letI : NormedSpace ℝ (E →L[ℂ] E) := NormedSpace.complexToReal
  letI : NormedSpace ℝ V := V.normedSpace
  letI : NormedSpace ℝ (Fin m → E →L[ℂ] E) := Pi.normedSpace
  quotientConditionNumber (F := V) (G := Fin m → E →L[ℂ] E) (compressionCommutatorMap V A)

set_option backward.isDefEq.respectTransparency false in
theorem compressionConditionNumber_nonneg {m : ℕ} (V : Submodule ℝ (E →L[ℂ] E))
    (A : Fin m → E →L[ℂ] E) : 0 ≤ compressionConditionNumber V A := by
  unfold compressionConditionNumber
  exact quotientConditionNumber_nonneg (compressionCommutatorMap V A)

set_option backward.isDefEq.respectTransparency false in
/-- A real span of self-adjoint operators has an orthonormal basis in which every
off-diagonal entry is controlled by its commutators with any finite spanning family.
The kernel consists of the centre of this span, whose members commute and hence have a
common orthonormal eigenbasis. This replaces the final separation assertion in Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_norm_inner_le_compressionCommutatorMap
    (V : Submodule ℝ (E →L[ℂ] E)) (hV : ∀ x ∈ V, IsSelfAdjoint x) {m : ℕ}
    (A : Fin m → E →L[ℂ] E) (hspan : Submodule.span ℝ (Set.range A) = V) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E,
      ∀ (x : V) a c, a ≠ c →
        ‖⟪b a, x.val (b c)⟫_ℂ‖ ≤
          quotientConditionNumber (compressionCommutatorMap V A) *
            ∑ i, ‖A i * x.val - x.val * A i‖ := by
  classical
  let τ := compressionCommutatorMap V A
  have hcentral (x : τ.ker) (y : V) : Commute x.val.val y.val := by
    have hy : y.val ∈ Submodule.span ℝ (Set.range A) := hspan.symm ▸ y.property
    suffices ∀ z ∈ Submodule.span ℝ (Set.range A), Commute x.val.val z from this y.val hy
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      have hx := congrFun (LinearMap.mem_ker.mp x.property) i
      exact (sub_eq_zero.mp hx).symm
    | zero => exact Commute.zero_right _
    | add y z _ _ hy hz => exact hy.add_right hz
    | smul c y _ hy => exact hy.smul_right c
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_joint_eigenvectors
    (fun z : τ.ker => z.val.val)
    (fun z => hV _ z.val.property) (fun z w => hcentral z w.val)
  refine ⟨b, fun x a c hac => ?_⟩
  let S : V →ₗ[ℝ] ℂ :=
    (((innerSL ℂ (b a)).comp (ContinuousLinearMap.apply ℂ E (b c))).restrictScalars ℝ).toLinearMap
      |>.comp V.subtype
  have hker : τ.ker ≤ S.ker := by
    intro y hy
    obtain ⟨r, hr⟩ := hb ⟨y, hy⟩ c
    change ⟪b a, y.val (b c)⟫_ℂ = 0
    rw [hr, inner_smul_right, b.orthonormal.inner_eq_zero hac, mul_zero]
  have hS (y : V) : ‖S y‖ ≤ ‖y‖ := by
    change ‖⟪b a, y.val (b c)⟫_ℂ‖ ≤ ‖y.val‖
    calc _ ≤ ‖b a‖ * ‖y.val (b c)‖ := norm_inner_le_norm _ _
      _ ≤ ‖y.val‖ := by simpa only [b.orthonormal.1 a, b.orthonormal.1 c, one_mul, mul_one]
          using y.val.le_opNorm (b c)
  have hcomp : ‖S x‖ ≤ quotientConditionNumber τ * ‖τ x‖ :=
    norm_le_quotientConditionNumber_mul (F := V) (G := Fin m → E →L[ℂ] E) (H := ℂ)
      τ S hker hS x
  have hTx : ‖τ x‖ ≤ ∑ i, ‖A i * x.val - x.val * A i‖ := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr
    intro i
    exact Finset.single_le_sum (f := fun j => ‖A j * x.val - x.val * A j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  change ‖S x‖ ≤ quotientConditionNumber τ * _
  exact hcomp.trans (mul_le_mul_of_nonneg_left hTx (quotientConditionNumber_nonneg τ))

/-- The real span of the original Hermitian compressions. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
noncomputable abbrev realCompressionSpan (B : V → E →L[ℂ] E) : Submodule ℝ (E →L[ℂ] E) :=
  Submodule.span ℝ (Set.range B)

set_option backward.isDefEq.respectTransparency false in
/-- Construction of the basis and of at most `n²` original compressions controlling every
off-diagonal entry. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1695–1708. -/
theorem exists_orthonormalBasis_norm_inner_le_commutators (B : V → E →L[ℂ] E)
    (hB : ∀ i, IsSelfAdjoint (B i)) :
    ∃ (m : ℕ) (j : Fin m → V)
      (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E),
      m ≤ (Module.finrank ℂ E) ^ 2 ∧
      Submodule.span ℝ (Set.range (B ∘ j)) = realCompressionSpan B ∧
      ∀ i a c, a ≠ c →
        ‖⟪b a, B i (b c)⟫_ℂ‖ ≤
          compressionConditionNumber (realCompressionSpan B) (B ∘ j) *
            ∑ k, ‖B (j k) * B i - B i * B (j k)‖ := by
  classical
  let V := realCompressionSpan B
  have hV : V ≤ selfAdjoint.submodule ℝ (E →L[ℂ] E) :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hB i)
  obtain ⟨A, hA, hspan, _⟩ := Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range B)
  choose j hj using hA
  have hAj : B ∘ j = A := funext hj
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_norm_inner_le_compressionCommutatorMap V
    (fun x hx => hV hx) A hspan
  refine ⟨Module.finrank ℝ V, j, b, ?_, hAj.symm ▸ hspan, fun i a c hac => ?_⟩
  · exact (Submodule.finrank_mono hV).trans_eq finrank_selfAdjoint_continuousLinearMap
  · rw [hAj]
    simpa only [compressionConditionNumber, hj] using
      hb ⟨B i, Submodule.subset_span (Set.mem_range_self i)⟩ a c hac

end CompressionSpan

noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) :
    InnerProductSpace ℂ (groundSpace H E₀) :=
  (groundSpace H E₀).innerProductSpace

section GroundSpace

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

local instance (H : Matrix ν ν ℂ) (E₀ : ℝ) : CompleteSpace (groundSpace H E₀) :=
  FiniteDimensional.complete ℂ (groundSpace H E₀)

/-- The compression `P W P`, acting on the ground eigenspace itself. It is the compression
`subspaceCompression` of `W` to the ground space
(`groundSpaceCompression_eq_subspaceCompression`). Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1678–1708. -/
noncomputable def groundSpaceCompression (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    groundSpace H E₀ →L[ℂ] groundSpace H E₀ :=
  ((groundCompression H E₀ W).codRestrict (groundSpace H E₀)
    (fun _ => (groundSpace H E₀).starProjection_apply_mem _)).comp
      (groundSpace H E₀).subtypeL

@[simp]
theorem coe_groundSpaceCompression_apply (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ)
    (x : groundSpace H E₀) :
    (groundSpaceCompression H E₀ W x : EuclideanSpace ℂ ν) = groundCompression H E₀ W x := rfl

/-- The ground-space compression is the compression to the ground space. -/
theorem groundSpaceCompression_eq_subspaceCompression (H : Matrix ν ν ℂ) (E₀ : ℝ)
    (W : Matrix ν ν ℂ) :
    groundSpaceCompression H E₀ W =
      subspaceCompression (groundSpace H E₀) (toEuclideanCLM (n := ν) (𝕜 := ℂ) W) := by
  ext x
  simp [coe_subspaceCompression_apply, groundCompression, mul_apply_eq_comp,
    (groundSpace H E₀).starProjection_eq_self_iff.mpr x.2]

theorem norm_groundSpaceCompression_apply (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ)
    (x : groundSpace H E₀) :
    ‖groundSpaceCompression H E₀ W x‖ = ‖groundCompression H E₀ W x‖ := by
  rw [← coe_groundSpaceCompression_apply]
  rfl

theorem coe_groundSpaceCompression_commutator_apply (H : Matrix ν ν ℂ) (E₀ : ℝ)
    (W B : Matrix ν ν ℂ) (x : groundSpace H E₀) :
    ((groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W) x : EuclideanSpace ℂ ν) =
      (groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W) x := by
  simp [mul_apply_eq_comp, _root_.sub_apply]

theorem isSelfAdjoint_groundSpaceCompression (H : Matrix ν ν ℂ) (E₀ : ℝ)
    {W : Matrix ν ν ℂ} (hW : W.IsHermitian) : IsSelfAdjoint (groundSpaceCompression H E₀ W) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  exact (isSelfAdjoint_groundCompression H E₀ hW).isSymmetric x.val y.val

/-- The norm of a ground-space compression does not exceed the original term norm.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1708. -/
theorem norm_groundSpaceCompression_le (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W‖ ≤ ‖W‖ := by
  refine (show ‖groundSpaceCompression H E₀ W‖ ≤ ‖groundCompression H E₀ W‖ from ?_).trans
    (norm_groundCompression_le H E₀ W)
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x =>
    (norm_groundSpaceCompression_apply H E₀ W x).trans_le
      ((groundCompression H E₀ W).le_opNorm x.val)

/-- Restriction to the ground space does not increase the norm of the commutator.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1683–1708. -/
theorem norm_groundSpaceCompression_commutator_le (H : Matrix ν ν ℂ) (E₀ : ℝ)
    (W B : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W‖ ≤
      ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have h := (groundCompression H E₀ W * groundCompression H E₀ B -
    groundCompression H E₀ B * groundCompression H E₀ W).le_opNorm x.val
  rwa [← coe_groundSpaceCompression_commutator_apply] at h

/-- The ambient compression has exactly the operator norm of its restriction to the
ground eigenspace. Hastings, arXiv:cond-mat/0508554v3, lines 1562–1601. -/
theorem norm_groundSpaceCompression_eq (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W‖ = ‖groundCompression H E₀ W‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦
      (norm_groundSpaceCompression_apply H E₀ W x).trans_le
        ((groundCompression H E₀ W).le_opNorm x.val)
  · refine ContinuousLinearMap.opNorm_le_bound (groundCompression H E₀ W)
      (norm_nonneg (groundSpaceCompression H E₀ W)) ?_
    intro x
    let y : groundSpace H E₀ :=
      ⟨(groundSpace H E₀).starProjection x,
        (groundSpace H E₀).starProjection_apply_mem x⟩
    have hCx : groundCompression H E₀ W x =
        (groundSpaceCompression H E₀ W y : EuclideanSpace ℂ ν) := by
      have hp : (groundSpace H E₀).starProjection
          ((groundSpace H E₀).starProjection x) =
          (groundSpace H E₀).starProjection x :=
        (groundSpace H E₀).starProjection_eq_self_iff.mpr
          ((groundSpace H E₀).starProjection_apply_mem x)
      simp only [y, coe_groundSpaceCompression_apply, groundCompression,
        mul_apply_eq_comp, hp]
    rw [hCx]
    exact ((groundSpaceCompression H E₀ W).le_opNorm y).trans
      (mul_le_mul_of_nonneg_left
        ((groundSpace H E₀).norm_starProjection_apply_le x)
        (norm_nonneg (groundSpaceCompression H E₀ W)))

/-- Restricting a compressed commutator to the ground eigenspace preserves its norm.
Hastings, arXiv:cond-mat/0508554v3, lines 1562–1601 and 1644–1654. -/
theorem norm_groundSpaceCompression_commutator_eq (H : Matrix ν ν ℂ) (E₀ : ℝ)
    (W B : Matrix ν ν ℂ) :
    ‖groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W‖ =
      ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ := by
  apply le_antisymm (norm_groundSpaceCompression_commutator_le H E₀ W B)
  refine ContinuousLinearMap.opNorm_le_bound
    (groundCompression H E₀ W * groundCompression H E₀ B -
      groundCompression H E₀ B * groundCompression H E₀ W)
    (norm_nonneg (groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
      groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W)) ?_
  intro x
  let y : groundSpace H E₀ :=
    ⟨(groundSpace H E₀).starProjection x,
      (groundSpace H E₀).starProjection_apply_mem x⟩
  have hp : (groundSpace H E₀).starProjection
      ((groundSpace H E₀).starProjection x) =
      (groundSpace H E₀).starProjection x :=
    (groundSpace H E₀).starProjection_eq_self_iff.mpr
      ((groundSpace H E₀).starProjection_apply_mem x)
  have hCx : (groundCompression H E₀ W * groundCompression H E₀ B -
      groundCompression H E₀ B * groundCompression H E₀ W) x =
      ((groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
        groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W) y :
          EuclideanSpace ℂ ν) := by
    simp only [_root_.sub_apply, mul_apply_eq_comp, Submodule.coe_sub,
      coe_groundSpaceCompression_apply, y, groundCompression, hp]
  rw [hCx]
  exact ((groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
    groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W).le_opNorm y).trans
      (mul_le_mul_of_nonneg_left ((groundSpace H E₀).norm_starProjection_apply_le x)
        (norm_nonneg (groundSpaceCompression H E₀ W * groundSpaceCompression H E₀ B -
          groundSpaceCompression H E₀ B * groundSpaceCompression H E₀ W)))


end GroundSpace

section Graph

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]

set_option backward.isDefEq.respectTransparency false in
/-- A constructed orthonormal basis of the nonzero ground space satisfies a summed
off-diagonal estimate using at most `n²` local terms. The geometric constant is that
of the commutator row sum, and the additional factor is the explicitly displayed quotient
conditioning of the selected ground-space commutator map, which may depend on the system
size. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu` and lines 1695–1708. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    [NeZero (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀))] :
    let B : κ → groundSpace Φ.hamiltonian E₀ →L[ℂ]
        groundSpace Φ.hamiltonian E₀ :=
      fun i => groundSpaceCompression Φ.hamiltonian E₀ (Φ.term i)
    ∃ (m : ℕ) (j : Fin m → κ)
      (b : OrthonormalBasis
        (Fin (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀))) ℂ
          (groundSpace Φ.hamiltonian E₀)),
      m ≤ (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)) ^ 2 ∧
      ∑ i, ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i)))‖ ≤
        (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀) - 1 : ℕ) *
          compressionConditionNumber (realCompressionSpan B) (B ∘ j) *
          ∑ k, commutatorConst R vR b₀ Kg kg *
            Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) * ‖Φ.term (j k)‖ *
              (|b₀| * (Kg * shellSumConst (commutatorRate R vR b₀ ΔE) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let K := groundSpace Φ.hamiltonian E₀
  let B := fun i => groundSpaceCompression Φ.hamiltonian E₀ (Φ.term i)
  obtain ⟨m, j, b, hm, _, hb⟩ := exists_orthonormalBasis_norm_inner_le_commutators B
    (fun i => isSelfAdjoint_groundSpaceCompression _ _ (hHerm i))
  refine ⟨m, j, b, hm, ?_⟩
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  let C := compressionConditionNumber (realCompressionSpan B) (B ∘ j)
  have hC : 0 ≤ C := compressionConditionNumber_nonneg _ _
  have hv : Orthonormal ℂ (fun c => (b c : EuclideanSpace ℂ (Config X))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hent (i : κ) :
      ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (Φ.term i))‖ ≤
        (Module.finrank ℂ K - 1 : ℕ) * (C * ∑ k, ‖B (j k) * B i - B i * B (j k)‖) := by
    exact norm_offDiagonalPartFamily_le hv _ (by positivity) fun c e hce => hb i c e hce
  calc _ ≤ ∑ i, (Module.finrank ℂ K - 1 : ℕ) *
        (C * ∑ k, ‖B (j k) * B i - B i * B (j k)‖) :=
      Finset.sum_le_sum fun i _ => hent i
    _ = (Module.finrank ℂ K - 1 : ℕ) * C *
        ∑ k, ∑ i, ‖B (j k) * B i - B i * B (j k)‖ := by
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) hC)
      refine Finset.sum_le_sum fun k _ => ?_
      refine (Finset.sum_le_sum fun i _ => norm_groundSpaceCompression_commutator_le
        Φ.hamiltonian E₀ (Φ.term (j k)) (Φ.term i)).trans ?_
      exact sum_norm_groundCompression_commutator_le G a ha Φ hHerm R hDiam vR
        hCard b₀ hBudget Kg kg hGrowth hΔE hgap (j k)

end Graph



end ManyBody

namespace ManyBody


variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The difference of the two eigenvalues of a self-adjoint operator on a two-dimensional
space. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1680–1687. -/
noncomputable def twoDimensionalSpectralSpread (A : E →L[ℂ] E) (hA : IsSelfAdjoint A)
    (hn : Module.finrank ℂ E = 2) : ℝ :=
  |hA.isSymmetric.eigenvalues hn 0 - hA.isSymmetric.eigenvalues hn 1|

/-- A two-dimensional Hermitian compression with zero spectral spread is scalar.
This is the degenerate case of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1678–1694. -/
theorem eq_smul_one_of_twoDimensionalSpectralSpread_eq_zero (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hn : Module.finrank ℂ E = 2)
    (hzero : twoDimensionalSpectralSpread A hA hn = 0) :
    ∃ r : ℝ, A = (r : ℂ) • (1 : E →L[ℂ] E) := by
  let b := hA.isSymmetric.eigenvectorBasis hn
  let r := hA.isSymmetric.eigenvalues hn
  have hr : r 0 = r 1 := sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hAb (a : Fin 2) : A (b a) = (r 0 : ℂ) • b a := by
    calc A (b a) = (r a : ℂ) • b a := hA.isSymmetric.apply_eigenvectorBasis hn a
      _ = (r 0 : ℂ) • b a := by congr 1; fin_cases a <;> simp_all
  refine ⟨r 0, ?_⟩
  ext x
  calc A x = A (∑ a, ⟪b a, x⟫_ℂ • b a) := congrArg A (b.sum_repr' x).symm
    _ = (r 0 : ℂ) • ∑ a, ⟪b a, x⟫_ℂ • b a := by
      simp only [map_sum, map_smul, hAb, Finset.smul_sum, smul_smul, mul_comm]
    _ = ((r 0 : ℂ) • (1 : E →L[ℂ] E)) x := by rw [b.sum_repr']; rfl

/-- A two-dimensional Hermitian operator differs from a real scalar by an operator whose
norm is its spectral spread. This gives the estimate complementary to division by the
spectral spread in Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1694. -/
theorem exists_norm_sub_smul_one_eq_twoDimensionalSpectralSpread (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hn : Module.finrank ℂ E = 2) :
    ∃ r : ℝ, ‖A - (r : ℂ) • (1 : E →L[ℂ] E)‖ = twoDimensionalSpectralSpread A hA hn := by
  let b := hA.isSymmetric.eigenvectorBasis hn
  let r := hA.isSymmetric.eigenvalues hn
  have hAb (a : Fin 2) : A (b a) = (r a : ℂ) • b a :=
    hA.isSymmetric.apply_eigenvectorBasis hn a
  have hdecomp : A - (r 0 : ℂ) • (1 : E →L[ℂ] E) =
      ((r 1 - r 0 : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ (b 1) (b 1) := by
    ext x
    have hx : x = ⟪b 0, x⟫_ℂ • b 0 + ⟪b 1, x⟫_ℂ • b 1 := by
      simpa only [Fin.sum_univ_two] using (b.sum_repr' x).symm
    rw [hx]
    simp [InnerProductSpace.rankOne_apply, map_add, map_smul, hAb, b.inner_eq_ite, smul_smul]
    module
  refine ⟨r 0, ?_⟩
  rw [hdecomp, norm_smul, InnerProductSpace.norm_rankOne, b.orthonormal.1 1, mul_one,
    mul_one, Complex.norm_real]
  exact abs_sub_comm _ _

/-- In any orthonormal basis of a two-dimensional space, the off-diagonal part of a
Hermitian operator has norm at most its spectral spread. Together with the commutator
estimate this removes small spectral denominators from the qualitative bound of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1683–1694. -/
theorem norm_inner_le_twoDimensionalSpectralSpread (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hn : Module.finrank ℂ E = 2)
    {v : Fin 2 → E} (hv : Orthonormal ℂ v) {a c : Fin 2} (hac : a ≠ c) :
    ‖⟪v a, A (v c)⟫_ℂ‖ ≤ twoDimensionalSpectralSpread A hA hn := by
  obtain ⟨r, hr⟩ := exists_norm_sub_smul_one_eq_twoDimensionalSpectralSpread A hA hn
  have heq : ⟪v a, (A - (r : ℂ) • (1 : E →L[ℂ] E)) (v c)⟫_ℂ =
      ⟪v a, A (v c)⟫_ℂ := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_right, inner_smul_right,
      hv.inner_eq_zero hac, mul_zero, sub_zero]
  rw [← heq, ← hr]
  refine (norm_inner_le_norm _ _).trans ?_
  simpa only [hv.1 a, hv.1 c, one_mul, mul_one] using
    (A - (r : ℂ) • (1 : E →L[ℂ] E)).le_opNorm (v c)

/-- The off-diagonal operator version of the spectral-spread bound. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1683–1694. -/
theorem norm_offDiagonalPartFamily_le_twoDimensionalSpectralSpread (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hn : Module.finrank ℂ E = 2)
    {v : Fin 2 → E} (hv : Orthonormal ℂ v) :
    ‖offDiagonalPartFamily v A‖ ≤ twoDimensionalSpectralSpread A hA hn := by
  have hδ : 0 ≤ twoDimensionalSpectralSpread A hA hn := by
    unfold twoDimensionalSpectralSpread
    exact abs_nonneg _
  simpa only [Nat.reduceSub, Nat.cast_one, one_mul] using
    norm_offDiagonalPartFamily_le hv A hδ fun _ _ hac =>
      norm_inner_le_twoDimensionalSpectralSpread A hA hn hv hac

/-- For a finite Hermitian family on a two-dimensional space, either every member is
scalar, or an original member with maximal positive spectral spread has an orthonormal
eigenbasis controlling every off-diagonal part with the source's denominator.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1694. -/
theorem exists_orthonormalBasis_maximal_twoDimensionalSpectralSpread [Finite V]
    (B : V → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i)) (hn : Module.finrank ℂ E = 2) :
    (∀ i, ∃ r : ℝ, B i = (r : ℂ) • (1 : E →L[ℂ] E)) ∨
    ∃ (j : V) (b : OrthonormalBasis (Fin 2) ℂ E),
      0 < twoDimensionalSpectralSpread (B j) (hB j) hn ∧
      (∀ i, twoDimensionalSpectralSpread (B i) (hB i) hn ≤
        twoDimensionalSpectralSpread (B j) (hB j) hn) ∧
      (∀ a, B j (b a) = ((hB j).isSymmetric.eigenvalues hn a : ℂ) • b a) ∧
      ∀ i, ‖offDiagonalPartFamily b (B i)‖ ≤
        ‖B j * B i - B i * B j‖ / twoDimensionalSpectralSpread (B j) (hB j) hn := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let δ := fun i => twoDimensionalSpectralSpread (B i) (hB i) hn
  by_cases hzero : ∀ i, δ i = 0
  · exact Or.inl fun i => eq_smul_one_of_twoDimensionalSpectralSpread_eq_zero
      (B i) (hB i) hn (hzero i)
  · obtain ⟨i, hi⟩ := not_forall.mp hzero
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ δ ⟨i, Finset.mem_univ i⟩
    have hδ : 0 < δ j := lt_of_lt_of_le
      (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hi)) (hj i (Finset.mem_univ i))
    let b := (hB j).isSymmetric.eigenvectorBasis hn
    let r := (hB j).isSymmetric.eigenvalues hn
    have hgap : ∀ a c : Fin 2, a ≠ c → δ j ≤ |r a - r c| := by
      intro a c hac
      fin_cases a <;> fin_cases c <;> simp_all [δ, twoDimensionalSpectralSpread, abs_sub_comm, r]
    refine Or.inr ⟨j, b, hδ, fun i => hj i (Finset.mem_univ i),
      fun a => (hB j).isSymmetric.apply_eigenvectorBasis hn a, fun i => ?_⟩
    simpa only [Nat.reduceSub, Nat.cast_one, one_mul] using
      norm_offDiagonalPartFamily_le_norm_commutator_div (hB j) (B i) b.orthonormal
        (fun a => (hB j).isSymmetric.apply_eigenvectorBasis hn a) hδ hgap

set_option backward.isDefEq.respectTransparency false in
/-- Normalizing by the original term bounds and comparing the spectral-spread estimate
with the commutator estimate removes the small denominator. The resulting decay is the
square root of the commutator decay. This gives a uniform version of the qualitative
two-dimensional assertion of Hastings, arXiv:cond-mat/0508554v3, eq. `oibu`, lines 1678–1694. -/
theorem exists_orthonormalBasis_norm_inner_le_sqrt_commutator_decay [Finite V]
    (B : V → E →L[ℂ] E) (hB : ∀ i, IsSelfAdjoint (B i)) (hn : Module.finrank ℂ E = 2)
    (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) (hNorm : ∀ i, ‖B i‖ ≤ w i)
    {C : ℝ} (hC : 0 ≤ C) (f : V → V → ℝ) (hf : ∀ i j, 0 ≤ f i j)
    (hcomm : ∀ i j, ‖B j * B i - B i * B j‖ ≤ C * w j * w i * (f j i) ^ 2) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ E,
      (∀ i a c, a ≠ c → ⟪b a, B i (b c)⟫_ℂ = 0) ∨
      ∃ j, ∀ i a c, a ≠ c → ‖⟪b a, B i (b c)⟫_ℂ‖ ≤ Real.sqrt C * w i * f j i := by
  classical
  let D : V → E →L[ℂ] E := fun i => (w i)⁻¹ • B i
  have hD (i : V) : IsSelfAdjoint (D i) := (IsSelfAdjoint.all ((w i)⁻¹)).smul (hB i)
  have hrestore (i : V) : w i • D i = B i := by
    by_cases hi : w i = 0
    · have hBi : B i = 0 := norm_eq_zero.mp
        (((hNorm i).trans_eq hi).antisymm (norm_nonneg _))
      simp [D, hi, hBi]
    · simp only [D, smul_smul, mul_inv_cancel₀ hi, one_smul]
  rcases exists_orthonormalBasis_maximal_twoDimensionalSpectralSpread D hD hn with
    hscalar | ⟨j, b, hδ, hmax, hDb, _⟩
  · let b := (stdOrthonormalBasis ℂ E).reindex (finCongr hn)
    refine ⟨b, Or.inl fun i a c hac => ?_⟩
    obtain ⟨r, hr⟩ := hscalar i
    rw [← hrestore i, hr]
    simp only [smul_apply, one_apply_eq_self, ← Complex.coe_smul, inner_smul_right,
      b.orthonormal.inner_eq_zero hac, mul_zero]
  · let δ := twoDimensionalSpectralSpread (D j) (hD j) hn
    let r := (hD j).isSymmetric.eigenvalues hn
    have hwj : 0 < w j := by
      by_contra hj
      have hj0 : w j = 0 := le_antisymm (not_lt.mp hj) (hw j)
      have hr (a : Fin 2) : r a = 0 := by
        have hz : (r a : ℂ) • b a = 0 := (hDb a).symm.trans (by simp [D, hj0])
        exact Complex.ofReal_eq_zero.mp
          ((smul_eq_zero.mp hz).resolve_right (b.orthonormal.ne_zero a))
      have : δ = 0 := by
        change |r 0 - r 1| = 0
        rw [hr 0, hr 1, sub_self, abs_zero]
      exact (ne_of_gt hδ) this
    have hgap {a c : Fin 2} (hac : a ≠ c) : δ ≤ |r a - r c| := by
      fin_cases a <;> fin_cases c <;> simp_all [δ, twoDimensionalSpectralSpread, abs_sub_comm, r]
    refine ⟨b, Or.inr ⟨j, fun i a c hac => ?_⟩⟩
    let z := ‖⟪b a, B i (b c)⟫_ℂ‖
    have hz : 0 ≤ z := norm_nonneg _
    have hsmall : z ≤ w i * δ := by
      have heq : z = w i * ‖⟪b a, D i (b c)⟫_ℂ‖ := by
        dsimp only [z]
        rw [← hrestore i]
        simp only [smul_apply, ← Complex.coe_smul, inner_smul_right, norm_mul,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]
      rw [heq]
      exact mul_le_mul_of_nonneg_left
        ((norm_inner_le_twoDimensionalSpectralSpread (D i) (hD i) hn b.orthonormal hac).trans
          (hmax i)) (hw i)
    have hscaled : ‖D j * B i - B i * D j‖ ≤ C * w i * (f j i) ^ 2 := by
      have heq : D j * B i - B i * D j = (w j)⁻¹ • (B j * B i - B i * B j) := by
        simp only [D, smul_mul_assoc, mul_smul_comm, smul_sub]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwj)]
      calc _ ≤ (w j)⁻¹ * (C * w j * w i * (f j i) ^ 2) :=
          mul_le_mul_of_nonneg_left (hcomm i j) (inv_nonneg.mpr hwj.le)
        _ = _ := by field_simp
    have hlarge : δ * z ≤ C * w i * (f j i) ^ 2 := by
      have hne : r a ≠ r c := fun heq => by
        have := hgap hac
        rw [heq, sub_self, abs_zero] at this
        exact (not_le_of_gt hδ) this
      have hh := norm_inner_le_norm_commutator_div (hD j) (B i) (hDb a) (hDb c) hne
      simp only [b.orthonormal.1 a, b.orthonormal.1 c, mul_one] at hh
      have hh' : z ≤ ‖D j * B i - B i * D j‖ / δ :=
        hh.trans (div_le_div_of_nonneg_left (norm_nonneg _) hδ (hgap hac))
      simpa only [mul_comm] using (((le_div_iff₀ hδ).mp hh').trans hscaled)
    have hsquare : z ^ 2 ≤ C * (w i) ^ 2 * (f j i) ^ 2 := by
      calc z ^ 2 = z * z := pow_two z
        _ ≤ (w i * δ) * z := mul_le_mul_of_nonneg_right hsmall hz
        _ = w i * (δ * z) := by ring
        _ ≤ w i * (C * w i * (f j i) ^ 2) := mul_le_mul_of_nonneg_left hlarge (hw i)
        _ = _ := by ring
    have hright : 0 ≤ Real.sqrt C * w i * f j i :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hw i)) (hf j i)
    change z ≤ _
    apply (pow_le_pow_iff_left₀ hz hright two_ne_zero).mp
    simpa only [mul_pow, Real.sq_sqrt hC] using hsquare



end ManyBody

namespace ManyBody


section WeightedRow

variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] {X : V → Type*}
  [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- A weighted exponential row sum, with a bound on the weights at each anchor.
This is the geometric summation in Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `oibu`, lines 1689–1694, valid at any positive rate. -/
theorem sum_weight_mul_exp_neg_edist_le (G : SimpleGraph V) (a : κ → V)
    (w : κ → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ℝ)
    (hBudget : ∀ x, ∑ i ∈ Finset.univ.filter (fun i => a i = x), w i ≤ B)
    (x : V) (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ r : ℕ,
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {β : ℝ} (hβ : 0 < β) :
    ∑ i, w i * (if G.edist x (a i) = ⊤ then 0 else
      Real.exp (-(β * ((G.edist x (a i)).toNat : ℝ)))) ≤ B * (Kg * shellSumConst β kg) := by
  classical
  let f : V → ℝ := fun y => if G.edist x y = ⊤ then 0 else
    Real.exp (-(β * ((G.edist x y).toNat : ℝ)))
  have hf (y : V) : 0 ≤ f y := by dsimp only [f]; split_ifs <;> positivity
  have hB : 0 ≤ B := (Finset.sum_nonneg fun i _ => hw i).trans (hBudget x)
  have hgroup := sum_weight_mul_comp_le_budget_mul_sum a w B hBudget f hf
  have hsites : ∑ y, f y ≤ Kg * shellSumConst β kg := by
    have heq : ∑ y, f y = ∑ y ∈ Finset.univ.filter (fun y => G.edist x y ≠ ⊤),
        Real.exp (-(β * ((G.edist x y).toNat : ℝ))) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun y _ => ?_
      dsimp only [f]
      split_ifs <;> simp_all
    rw [heq]
    exact sum_exp_neg_edist_le G x Kg kg hGrowth hβ
  exact hgroup.trans (mul_le_mul_of_nonneg_left hsites hB)

end WeightedRow

noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) : InnerProductSpace ℂ (groundSpace H E₀) :=
  (groundSpace H E₀).innerProductSpace

section Graph

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]

set_option backward.isDefEq.respectTransparency false in
/-- There is an orthonormal basis of a two-dimensional ground space for which the
sum of the off-diagonal parts is bounded only by the local norm budget, range, gap and
graph growth. The rate is half
the commutator decay rate. This proves the qualitative size independence of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1678–1694, with an explicit
corrected constant; see `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`. -/
theorem exists_twoDimensional_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    (hdim : Module.finrank ℂ (groundSpace Φ.hamiltonian E₀) = 2) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ (groundSpace Φ.hamiltonian E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i)))‖ ≤
        Real.sqrt (commutatorConst R vR b₀ |Kg| kg *
          Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1))) *
          (|b₀| * (|Kg| * shellSumConst (commutatorRate R vR b₀ ΔE / 2) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let K := groundSpace Φ.hamiltonian E₀
  let B := fun i => groundSpaceCompression Φ.hamiltonian E₀ (Φ.term i)
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
  have hC : 0 ≤ C := mul_nonneg
    (le_trans (by norm_num) (six_le_commutatorConst R vR b₀ (abs_nonneg Kg) kg))
    (Real.exp_pos _).le
  have hGrow : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r => (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  let f := fun j i => if G.edist (a j) (a i) = ⊤ then 0 else
    Real.exp (-(γ / 2 * ((G.edist (a j) (a i)).toNat : ℝ)))
  have hf (j i : κ) : 0 ≤ f j i := by dsimp only [f]; split_ifs <;> positivity
  have hnorm (i : κ) : ‖B i‖ ≤ ‖Φ.term i‖ := norm_groundSpaceCompression_le _ _ _
  have hcomm (i j : κ) : ‖B j * B i - B i * B j‖ ≤ C * ‖Φ.term j‖ * ‖Φ.term i‖ * (f j i) ^ 2 := by
    have heq : (f j i) ^ 2 = if G.edist (a j) (a i) = ⊤ then 0 else
        Real.exp (-(γ * ((G.edist (a j) (a i)).toNat : ℝ))) := by
      dsimp only [f]
      split_ifs
      · simp
      · rw [← Real.exp_nat_mul]
        congr 1
        ring
    rw [heq]
    exact (norm_groundSpaceCompression_commutator_le _ _ _ _).trans
      (norm_groundCompression_commutator_le_exp_edist G a ha Φ hHerm R hDiam vR
        hCard b₀ hBudget |Kg| kg hGrow hΔE hgap i j)
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_norm_inner_le_sqrt_commutator_decay B
    (fun i => isSelfAdjoint_groundSpaceCompression _ _ (hHerm i)) hdim
    (fun i => ‖Φ.term i‖) (fun i => norm_nonneg _) hnorm hC f hf hcomm
  refine ⟨b, ?_⟩
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  have hv : Orthonormal ℂ (fun c => (b c : EuclideanSpace ℂ (Config X))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hbound0 : 0 ≤ Real.sqrt C * (|b₀| * (|Kg| * shellSumConst (γ / 2) kg)) := by
    have := shellSumConst_nonneg (show 0 < γ / 2 by positivity) kg
    positivity
  rcases hb with hzero | ⟨j, hb⟩
  · refine (show ∑ i, ‖offDiagonalPartFamily _ _‖ ≤ 0 from ?_).trans hbound0
    apply Finset.sum_nonpos
    intro i _
    simpa only [mul_zero] using norm_offDiagonalPartFamily_le hv
      (groundCompression Φ.hamiltonian E₀ (Φ.term i)) le_rfl (fun c e hce => by
        have heq := hzero i c e hce
        change ⟪(b c : EuclideanSpace ℂ (Config X)),
          groundCompression Φ.hamiltonian E₀ (Φ.term i) (b e)⟫_ℂ = 0 at heq
        simpa only [heq, norm_zero] using (le_rfl : (0 : ℝ) ≤ 0))
  · have hterm (i : κ) :
        ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
          (groundCompression Φ.hamiltonian E₀ (Φ.term i))‖ ≤ Real.sqrt C * ‖Φ.term i‖ * f j i := by
      simpa only [Nat.reduceSub, Nat.cast_one, one_mul] using norm_offDiagonalPartFamily_le hv
        (groundCompression Φ.hamiltonian E₀ (Φ.term i))
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (hf j i))
        (fun c e hce => hb i c e hce)
    calc _ ≤ ∑ i, Real.sqrt C * ‖Φ.term i‖ * f j i := Finset.sum_le_sum fun i _ => hterm i
      _ = Real.sqrt C * ∑ i, ‖Φ.term i‖ * f j i := by simp only [← mul_assoc, Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply sum_weight_mul_exp_neg_edist_le G a (fun i => ‖Φ.term i‖) (fun i => norm_nonneg _)
          |b₀| _ (a j) |Kg| kg (hGrow (a j)) (by positivity : 0 < γ / 2)
        exact fun x ↦ (sum_weight_anchor_le_of_support_budget T a ha
          (fun i ↦ ‖Φ.term i‖) (fun i ↦ norm_nonneg _) b₀ hBudget x).trans (le_abs_self b₀)

end Graph

end ManyBody
