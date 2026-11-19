/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import QICLean.Analysis.LowEnergyBasis.OffDiagonal

/-!
@@DOC
-/

noncomputable section

open scoped InnerProductSpace

namespace LowEnergyBasis

/-- Finite-dimensional complex inner product spaces are complete. -/
local instance completeSpace_of_finiteDimensional {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] : CompleteSpace E :=
  FiniteDimensional.complete ℂ E

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

end LowEnergyBasis
