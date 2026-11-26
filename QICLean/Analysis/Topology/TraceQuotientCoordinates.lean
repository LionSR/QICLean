/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Matrix
import QICLean.Algebra.MatrixAlgebra.SkolemNoether
import QICLean.Analysis.Topology.ContinuousIdempotentFrames

/-!
# Coordinates for multiplication on a trace quotient

Let G be the complex-bilinear two-site trace form and F a fixed section of its
coefficient quotient. The matrix C = G F carries these coordinates into the
trace-dual space. The positive Hermitian Gram matrix C† C is used only to invert
this section; it is distinct from the bilinear form G. Contracted three-site
trace data R then give multiplication coefficients (C† C)⁻¹ C† R.

This file establishes continuity of those coefficients on a constant-rank
neighborhood where a fixed section persists (see
`QICLean.Analysis.Topology.ContinuousIdempotentFrames`). Identifying the coefficients with the
quotient product is a separate algebraic step.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993.

Moved from TNLean,
`TNLean/MPS/CanonicalForm/TraceQuotient/ContinuousTraceQuotientMultiplication.lean`,
`TNLean/MPS/CanonicalForm/TraceQuotient/FramedLeftIdealRealization.lean`,
`TNLean/MPS/CanonicalForm/TraceQuotient/TraceQuotientAlgebraRecovery.lean`,
`TNLean/MPS/CanonicalForm/TraceQuotient/TraceQuotientTripleContinuity.lean`,
`TNLean/MPS/CanonicalForm/TraceQuotient/TraceQuotientLetterCoordinates.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

section

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- Multiplication coordinates obtained by inverting the positive Hermitian
Gram matrix of a fixed section of the trace quotient. -/
noncomputable def traceQuotientProductCoordinates {d r : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ)
    (R : Matrix (Fin d) (Fin r × Fin r) ℂ) :
    Matrix (Fin r) (Fin r × Fin r) ℂ :=
  ((G * F)ᴴ * (G * F))⁻¹ * (G * F)ᴴ * R

/-- Continuous two- and three-site trace data yield continuous multiplication
coordinates whenever the chosen section is injective. -/
theorem continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (R : T → Matrix (Fin d) (Fin r × Fin r) ℂ) (hR : Continuous R)
    (hInj : ∀ t, Function.Injective (G t * F).mulVec) :
    Continuous fun t => traceQuotientProductCoordinates (G t) F (R t) := by
  have hC : Continuous fun t => G t * F := hG.matrix_mul continuous_const
  exact (continuous_gramLeftInverse _ hC hInj).matrix_mul hR

/-- A constant-rank two-site trace family and continuous contracted three-site
trace data admit continuous multiplication coordinates on a fixed local section. -/
theorem exists_open_continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hRank : ∀ t, (G t).rank = r) (t₀ : T)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (hBase : Function.Injective (G t₀ * F).mulVec)
    (R : T → Matrix (Fin d) (Fin r × Fin r) ℂ) (hR : Continuous R) :
    ∃ S : Set T, IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F (R t)) S ∧
      ∀ t ∈ S, Function.Injective (G t * F).mulVec ∧
        LinearMap.range (G t * F).mulVecLin = LinearMap.range (G t).mulVecLin := by
  obtain ⟨S, hS, ht₀, hSection⟩ := exists_open_fixedSection_range G hG hRank t₀ F hBase
  refine ⟨S, hS, ht₀, ?_, hSection⟩
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_traceQuotientProductCoordinates
    (fun t : S => G t) (hG.comp continuous_subtype_val) F
    (fun t : S => R t) (hR.comp continuous_subtype_val)
    (fun t => (hSection t t.property).1)

/-- Continuous trace data of constant rank admit locally continuous quotient
multiplication coordinates, with the base section supplied as a conclusion. -/
theorem exists_local_continuous_traceQuotientProductCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ}
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : Continuous G)
    (hRank : ∀ t, (G t).rank = r) (t₀ : T)
    (R : Matrix (Fin d) (Fin r) ℂ → T → Matrix (Fin d) (Fin r × Fin r) ℂ)
    (hR : ∀ F, Continuous (R F)) :
    ∃ (F : Matrix (Fin d) (Fin r) ℂ) (S : Set T), IsOpen S ∧ t₀ ∈ S ∧
      ContinuousOn (fun t => traceQuotientProductCoordinates (G t) F (R F t)) S ∧
      ∀ t ∈ S, Function.Injective (G t * F).mulVec ∧
        LinearMap.range (G t * F).mulVecLin = LinearMap.range (G t).mulVecLin := by
  obtain ⟨F, hF⟩ := exists_fixedSection_of_rank (G t₀) (hRank t₀)
  obtain ⟨S, hS⟩ := exists_open_continuous_traceQuotientProductCoordinates
    G hG hRank t₀ F hF (R F) (hR F)
  exact ⟨F, S, hS⟩

end Matrix

end

section

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators

namespace Matrix

/-- Left multiplication represented in a supplied frame with a left inverse. -/
noncomputable def leftIdealFrameAction {r D : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :
    (Fin r → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  LinearMap.toMatrix'.toLinearMap.comp ((μ.compl₂ J).compr₂ H)

/-- Evaluation of the matrix representing framed left multiplication. -/
theorem leftIdealFrameAction_mulVec {r D : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (x : Fin r → ℂ) (v : Fin D → ℂ) :
    leftIdealFrameAction μ J H x *ᵥ v = H (μ x (J v)) := by
  simp only [leftIdealFrameAction, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.toMatrix'_mulVec, LinearMap.compr₂_apply, LinearMap.compl₂_apply]

/-- A frame spanning a principal left ideal intertwines its framed action
with the original left multiplication. -/
theorem leftIdealFrameAction_intertwines {r D : ℕ}
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (hAssoc : ∀ x y z, μ (μ x y) z = μ x (μ y z)) (p : Fin r → ℂ)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) :
    ∀ x v, J (leftIdealFrameAction μ J H x *ᵥ v) = μ x (J v) := by
  intro x v
  obtain ⟨y, hy⟩ : J v ∈ LinearMap.range (μ.flip p) :=
    hRange ▸ (show J v ∈ LinearMap.range J from ⟨v, rfl⟩)
  change μ y p = J v at hy
  have hmem : μ x (J v) ∈ LinearMap.range J := by
    rw [hRange]
    exact ⟨μ x y, by simp only [LinearMap.flip_apply, hAssoc, hy]⟩
  obtain ⟨w, hw⟩ := hmem
  rw [leftIdealFrameAction_mulVec, ← hw]
  simpa only [LinearMap.comp_apply, LinearMap.id_apply]
    using congrArg (fun f => J (f w)) hHJ

/-- A D-dimensional faithful frame of a left action realizes the quotient
matrix algebra by a bond gauge. The frame intertwining is supplied here;
its derivation from an invariant minimal left ideal is separate. -/
theorem exists_inner_of_framed_leftAction {r D : ℕ} [NeZero D]
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ)) (hJ : Function.Injective J)
    (L : (Fin r → ℂ) →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hAction : ∀ x v, J (L x *ᵥ v) = μ x (J v)) :
    ∃ X : GL (Fin D) ℂ, ∀ x,
      L x = (X : Matrix (Fin D) (Fin D) ℂ) * E x *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  let : Mul (Fin r → ℂ) := ⟨fun x y => μ x y⟩
  let : Semigroup (Fin r → ℂ) := E.injective.semigroup E hE
  have hAssoc : ∀ x y z, μ (μ x y) z = μ x (μ y z) := mul_assoc
  have hMul : ∀ x y, L (μ x y) = L x * L y := by
    intro x y
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    apply hJ
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hAction, hAssoc]
  let : One (Fin r → ℂ) := ⟨E.symm 1⟩
  let : MulOneClass (Fin r → ℂ) :=
    E.injective.mulOneClass E (E.apply_symm_apply 1) hE
  have hUnit : ∀ x, μ (E.symm 1) x = x := one_mul
  have hOne : L (E.symm 1) = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    apply hJ
    simp only [Matrix.toLin'_apply, hAction, hUnit, Matrix.one_mulVec]
  let T := L.comp E.symm.toLinearMap
  have hTMul : ∀ M N, T (M * N) = T M * T N := by
    intro M N
    have hInv : μ (E.symm M) (E.symm N) = E.symm (M * N) := E.injective (by
      simp only [hE, E.apply_symm_apply])
    change L (E.symm (M * N)) = L (E.symm M) * L (E.symm N)
    rw [← hInv, hMul]
  obtain ⟨X, hX⟩ := Matrix.exists_inner_of_linear_mul_endomorphism T hTMul
    (Matrix.linearMap_ne_zero_of_map_one T hOne)
  exact ⟨X, fun x => by
    simpa only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, E.symm_apply_apply]
      using hX (E x)⟩

/-- A full frame of a D-dimensional principal left ideal realizes the full
matrix algebra by the explicit framed action. -/
theorem exists_inner_of_leftIdealFrame {r D : ℕ} [NeZero D]
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y) (p : Fin r → ℂ)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) :
    ∃ X : GL (Fin D) ℂ, ∀ x,
      leftIdealFrameAction μ J H x = (X : Matrix (Fin D) (Fin D) ℂ) * E x *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
  let : Mul (Fin r → ℂ) := ⟨fun x y => μ x y⟩
  let : Semigroup (Fin r → ℂ) := E.injective.semigroup E hE
  exact exists_inner_of_framed_leftAction μ E hE J
    (LinearMap.injective_of_comp_eq_id J H hHJ) (leftIdealFrameAction μ J H)
    (leftIdealFrameAction_intertwines μ mul_assoc
      p J H hHJ hRange)

/-- The framed left-ideal action is a multiplicative linear equivalence and
preserves the trace determined by any pointwise matrix-algebra identification. -/
theorem exists_linearEquiv_leftIdealFrameAction {r D : ℕ} [NeZero D]
    (μ : (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (E : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : ∀ x y, E (μ x y) = E x * E y) (p : Fin r → ℂ)
    (J : (Fin D → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (H : (Fin r → ℂ) →ₗ[ℂ] (Fin D → ℂ)) (hHJ : H.comp J = LinearMap.id)
    (hRange : LinearMap.range J = LinearMap.range (μ.flip p)) :
    ∃ Θ : (Fin r → ℂ) ≃ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ,
      (∀ x, Θ x = leftIdealFrameAction μ J H x) ∧
      (∀ x y, Θ (μ x y) = Θ x * Θ y) ∧
      (∀ x, Matrix.trace (Θ x) = Matrix.trace (E x)) := by
  obtain ⟨X, hX⟩ := exists_inner_of_leftIdealFrame μ E hE p J H hHJ hRange
  let Θ := (E.trans (Units.mulLeftLinearEquiv ℂ (Matrix (Fin D) (Fin D) ℂ) X)).trans
    (Units.mulRightLinearEquiv ℂ X⁻¹)
  have hΘ : ∀ x, Θ x = leftIdealFrameAction μ J H x := by
    intro x
    simpa only [Θ, LinearEquiv.trans_apply, Units.mulLeftLinearEquiv_apply,
      Units.mulRightLinearEquiv_apply] using (hX x).symm
  refine ⟨Θ, hΘ, ?_, ?_⟩
  · intro x y
    simp [Θ, hE, Matrix.mul_assoc]
  · intro x
    rw [hΘ, hX]
    exact Matrix.trace_units_conj X (E x)

end Matrix

end

section

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

set_option linter.mathlibStandardSet true

open scoped Matrix

namespace Matrix

/-- Explicit framed matrices are continuous on the common domain of their multiplication,
frame, inverse, and letter coefficients. No algebraic assumptions are needed for continuity. -/
theorem continuousOn_leftIdealFrameAction
    {T : Type*} [TopologicalSpace T] {r D : ℕ} (S : Set T)
    (μ : T → (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    (M : T → Matrix (Fin r) (Fin r × Fin r) ℂ) (hM : ContinuousOn M S)
    (hμ : ∀ t x y, μ t x y = M t *ᵥ (fun ab => x ab.1 * y ab.2))
    (J : T → Matrix (Fin r) (Fin D) ℂ) (hJ : ContinuousOn J S)
    (H : T → Matrix (Fin D) (Fin r) ℂ) (hH : ContinuousOn H S)
    (x : T → Fin r → ℂ) (hx : ContinuousOn x S) :
    ContinuousOn (fun t => leftIdealFrameAction (μ t) (J t).mulVecLin
      (H t).mulVecLin (x t)) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hM hJ hH hx ⊢
  apply continuous_matrix
  intro i j
  have hJs : Continuous fun t : S => J t *ᵥ (Pi.single j 1 : Fin D → ℂ) :=
    hJ.matrix_mulVec continuous_const
  have hTen : Continuous fun t : S => fun ab : Fin r × Fin r =>
      x t ab.1 * (J t *ᵥ (Pi.single j 1 : Fin D → ℂ)) ab.2 :=
    continuous_pi fun ab => ((continuous_apply ab.1).comp hx).mul
      ((continuous_apply ab.2).comp hJs)
  have hCont := (continuous_apply i).comp (hH.matrix_mulVec (hM.matrix_mulVec hTen))
  simpa only [Set.domRestrict_apply, leftIdealFrameAction, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.toMatrix'_apply, LinearMap.compr₂_apply,
    LinearMap.compl₂_apply, Matrix.mulVecLin_apply, hμ, Function.comp_def] using hCont

end Matrix

end

section

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators ComplexOrder

namespace Matrix

/-- The raw three-site trace vector contracted with two columns of a physical
coefficient section.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
noncomputable def traceQuotientTripleColumns {d r D : ℕ}
    (B : Fin d → Matrix (Fin D) (Fin D) ℂ) (F : Matrix (Fin d) (Fin r) ℂ) :
    Matrix (Fin d) (Fin r × Fin r) ℂ :=
  Matrix.of fun j ab => Matrix.trace
    (Fintype.linearCombination ℂ B (F *ᵥ Pi.single ab.1 1) *
      Fintype.linearCombination ℂ B (F *ᵥ Pi.single ab.2 1) * B j)

/-- The three-site proportionality identity persists after contracting its
first two physical indices with arbitrary coefficient vectors.
Auxiliary context: arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem traceQuotientSection_triple {d D E : ℕ}
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ) (B : Fin d → Matrix (Fin E) (Fin E) ℂ) (α₃ : ℂ)
    (hTriple : ∀ i k j, Matrix.trace (B i * B k * B j) =
      α₃ * Matrix.trace (A i * A k * A j)) :
    ∀ u v j, Matrix.trace
      (Fintype.linearCombination ℂ B u * Fintype.linearCombination ℂ B v * B j) =
      α₃ * Matrix.trace
        (Fintype.linearCombination ℂ A u * Fintype.linearCombination ℂ A v * A j) := by
  intro u v j
  have hTriple' : ∀ i k j, Matrix.trace (B i * (B k * B j)) =
      α₃ * Matrix.trace (A i * (A k * A j)) := by
    simpa only [Matrix.mul_assoc] using hTriple
  simp only [Fintype.linearCombination_apply, Matrix.sum_mul,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    smul_eq_mul, hTriple', Finset.mul_sum, mul_assoc, mul_left_comm]

end Matrix

end

section TraceQuotientTripleContinuity

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators

namespace Matrix

/-- Contracting a continuous raw tensor family against a fixed physical
section gives continuous three-site trace columns. Auxiliary context:
arXiv:1010.3732, Section II.F.2, lines 953–993. -/
theorem continuous_traceQuotientTripleColumns
    {T : Type*} [TopologicalSpace T] {d r D : ℕ}
    (B : T → (Fin d → Matrix (Fin D) (Fin D) ℂ)) (hB : Continuous B)
    (F : Matrix (Fin d) (Fin r) ℂ) :
    Continuous fun t => traceQuotientTripleColumns (B t) F := by
  have hLC : ∀ x : Fin d → ℂ,
      Continuous fun t => Fintype.linearCombination ℂ (B t) x := by
    intro x
    simpa only [Fintype.linearCombination_apply, Pi.smul_apply, Function.comp_apply] using
      continuous_finsetSum Finset.univ fun i _ =>
        ((continuous_apply i).comp hB).const_smul (x i)
  apply continuous_matrix
  intro j ab
  exact ((hLC (F *ᵥ Pi.single ab.1 1)).matrix_mul
    (hLC (F *ᵥ Pi.single ab.2 1))).matrix_mul
      ((continuous_apply j).comp hB) |>.matrix_trace

end Matrix

end TraceQuotientTripleContinuity

section

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

set_option linter.mathlibStandardSet true

open scoped Matrix BigOperators

namespace Matrix

/-- Coordinates of the original physical letters in a fixed trace section. -/
noncomputable def traceQuotientLetterCoordinates {d r : ℕ}
    (G : Matrix (Fin d) (Fin d) ℂ) (F : Matrix (Fin d) (Fin r) ℂ) :
    Matrix (Fin r) (Fin d) ℂ :=
  ((G * F)ᴴ * (G * F))⁻¹ * (G * F)ᴴ * G

end Matrix

end

section

set_option relaxedAutoImplicit false

set_option maxSynthPendingDepth 3

set_option linter.mathlibStandardSet true

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

/-- Reconstructed letter coordinates are continuous wherever the fixed section is injective. -/
theorem continuousOn_traceQuotientLetterCoordinates
    {T : Type*} [TopologicalSpace T] {d r : ℕ} (S : Set T)
    (G : T → Matrix (Fin d) (Fin d) ℂ) (hG : ContinuousOn G S)
    (F : Matrix (Fin d) (Fin r) ℂ)
    (hInj : ∀ t ∈ S, Function.Injective (G t * F).mulVec) :
    ContinuousOn (fun t => traceQuotientLetterCoordinates (G t) F) S := by
  rw [continuousOn_iff_continuous_domRestrict] at hG ⊢
  have hC : Continuous fun t : S => G t * F := hG.matrix_mul continuous_const
  exact (continuous_gramLeftInverse _ hC (fun t => hInj t t.property)).matrix_mul hG

end Matrix

end
