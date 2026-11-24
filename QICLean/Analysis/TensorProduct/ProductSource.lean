/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
Assisted-by: OpenAI Codex (GPT-6).
These constructions and proofs are independently written from the manuscript
and Mathlib; no upstream OpenAI Lean proof text is reused in this file.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QICLean.Algebra.Kronecker.KroneckerSandwich

/-!
# Kronecker averages replacing a Schmidt outer product

A point `x` of `ℝ^(ι × 2)` has the complex coordinates `(x_{i,0} + i x_{i,1}) / √2`. For
nonnegative weights `λ` on `A` and `μ` on `C` and a point `x` of `ℝ^((Fin k × (A × C)) × 2)`,
the matrices `U_j` and `V_j` on `A × C` have the entries `(λ_a μ_c)^{1/4} g_{j,a,c}` and
`(λ_a μ_c)^{1/4} conj g_{j,a,c}`, where `g` are the complex coordinates of `x`. Their Kronecker
average `k⁻¹ ∑_j U_j ⊗ V_j` replaces the outer product `|√λ⟩⟨√μ|` of the two Schmidt vectors
written in the paired bases; the correction is the difference of the two.

Four matrices `E`, `F`, `Et`, `Ft` with columns indexed by `A` and `C` carry the Schmidt vectors
to `∑_a √λ_a E_{·a} ⊗ F_{·a}` and the matrices above to matrices between their row spaces, by
`Matrix.kroneckerSandwich`; the matrices need not have orthonormal columns. Every object here
is a function of the point `x`; no measure is involved.

## Main definitions

* `EuclideanSpace.complexCoordinate`: the complex coordinate `(x_{i,0} + i x_{i,1}) / √2`.
* `Matrix.schmidtVector`, `Matrix.schmidtOuterProduct`: the Schmidt vector in the paired basis
  and the outer product of two of them.
* `Matrix.schmidtFrameVector`, `Matrix.schmidtFrameOuterProduct`: the same in the columns of
  two matrices.
* `ProductSource.sourceU`, `ProductSource.sourceV`, `ProductSource.sampledSource`,
  `ProductSource.sourceCorrection`: the factors, their Kronecker average and the correction.
* `ProductSource.ambientSourceU`, `ProductSource.ambientSourceV`,
  `ProductSource.ambientSampledSource`, `ProductSource.ambientSourceCorrection`: the same
  carried by four matrices.

## Main results

* `Matrix.kroneckerSandwich_schmidtOuterProduct`: the carried Schmidt outer product.
* `ProductSource.ambientSampledSource_eq_kroneckerSandwich`,
  `ProductSource.ambientSourceCorrection_eq_kroneckerSandwich`: the carried average and
  correction.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `04-compression.tex:279–309`, `eq:compression-random-source`.
-/

open scoped BigOperators ComplexConjugate Kronecker

noncomputable section

namespace EuclideanSpace

/-- The complex coordinate `(x_{i,0} + i x_{i,1}) / √2` of a point of `ℝ^(ι × 2)`; the factor
`1 / √2` gives unit mean square to a standard Gaussian point.
Source: `04-compression.tex:291–297`. -/
def complexCoordinate {ι : Type*} (i : ι) (x : EuclideanSpace ℝ (ι × Fin 2)) : ℂ :=
  ((x (i, 0) : ℂ) + Complex.I * (x (i, 1) : ℂ)) / (Real.sqrt 2 : ℂ)

/-- The defining formula of the complex coordinate. -/
theorem complexCoordinate_apply {ι : Type*} (i : ι) (x : EuclideanSpace ℝ (ι × Fin 2)) :
    complexCoordinate i x = ((x (i, 0) : ℂ) + Complex.I * (x (i, 1) : ℂ)) /
      (Real.sqrt 2 : ℂ) :=
  rfl

end EuclideanSpace

namespace Matrix

variable {A C W X Y Z : Type*}

/-- The Schmidt vector in its paired basis, with amplitudes `√λ_a` at the pairs `(a, a)`.
Source: `04-compression.tex:281–289`. -/
def schmidtVector [DecidableEq A] (lam : A → ℝ) (p : A × A) : ℂ :=
  if p.1 = p.2 then (Real.sqrt (lam p.1) : ℂ) else 0

/-- The rectangular outer product `|√λ⟩⟨√μ|` of two Schmidt vectors in their paired bases.
Source: `eq:compression-random-source`, `04-compression.tex:281–305`. -/
def schmidtOuterProduct [DecidableEq A] [DecidableEq C] (lam : A → ℝ) (mu : C → ℝ) :
    Matrix (A × A) (C × C) ℂ :=
  Matrix.vecMulVec (schmidtVector lam) (fun q ↦ conj (schmidtVector mu q))

/-- The entries of the outer product of two Schmidt vectors: `√λ_a √μ_c` at `((a, a), (c, c))`
and zero elsewhere. -/
theorem schmidtOuterProduct_apply [DecidableEq A] [DecidableEq C] (lam : A → ℝ) (mu : C → ℝ)
    (p : A × A) (q : C × C) :
    schmidtOuterProduct lam mu p q =
      if p.1 = p.2 ∧ q.1 = q.2 then
        ((Real.sqrt (lam p.1) * Real.sqrt (mu q.1) : ℝ) : ℂ) else 0 := by
  by_cases hp : p.1 = p.2 <;> by_cases hq : q.1 = q.2 <;>
    simp [schmidtOuterProduct, Matrix.vecMulVec_apply, schmidtVector, hp, hq]

/-- The vector `∑_a √λ_a E_{·a} ⊗ F_{·a}` with Schmidt weights `λ` in the columns of `E` and `F`.
Source: `04-compression.tex:281–289`. -/
def schmidtFrameVector [Fintype A] (lam : A → ℝ) (E : Matrix W A ℂ) (F : Matrix X A ℂ)
    (p : W × X) : ℂ :=
  ∑ a, (Real.sqrt (lam a) : ℂ) * E p.1 a * F p.2 a

/-- The outer product of two vectors with Schmidt weights in the columns of given matrices.
Source: `eq:compression-random-source`, `04-compression.tex:281–305`. -/
def schmidtFrameOuterProduct [Fintype A] [Fintype C] (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    Matrix (W × X) (Y × Z) ℂ :=
  Matrix.vecMulVec (schmidtFrameVector lam E F)
    (fun q ↦ conj (schmidtFrameVector mu Et Ft q))

/-- The vector with Schmidt weights in the columns of `E` and `F` is `E ⊗ F` applied to the
Schmidt vector in the paired basis. -/
theorem schmidtFrameVector_eq_mulVec [Fintype A] [DecidableEq A] (lam : A → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) :
    schmidtFrameVector lam E F = (E ⊗ₖ F) *ᵥ schmidtVector lam := by
  funext p
  simp only [Matrix.mulVec_apply_eq_sum, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, schmidtVector,
    mul_ite, mul_zero]
  change (∑ a, (Real.sqrt (lam a) : ℂ) * E p.1 a * F p.2 a) =
    ∑ a, ∑ b, if a = b then (E p.1 a * F p.2 b) * (Real.sqrt (lam a) : ℂ) else 0
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Carrying the outer product of two Schmidt vectors by `E ⊗ F` and `Et ⊗ Ft` gives the outer
product of the vectors with Schmidt weights in the columns of these matrices. -/
theorem kroneckerSandwich_schmidtOuterProduct [Fintype A] [Fintype C] [DecidableEq A]
    [DecidableEq C] (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ) :
    kroneckerSandwich E F Et Ft (schmidtOuterProduct lam mu) =
      schmidtFrameOuterProduct lam mu E F Et Ft := by
  unfold schmidtFrameOuterProduct
  rw [schmidtFrameVector_eq_mulVec, schmidtFrameVector_eq_mulVec]
  simp only [kroneckerSandwich, schmidtOuterProduct, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul]
  congr 1
  exact (Matrix.star_mulVec _ _).symm

end Matrix

namespace ProductSource

open Matrix

variable {A C W X Y Z : Type*}

/-- The first factor `U_j`, with entries `(λ_a μ_c)^{1/4} g_{j,a,c}` for the complex
coordinates `g` of the point `x`.
Source: `eq:compression-random-source`, `04-compression.tex:294–297`. -/
def sourceU (k : ℕ) (lam : A → ℝ) (mu : C → ℝ) (j : Fin k)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) : Matrix A C ℂ :=
  Matrix.of fun a c ↦ (((lam a * mu c) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
    EuclideanSpace.complexCoordinate (j, (a, c)) x

/-- The second factor `V_j`, with the conjugates of the same complex coordinates as `U_j`.
Source: `04-compression.tex:297–300`. -/
def sourceV (k : ℕ) (lam : A → ℝ) (mu : C → ℝ) (j : Fin k)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) : Matrix A C ℂ :=
  Matrix.of fun b d ↦ (((lam b * mu d) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
    conj (EuclideanSpace.complexCoordinate (j, (b, d)) x)

/-- The Kronecker average `k⁻¹ ∑_j U_j ⊗ V_j`.
Source: `eq:compression-random-source`, `04-compression.tex:300–305`. -/
def sampledSource (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) : Matrix (A × A) (C × C) ℂ :=
  (k : ℂ)⁻¹ • ∑ j : Fin k, sourceU k lam mu j x ⊗ₖ sourceV k lam mu j x

/-- The correction: the Kronecker average minus the outer product of the two Schmidt vectors,
without positivity or Hermiticity assumptions.
Source: `eq:compression-random-source`, `04-compression.tex:302–305`. -/
def sourceCorrection [DecidableEq A] [DecidableEq C] (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) : Matrix (A × A) (C × C) ℂ :=
  sampledSource k lam mu x - schmidtOuterProduct lam mu

/-- The first factor carried by `E` and `Et`: `E U_j Etᴴ`.
Source: `eq:compression-random-source`, `04-compression.tex:294–297`. -/
def ambientSourceU [Fintype A] [Fintype C] (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (Et : Matrix Y C ℂ) (j : Fin k)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) : Matrix W Y ℂ :=
  E * sourceU k lam mu j x * Et.conjTranspose

/-- The second factor carried by `F` and `Ft`: `F V_j Ftᴴ`.
Source: `eq:compression-random-source`, `04-compression.tex:297–300`. -/
def ambientSourceV [Fintype A] [Fintype C] (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (F : Matrix X A ℂ) (Ft : Matrix Z C ℂ) (j : Fin k)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) : Matrix X Z ℂ :=
  F * sourceV k lam mu j x * Ft.conjTranspose

/-- The Kronecker average of the carried factors.
Source: `eq:compression-random-source`, `04-compression.tex:300–309`. -/
def ambientSampledSource [Fintype A] [Fintype C] (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) : Matrix (W × X) (Y × Z) ℂ :=
  (k : ℂ)⁻¹ • ∑ j : Fin k,
    ambientSourceU k lam mu E Et j x ⊗ₖ ambientSourceV k lam mu F Ft j x

/-- The carried correction: the carried Kronecker average minus the outer product of the two
vectors with Schmidt weights in the columns of the four matrices.
Source: `eq:compression-random-source`, `04-compression.tex:302–305`. -/
def ambientSourceCorrection [Fintype A] [Fintype C] (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) : Matrix (W × X) (Y × Z) ℂ :=
  ambientSampledSource k lam mu E F Et Ft x - schmidtFrameOuterProduct lam mu E F Et Ft

/-- The Kronecker product of the two carried factors is the carried Kronecker product. -/
theorem ambientSourceU_kronecker_ambientSourceV [Fintype A] [Fintype C] (k : ℕ)
    (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (j : Fin k) (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) :
    ambientSourceU k lam mu E Et j x ⊗ₖ ambientSourceV k lam mu F Ft j x =
      kroneckerSandwich E F Et Ft (sourceU k lam mu j x ⊗ₖ sourceV k lam mu j x) :=
  (kroneckerSandwich_kronecker E F Et Ft _ _).symm

/-- The Kronecker average of the carried factors is the carried Kronecker average. -/
theorem ambientSampledSource_eq_kroneckerSandwich [Fintype A] [Fintype C] (k : ℕ)
    (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) :
    ambientSampledSource k lam mu E F Et Ft x =
      kroneckerSandwich E F Et Ft (sampledSource k lam mu x) := by
  simp only [ambientSampledSource, ambientSourceU_kronecker_ambientSourceV,
    kroneckerSandwich, sampledSource, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_sum, Matrix.sum_mul]

/-- The carried correction is the carried correction matrix. -/
theorem ambientSourceCorrection_eq_kroneckerSandwich [Fintype A] [Fintype C] [DecidableEq A]
    [DecidableEq C] (k : ℕ) (lam : A → ℝ) (mu : C → ℝ)
    (E : Matrix W A ℂ) (F : Matrix X A ℂ) (Et : Matrix Y C ℂ) (Ft : Matrix Z C ℂ)
    (x : EuclideanSpace ℝ ((Fin k × (A × C)) × Fin 2)) :
    ambientSourceCorrection k lam mu E F Et Ft x =
      kroneckerSandwich E F Et Ft (sourceCorrection k lam mu x) := by
  rw [ambientSourceCorrection, ambientSampledSource_eq_kroneckerSandwich,
    ← kroneckerSandwich_schmidtOuterProduct]
  simp only [kroneckerSandwich, sourceCorrection, Matrix.mul_sub, Matrix.sub_mul]

end ProductSource
