/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalPureCompression
import QICLean.Channel.MaximallyEntangled

/-!
# A Bell projection onto a selected spectral subspace

The selected eigenvectors of the actual first marginal determine a Bell vector
on the physical factor and an auxiliary copy of the selected coordinate space.
Projecting the original vector together with a uniform auxiliary pair onto this
Bell vector gives the compressed typical vector with coefficient
`sqrt z / |E|`.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 247–290, `comparator:bell-pin`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Only the one-copy identity is proved here. Tensor powers and auxiliary label
projections are separate consequences.

Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:bell-pin, comparator:prevector.
Provenance-ID: 8753-qic-typical-bell-pin-01
Downstream declaration:
Matrix.selectedBellVector
Provenance-ID: 8753-qic-typical-bell-pin-02
Downstream declaration:
Matrix.norm_selectedBellVector
Provenance-ID: 8753-qic-typical-bell-pin-03
Downstream declaration:
Matrix.selectedBellProjection
Provenance-ID: 8753-qic-typical-bell-pin-04
Downstream declaration:
Matrix.isStarProjection_selectedBellProjection
Provenance-ID: 8753-qic-typical-bell-pin-05
Downstream declaration:
Matrix.bellPinPrevector
Provenance-ID: 8753-qic-typical-bell-pin-06
Downstream declaration:
Matrix.bellPinPostvector
Provenance-ID: 8753-qic-typical-bell-pin-07
Downstream declaration:
Matrix.selectedBellProjection_bellPinPrevector
-/

open scoped BigOperators Matrix Kronecker ComplexOrder InnerProductSpace

noncomputable section

namespace Matrix

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

private def selectedUniformPair (E : Finset A) : EuclideanSpace ℂ (E × E) :=
  WithLp.toLp 2 (fun x ↦ omegaVec (Fintype.card E)
    ((Fintype.equivFin E) x.1, (Fintype.equivFin E) x.2))

omit [Fintype A] in
private theorem selectedUniformPair_apply (E : Finset A) (c r : E) :
    selectedUniformPair E (c, r) =
      if c = r then (Real.sqrt (E.card : ℝ) : ℂ)⁻¹ else 0 := by
  simp [selectedUniformPair, omegaVec, one_div]

omit [Fintype A] [DecidableEq A] in
private theorem selectedUniformPair_star_dotProduct_self (E : Finset A) (hE : 0 < E.card) :
    star (selectedUniformPair E) ⬝ᵥ selectedUniformPair E = 1 := by
  classical
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Fintype.sum_prod_type,
    Finset.univ_eq_attach, selectedUniformPair_apply, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_attach, ↓reduceIte, map_inv₀, Complex.conj_ofReal, Finset.sum_const,
    Finset.card_attach, nsmul_eq_mul]
  have ht : (Real.sqrt (E.card : ℝ) : ℂ)⁻¹ * (Real.sqrt (E.card : ℝ) : ℂ)⁻¹ =
      (E.card : ℂ)⁻¹ := by
    simpa only [one_div, star_inv₀, Complex.star_def, Complex.conj_ofReal] using
      MaximallyEntangled.omegaCoeff_eq_inv hE
  simpa only [ht] using mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hE.ne')

variable (ψ : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "ρA" => partialTraceRight (vecMulVec ψ (star ψ))
local notation "hρA" => Matrix.PosSemidef.partialTraceRight (posSemidef_vecMulVec_self_star ψ)
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E
local notation "JE" => Matrix.IsHermitian.spectralSelectionEmbedding
  (Matrix.PosSemidef.isHermitian hρA) E

/-- The Bell vector obtained from the actual selected spectral embedding.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 247–253. -/
def selectedBellVector : EuclideanSpace ℂ (A × E) :=
  WithLp.toLp 2 ((JE ⊗ₖ (1 : Matrix E E ℂ)) *ᵥ selectedUniformPair E)

omit [DecidableEq B] in
private theorem selectedBellVector_apply (a : A) (c : E) :
    selectedBellVector ψ E (a, c) =
      (Real.sqrt (E.card : ℝ) : ℂ)⁻¹ * JE a c := by
  simp [selectedBellVector, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Matrix.one_apply, selectedUniformPair_apply, mul_comm]

omit [DecidableEq B] in
private theorem selectedBellVector_star_dotProduct_self (hz : 0 < zE) :
    star (selectedBellVector ψ E) ⬝ᵥ selectedBellVector ψ E = 1 := by
  have hJ := (hρA).isHermitian.isIsometry_spectralSelectionEmbedding E
  have hE : 0 < E.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr fun he ↦ by
      simp [he, IsHermitian.spectralRestrictionMass] at hz)
  have hK := hJ.kronecker JE (1 : Matrix E E ℂ) (by simp [IsIsometry])
  exact (star_mulVec_dotProduct_mulVec_of_conjTranspose_mul_eq_one hK
    (selectedUniformPair E)).trans (selectedUniformPair_star_dotProduct_self E hE)

omit [DecidableEq B] in
/-- Positive selected mass normalizes the actual selected Bell vector.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 247–253. -/
theorem norm_selectedBellVector (hz : 0 < zE) : ‖selectedBellVector ψ E‖ = 1 := by
  have hβ := selectedBellVector_star_dotProduct_self ψ E hz
  have hn : ‖selectedBellVector ψ E‖ ^ 2 = 1 := by
    simpa only [WithLp.toLp_ofLp, hβ, Complex.one_re] using
      norm_toLp_sq (selectedBellVector ψ E)
  nlinarith [norm_nonneg (selectedBellVector ψ E)]

/-- Orthogonal projection onto the selected Bell vector when the selected mass is positive.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 247–253. -/
def selectedBellProjection : Matrix (A × E) (A × E) ℂ :=
  vecMulVec (selectedBellVector ψ E) (star (selectedBellVector ψ E))

omit [DecidableEq B] in
/-- Positive selected mass makes the selected Bell outer product an orthogonal projection.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 247–253. -/
theorem isStarProjection_selectedBellProjection (hz : 0 < zE) :
    IsStarProjection (selectedBellProjection ψ E) := by
  rw [isStarProjection_iff']
  constructor
  · simp [selectedBellProjection, vecMulVec_mul_vecMulVec,
      selectedBellVector_star_dotProduct_self ψ E hz]
  · simp [selectedBellProjection, Matrix.star_eq_conjTranspose,
      conjTranspose_vecMulVec]

/-- The original vector and the actual uniform auxiliary pair, with factors ordered
as physical--auxiliary and selected--complementary pairs.
OpenAI area-law manuscript, `comparator:prevector`, lines 130–141, and
`comparator:bell-pin`, lines 283–290. -/
def bellPinPrevector : EuclideanSpace ℂ ((A × E) × (E × B)) :=
  WithLp.toLp 2 (fun x ↦ ψ (x.1.1, x.2.2) * selectedUniformPair E (x.1.2, x.2.1))

/-- The selected Bell vector tensored with the actual compressed typical vector.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 247–290. -/
def bellPinPostvector : EuclideanSpace ℂ ((A × E) × (E × B)) :=
  WithLp.toLp 2 (fun x ↦ selectedBellVector ψ E x.1 *
    compressedTypicalPureState ψ E x.2)

/-- The actual one-copy Bell projection has coefficient `sqrt z / |E|`.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 283–290. -/
theorem selectedBellProjection_bellPinPrevector (hz : 0 < zE) :
    WithLp.toLp 2 ((selectedBellProjection ψ E ⊗ₖ (1 : Matrix (E × B) (E × B) ℂ)) *ᵥ
      bellPinPrevector ψ E) =
      ((Real.sqrt zE : ℂ) / (E.card : ℂ)) • bellPinPostvector ψ E := by
  ext x
  rcases x with ⟨⟨a, c⟩, r, b⟩
  simp only [mulVec, dotProduct, selectedBellProjection, kroneckerMap_apply, vecMulVec_apply,
    selectedBellVector_apply, Pi.star_apply, RCLike.star_def, one_apply, mul_ite, mul_one,
    mul_zero, bellPinPrevector, selectedUniformPair_apply, ite_mul, zero_mul,
    Fintype.sum_prod_type, Finset.univ_eq_attach, Prod.mk.injEq, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte, map_mul,
    map_inv₀, Complex.conj_ofReal, bellPinPostvector, compressedTypicalPureState,
    mul_apply, conjTranspose_apply, schmidtCoeffMatrix_apply, PiLp.smul_apply, smul_eq_mul]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Finset.sum_const_zero, Finset.mem_attach]
  have hzs : (Real.sqrt zE : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hz).ne'
  have ht := MaximallyEntangled.omegaCoeff_eq_inv (E.card_pos.mpr ⟨c, c.property⟩)
  simp only [one_div, star_inv₀, Complex.star_def, Complex.conj_ofReal] at ht
  rw [div_eq_mul_inv, ← ht]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  generalize JE a c = u, (starRingEnd ℂ) (JE i r) = v, ψ (i, b) = w,
    (Real.sqrt (E.card : ℝ) : ℂ)⁻¹ = t, (Real.sqrt zE : ℂ) = s at ⊢ hzs
  field_simp

end Matrix
