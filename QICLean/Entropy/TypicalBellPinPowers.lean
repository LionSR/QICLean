/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalBellPin
import QICLean.Algebra.KroneckerFactorPositivity

/-!
# Bell projections on finitely many copies

The one-copy selected Bell projection gives the same identity on every finite
tensor power, with coefficient `(sqrt z / |E|)^k`. Canonical product coordinates
separate the physical--auxiliary factors from the selected and complementary
factors, so an arbitrary operator on the selected auxiliary copies factors
through the projection.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 283–298, `comparator:bell-pin`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:bell-pin.
Provenance-ID: 8753-qic-typical-bell-pin-powers-01
Downstream declaration:
Matrix.finKronecker_selectedBellProjection_bellPinPrevector
Provenance-ID: 8753-qic-typical-bell-pin-powers-02
Downstream declaration:
Matrix.finKronecker_selectedBellProjection_bellPinPrevector_label
Provenance-ID: 8753-qic-typical-bell-pin-powers-03
Downstream declaration:
Matrix.norm_prod_selectedBellVector
Provenance-ID: 8753-qic-typical-bell-pin-powers-04
Downstream declaration:
Matrix.isStarProjection_finKronecker_selectedBellProjection
Provenance-ID: 8753-qic-typical-bell-pin-powers-05
Downstream declaration:
Matrix.prod_selectedBellVector_perm
-/

open scoped BigOperators Matrix Kronecker ComplexOrder InnerProductSpace

noncomputable section

namespace Matrix

private theorem finKronecker_mulVec_prod {k : ℕ} {I : Type*} [Fintype I]
    (M : Fin k → Matrix I I ℂ) (v : Fin k → I → ℂ) :
    finKronecker M *ᵥ (fun x ↦ ∏ j, v j (x j)) =
      fun x ↦ ∏ j, (M j *ᵥ v j) (x j) := by
  funext x
  simp only [mulVec, dotProduct, finKronecker_apply]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

private theorem star_dotProduct_prod {k : ℕ} {I : Type*} [Fintype I]
    (v : Fin k → I → ℂ) :
    star (fun x : Fin k → I ↦ ∏ j, v j (x j)) ⬝ᵥ (fun x ↦ ∏ j, v j (x j)) =
      ∏ j, star (v j) ⬝ᵥ v j := by
  simp only [dotProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum fun (j : Fin k) (a : I) ↦ star (v j a) * v j a).symm

private theorem finKronecker_vecMulVec {k : ℕ} {I : Type*} [Fintype I]
    (v : Fin k → I → ℂ) :
    finKronecker (fun j ↦ vecMulVec (v j) (star (v j))) =
      vecMulVec (fun x : Fin k → I ↦ ∏ j, v j (x j))
        (star (fun x : Fin k → I ↦ ∏ j, v j (x j))) := by
  ext x y
  simp only [finKronecker_apply, vecMulVec_apply, Pi.star_apply, star_prod,
    Finset.prod_mul_distrib]

private theorem finKronecker_kronecker_one_group {k : ℕ} {L R : Type*}
    [Fintype L] [Fintype R] [DecidableEq R] (P : Matrix L L ℂ) :
    let e := Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ L) (fun _ ↦ R)
    (finKronecker fun _ : Fin k ↦ P ⊗ₖ (1 : Matrix R R ℂ)).submatrix e.symm e.symm =
      finKronecker (fun _ : Fin k ↦ P) ⊗ₖ
        (1 : Matrix (Fin k → R) (Fin k → R) ℂ) := by
  ext x y
  simp only [submatrix_apply, finKronecker_apply, kroneckerMap_apply,
    Equiv.arrowProdEquivProdArrow_symm_apply, Finset.prod_mul_distrib]
  congr 1
  by_cases h : x.2 = y.2
  · rw [h]
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [one_apply_ne h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (one_apply_ne hj)

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (ψ : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "hρA" => Matrix.PosSemidef.partialTraceRight (posSemidef_vecMulVec_self_star ψ)
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E

omit [DecidableEq B] in
private theorem prod_selectedBellVector_star_dotProduct_self (k : ℕ) (hz : 0 < zE) :
    star (fun x : Fin k → A × E ↦ ∏ j, selectedBellVector ψ E (x j)) ⬝ᵥ
      (fun x ↦ ∏ j, selectedBellVector ψ E (x j)) = 1 := by
  rw [star_dotProduct_prod]
  simp_rw [dotProduct_comm]
  simp only [← EuclideanSpace.inner_eq_star_dotProduct (selectedBellVector ψ E)
    (selectedBellVector ψ E), inner_self_eq_norm_sq_to_K,
    norm_selectedBellVector ψ E hz]
  norm_num

/-- The actual Bell identity on `k` copies has coefficient `(sqrt z / |E|)^k`.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 283–290. -/
theorem finKronecker_selectedBellProjection_bellPinPrevector (k : ℕ) (hz : 0 < zE) :
    WithLp.toLp 2
      ((finKronecker fun _ : Fin k ↦ selectedBellProjection ψ E ⊗ₖ
        (1 : Matrix (E × B) (E × B) ℂ)) *ᵥ
          (fun x ↦ ∏ j, bellPinPrevector ψ E (x j))) =
      (((Real.sqrt zE : ℂ) / (E.card : ℂ)) ^ k) •
        WithLp.toLp 2 (fun x : Fin k → (A × E) × (E × B) ↦
          ∏ j, bellPinPostvector ψ E (x j)) := by
  have hpin (x : (A × E) × (E × B)) :
      ((selectedBellProjection ψ E ⊗ₖ (1 : Matrix (E × B) (E × B) ℂ)) *ᵥ
        bellPinPrevector ψ E) x =
      ((Real.sqrt zE : ℂ) / (E.card : ℂ)) * bellPinPostvector ψ E x := by
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      congrArg (fun v : EuclideanSpace ℂ ((A × E) × (E × B)) ↦ v x)
        (selectedBellProjection_bellPinPrevector ψ E hz)
  ext x
  simp only [finKronecker_mulVec_prod, hpin, PiLp.smul_apply,
    smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- An arbitrary operator on the selected auxiliary copies factors through the actual
`k`-copy Bell projection. The coordinates are the canonical grouping of the physical--auxiliary,
selected, and complementary copies. No commutation hypothesis is required.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 283–298. -/
theorem finKronecker_selectedBellProjection_bellPinPrevector_label (k : ℕ) (hz : 0 < zE)
    (Λ : Matrix (Fin k → E) (Fin k → E) ℂ) :
    let e := (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ A × E) (fun _ ↦ E × B)).trans
      ((Equiv.refl (Fin k → A × E)).prodCongr
        (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ E) (fun _ ↦ B)))
    let Pk := finKronecker (fun _ : Fin k ↦ selectedBellProjection ψ E) ⊗ₖ
      (1 : Matrix ((Fin k → E) × (Fin k → B)) ((Fin k → E) × (Fin k → B)) ℂ)
    let ΛR := (1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
      (Λ ⊗ₖ (1 : Matrix (Fin k → B) (Fin k → B) ℂ))
    WithLp.toLp 2 (Pk *ᵥ (ΛR *ᵥ (fun x ↦ ∏ j, bellPinPrevector ψ E (e.symm x j)))) =
      (((Real.sqrt zE : ℂ) / (E.card : ℂ)) ^ k) •
        WithLp.toLp 2 (ΛR *ᵥ (fun x ↦ ∏ j, bellPinPostvector ψ E (e.symm x j))) := by
  intro e Pk ΛR
  let M := finKronecker fun _ : Fin k ↦ selectedBellProjection ψ E ⊗ₖ
    (1 : Matrix (E × B) (E × B) ℂ)
  have hgroup : M.submatrix e.symm e.symm = Pk := by
    change (M.submatrix
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ A × E) (fun _ ↦ E × B)).symm
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ A × E) (fun _ ↦ E × B)).symm).submatrix
        (Prod.map id (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ E) (fun _ ↦ B)).symm)
        (Prod.map id (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ ↦ E) (fun _ ↦ B)).symm) = Pk
    rw [finKronecker_kronecker_one_group]
    rw [← kroneckerMap_submatrix_right, submatrix_one_equiv]
  have hpin : Pk *ᵥ (fun x ↦ ∏ j, bellPinPrevector ψ E (e.symm x j)) =
      (((Real.sqrt zE : ℂ) / (E.card : ℂ)) ^ k) •
        (fun x ↦ ∏ j, bellPinPostvector ψ E (e.symm x j)) := by
    rw [← hgroup, submatrix_mulVec_equiv]
    simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]
    funext x
    simpa only [PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] using
      congrArg (fun v : EuclideanSpace ℂ (Fin k → (A × E) × (E × B)) ↦ v (e.symm x))
        (finKronecker_selectedBellProjection_bellPinPrevector ψ E k hz)
  have hcomm : Pk * ΛR = ΛR * Pk := by
    simp only [Pk, ΛR, ← mul_kronecker_mul, mul_one, one_mul]
  rw [mulVec_mulVec, hcomm, ← mulVec_mulVec, hpin, mulVec_smul]
  rfl

omit [DecidableEq B] in
/-- Every finite tensor power of the selected Bell vector has unit norm when the
actual selected mass is positive.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 283–298. -/
theorem norm_prod_selectedBellVector (k : ℕ) (hz : 0 < zE) :
    ‖WithLp.toLp 2 (fun x : Fin k → A × E ↦ ∏ j, selectedBellVector ψ E (x j))‖ = 1 := by
  have hn : ‖WithLp.toLp 2 (fun x : Fin k → A × E ↦
      ∏ j, selectedBellVector ψ E (x j))‖ ^ 2 = 1 := by
    simpa only [prod_selectedBellVector_star_dotProduct_self ψ E k hz, Complex.one_re] using
      norm_toLp_sq (fun x : Fin k → A × E ↦ ∏ j, selectedBellVector ψ E (x j))
  nlinarith [norm_nonneg (WithLp.toLp 2
    (fun x : Fin k → A × E ↦ ∏ j, selectedBellVector ψ E (x j)))]

omit [DecidableEq B] in
/-- The finite tensor power of the actual selected Bell projection is an orthogonal projection.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 283–298. -/
theorem isStarProjection_finKronecker_selectedBellProjection (k : ℕ) (hz : 0 < zE) :
    IsStarProjection (finKronecker fun _ : Fin k ↦ selectedBellProjection ψ E) := by
  simp only [selectedBellProjection, finKronecker_vecMulVec, isStarProjection_iff']
  constructor
  · simp [vecMulVec_mul_vecMulVec, prod_selectedBellVector_star_dotProduct_self ψ E k hz]
  · simp [Matrix.star_eq_conjTranspose, conjTranspose_vecMulVec]

omit [DecidableEq B] in
/-- Simultaneous permutations of the physical--auxiliary copies fix the repeated
selected Bell vector, without a normalization hypothesis.
OpenAI area-law manuscript, `comparator:bell-pin`, lines 290–295. -/
theorem prod_selectedBellVector_perm (k : ℕ) (σ : Equiv.Perm (Fin k))
    (x : Fin k → A × E) :
    (∏ j, selectedBellVector ψ E (x (σ j))) = ∏ j, selectedBellVector ψ E (x j) := by
  exact Equiv.prod_comp σ (fun j ↦ selectedBellVector ψ E (x j))

end Matrix
