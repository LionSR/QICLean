/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap
import QICLean.Channel.KrausRank
import QICLean.Channel.LorentzNormalForm.SpinorAction

/-!
# Canonical non-diagonal and singular qubit channels

This module formalizes the two non-generic channel representatives displayed in
Verstraete--Verschelde, *On Quantum Channels*, arXiv:quant-ph/0202124v2,
Theorem 8, Equations (17)--(19), and repeated in Wolf, Proposition 2.11
(`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 1021--1035).

Only the displayed representatives are treated here.  In particular, this file
does not prove that every qubit channel has one of these forms, does not derive
the necessary range `0 ≤ x ≤ 1`, and does not construct filtering maps.

The Pauli-transfer convention is Wolf's
`T̂ᵢⱼ = tr[σᵢ T(σⱼ)] / 2`.  QICLean's Choi matrix is normalized, so
for a trace-preserving qubit map
`tau = (1/4) sum i j, T̂ᵢⱼ σᵢ ⊗ σⱼᵀ`.  Consequently a raw Pauli
correlation matrix of `tau` has the extra sign in its `σ₂` input column
coming from `σ₂ᵀ = -σ₂`; no raw-correlation matrix is identified with
the transfer matrix below.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder
open Matrix Finset

noncomputable section

namespace Wolf

private abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
private abbrev QubitMap := QubitMatrix →ₗ[ℂ] QubitMatrix

/-! ## The non-diagonal representative -/

/-- The three fixed matrix directions in the Kraus family of
Verstraete--Verschelde, Equation (19). -/
def nonDiagonalKrausBase : Fin 3 → QubitMatrix
  | 0 => !![1, 0; 0, (1 / Real.sqrt 3 : ℝ)]
  | 1 => !![1, 0; 0, (-1 / Real.sqrt 3 : ℝ)]
  | 2 => !![0, 1; 0, 0]

/-- The three real coefficients in the Kraus family of
Verstraete--Verschelde, Equation (19). -/
def nonDiagonalKrausCoefficient (x : ℝ) : Fin 3 → ℝ
  | 0 => Real.sqrt ((1 + x) / 2)
  | 1 => Real.sqrt ((1 - x) / 2)
  | 2 => Real.sqrt (2 / 3)

/-- The exact three-operator non-diagonal Kraus family from
Verstraete--Verschelde, Equation (19).  The hypotheses `0 ≤ x ≤ 1` are
used only when certifying that this family is trace preserving. -/
def nonDiagonalKraus (x : ℝ) : Fin 3 → QubitMatrix :=
  fun i ↦ (nonDiagonalKrausCoefficient x i : ℂ) • nonDiagonalKrausBase i

/-- The canonical non-diagonal completely positive map displayed in
Verstraete--Verschelde, Theorem 8. -/
def nonDiagonalMap (x : ℝ) : QubitMap :=
  Kraus.mapLM (nonDiagonalKraus x)

/-- The source-displayed non-diagonal Kraus family is trace preserving on
the stated parameter interval. -/
theorem nonDiagonalKraus_isTP {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Kraus.IsTP (nonDiagonalKraus x) := by
  have hplus : 0 ≤ (1 + x) / 2 := by linarith
  have hminus : 0 ≤ (1 - x) / 2 := by linarith
  have hsplus := Real.sq_sqrt hplus
  have hsminus := Real.sq_sqrt hminus
  have hstwo := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have hplus' : 0 ≤ 1 + x := by linarith
  have hminus' : 0 ≤ 1 - x := by linarith
  have hsplus' := Real.sq_sqrt hplus'
  have hsminus' := Real.sq_sqrt hminus'
  have hsqrtTwo := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsqrtThree := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hsqrtTwo_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtThree_ne : Real.sqrt 3 ≠ 0 := by positivity
  have hsqrtTwoFour : Real.sqrt 2 ^ 4 = 4 := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, hsqrtTwo]
    norm_num
  rw [Kraus.IsTP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nonDiagonalKraus, nonDiagonalKrausCoefficient,
      nonDiagonalKrausBase, Fin.sum_univ_three, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      hsplus, hsminus, hstwo]
  all_goals norm_cast
  all_goals field_simp [hsqrtTwo_ne, hsqrtThree_ne]
  all_goals norm_num [hsplus', hsminus', hsqrtTwo, hsqrtThree, hsqrtTwoFour]

/-- The source-displayed non-diagonal Kraus family defines a channel on
`0 ≤ x ≤ 1`.  This is a sufficiency statement, not a derivation of the
parameter range. -/
theorem nonDiagonalMap_isChannel {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IsChannel (nonDiagonalMap x) :=
  Kraus.isChannel_mapLM _ (nonDiagonalKraus_isTP hx0 hx1)

/-- Entrywise action of the canonical non-diagonal representative. -/
theorem nonDiagonalMap_apply {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (X : QubitMatrix) :
    nonDiagonalMap x X =
      !![X 0 0 + (2 / 3 : ℂ) * X 1 1, (x / Real.sqrt 3 : ℝ) * X 0 1;
         (x / Real.sqrt 3 : ℝ) * X 1 0, (1 / 3 : ℂ) * X 1 1] := by
  have hplus : 0 ≤ (1 + x) / 2 := by linarith
  have hminus : 0 ≤ (1 - x) / 2 := by linarith
  have hsplus : Real.sqrt ((1 + x) / 2) ^ 2 = (1 + x) / 2 := Real.sq_sqrt hplus
  have hsminus : Real.sqrt ((1 - x) / 2) ^ 2 = (1 - x) / 2 := Real.sq_sqrt hminus
  have hstwo : Real.sqrt (2 / 3) ^ 2 = (2 / 3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtThree : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsqrtThree_ne : Real.sqrt 3 ≠ 0 := by positivity
  have hplus' : 0 ≤ 1 + x := by linarith
  have hminus' : 0 ≤ 1 - x := by linarith
  have hsplus' : Real.sqrt (1 + x) ^ 2 = 1 + x := Real.sq_sqrt hplus'
  have hsminus' : Real.sqrt (1 - x) ^ 2 = 1 - x := Real.sq_sqrt hminus'
  have hsqrtTwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtTwo_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsumReal :
      Real.sqrt (1 + x) / Real.sqrt 2 * (Real.sqrt (1 + x) / Real.sqrt 2) +
        Real.sqrt (1 - x) / Real.sqrt 2 * (Real.sqrt (1 - x) / Real.sqrt 2) = 1 := by
    field_simp [hsqrtTwo_ne]
    nlinarith [hsplus', hsminus', hsqrtTwo]
  have hdiffReal :
      Real.sqrt (1 + x) / Real.sqrt 2 * (Real.sqrt (1 + x) / Real.sqrt 2) -
        Real.sqrt (1 - x) / Real.sqrt 2 * (Real.sqrt (1 - x) / Real.sqrt 2) = x := by
    field_simp [hsqrtTwo_ne]
    nlinarith [hsplus', hsminus', hsqrtTwo]
  have hraiseReal :
      Real.sqrt 2 / Real.sqrt 3 * (Real.sqrt 2 / Real.sqrt 3) = 2 / 3 := by
    field_simp [hsqrtThree_ne, hsqrtTwo_ne]
    nlinarith [hsqrtTwo, hsqrtThree]
  have hinvThreeReal :
      (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 1 / 3 := by
    field_simp [hsqrtThree_ne]
    nlinarith [hsqrtThree]
  have hsum :
      ((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) +
        ((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) = 1 := by
    exact_mod_cast hsumReal
  have hdiff :
      ((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) -
        ((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ) *
          (((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) = x := by
    exact_mod_cast hdiffReal
  have hraise :
      ((Real.sqrt 2 : ℝ) : ℂ) / ((Real.sqrt 3 : ℝ) : ℂ) *
          (((Real.sqrt 2 : ℝ) : ℂ) / ((Real.sqrt 3 : ℝ) : ℂ)) =
        ((2 / 3 : ℝ) : ℂ) := by
    exact_mod_cast hraiseReal
  have hinvThree :
      (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ =
        ((1 / 3 : ℝ) : ℂ) := by
    exact_mod_cast hinvThreeReal
  norm_num at hraise hinvThree
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [nonDiagonalMap, Kraus.map_apply, nonDiagonalKraus,
      nonDiagonalKrausCoefficient, nonDiagonalKrausBase, Fin.sum_univ_three,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]
  · linear_combination (X 0 0) * hsum + (X 1 1) * hraise
  · linear_combination (X 0 1 * (((Real.sqrt 3 : ℝ) : ℂ))⁻¹) * hdiff
  · linear_combination (X 1 0 * (((Real.sqrt 3 : ℝ) : ℂ))⁻¹) * hdiff
  · have hdiag :
        ((((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) *
              (((Real.sqrt (1 + x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) +
            (((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ)) *
              (((Real.sqrt (1 - x) : ℝ) : ℂ) / ((Real.sqrt 2 : ℝ) : ℂ))) *
            ((((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * (((Real.sqrt 3 : ℝ) : ℂ))⁻¹) = 1 / 3 := by
        rw [hsum, hinvThree]
        norm_num
    linear_combination (X 1 1) * hdiag

/-- Exact Pauli-transfer matrix of the non-diagonal representative in
Wolf, Proposition 2.11 case 2. -/
theorem pauliTransferMatrix_nonDiagonalMap {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    pauliTransferMatrix (nonDiagonalMap x) =
      (!![1, 0, 0, 0;
          0, (x / Real.sqrt 3 : ℝ), 0, 0;
          0, 0, (x / Real.sqrt 3 : ℝ), 0;
          (2 / 3 : ℝ), 0, 0, (1 / 3 : ℝ)] : Matrix (Fin 4) (Fin 4) ℝ).map
        Complex.ofReal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliTransferMatrix, pauliTransferEntry,
      nonDiagonalMap_apply hx0 hx1, pauliMatrices, Matrix.trace_fin_two,
      Matrix.mul_apply]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- The displayed map satisfies the existing non-diagonal normal-form
predicate.  This does not assert existence of such a representative in every
filtering orbit. -/
theorem isLorentzNonDiagonal_nonDiagonalMap {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    IsLorentzNonDiagonal (nonDiagonalMap x) := by
  refine ⟨nonDiagonalMap_isChannel hx0 hx1, x, hx0, hx1, ?_, ?_, ?_, ?_, ?_⟩
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 3 0)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    simpa [pauliTransferMatrix] using h
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 1 1)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    simpa [pauliTransferMatrix] using h
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 2 2)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    simpa [pauliTransferMatrix] using h
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 3 3)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    simpa [pauliTransferMatrix] using h
  · intro i j hij htranslation
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M i j)
      (pauliTransferMatrix_nonDiagonalMap hx0 hx1)
    fin_cases i <;> fin_cases j <;> simp_all [pauliTransferMatrix]

/-! ## Choi/Kraus ranks of the displayed family -/

private theorem rank_sum_vecMulVec_eq_card_of_linearIndependent
    {n : Type*} [Fintype n] {r : ℕ} (v : Fin r → n → ℂ)
    (hv : LinearIndependent ℂ v) :
    (∑ i : Fin r, Matrix.vecMulVec (v i) (star (v i))).rank = r := by
  let C : Matrix n (Fin r) ℂ := fun p i ↦ v i p
  have hsum :
      ∑ i : Fin r, Matrix.vecMulVec (v i) (star (v i)) = C * Cᴴ := by
    ext p q
    rw [Matrix.sum_apply, Matrix.mul_apply]
    change (∑ i : Fin r, v i p * star (v i q)) =
      ∑ i : Fin r, v i p * star (v i q)
    rfl
  rw [hsum, Matrix.rank_self_mul_conjTranspose, Matrix.rank_eq_finrank_span_cols]
  change Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = r
  simpa using finrank_span_eq_card hv

private theorem choiRank_mapLM_eq_card_of_linearIndependent {r : ℕ}
    (K : Fin r → QubitMatrix) (hK : LinearIndependent ℂ K) :
    Channel.choiRank (Kraus.mapLM K) = r := by
  let c : ℂ := 1 / ((2 : ℝ).sqrt : ℂ)
  let v : Fin r → (Fin 2 × Fin 2) → ℂ :=
    fun j p ↦ c * K j p.1 p.2
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff] at hK ⊢
    intro g hg i
    apply hK g _ i
    apply Matrix.ext
    intro a b
    have hab := congrFun hg (a, b)
    have hentry : c * (∑ j : Fin r, g j * K j a b) = 0 := by
      simpa [v, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc] using hab
    rw [Matrix.sum_apply, show (0 : QubitMatrix) a b = 0 by rfl]
    simpa only [Matrix.smul_apply, smul_eq_mul] using
      (mul_eq_zero.mp hentry).resolve_left hc
  change (ChoiJamiolkowski.choiMatrix (Kraus.mapLM K)).rank = r
  rw [Channel.choiMatrix_mapLM_eq_sum_vecMulVec]
  exact rank_sum_vecMulVec_eq_card_of_linearIndependent v hv

private theorem nonDiagonalKrausBase_linearIndependent :
    LinearIndependent ℂ nonDiagonalKrausBase := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrArg (fun M : QubitMatrix ↦ M 0 0) hg
  have h11 := congrArg (fun M : QubitMatrix ↦ M 1 1) hg
  have h01 := congrArg (fun M : QubitMatrix ↦ M 0 1) hg
  simp [Fin.sum_univ_three, nonDiagonalKrausBase] at h00 h11 h01
  have hsqrt : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by positivity
  field_simp [hsqrt] at h11
  have hg0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have hg1 : g 1 = 0 := by linear_combination (h00 - h11) / 2
  fin_cases i
  · exact hg0
  · exact hg1
  · exact h01

private theorem nonDiagonalKraus_linearIndependent {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    LinearIndependent ℂ (nonDiagonalKraus x) := by
  have hcoeff : ∀ i : Fin 3, ((nonDiagonalKrausCoefficient x i : ℝ) : ℂ) ≠ 0 := by
    intro i
    apply Complex.ofReal_ne_zero.mpr
    fin_cases i
    · apply Real.sqrt_ne_zero'.2
      nlinarith
    · apply Real.sqrt_ne_zero'.2
      nlinarith
    · apply Real.sqrt_ne_zero'.2
      norm_num
  let u : Fin 3 → ℂˣ := fun i ↦ Units.mk0 _ (hcoeff i)
  have hli := nonDiagonalKrausBase_linearIndependent.units_smul u
  have heq : u • nonDiagonalKrausBase = nonDiagonalKraus x := by
    ext i a b
    rfl
  rw [← heq]
  exact hli

/-- For `0 ≤ x < 1`, all three operators in Equation (19) are needed:
the canonical non-diagonal channel has Choi/Kraus rank three. -/
theorem choiRank_nonDiagonalMap_eq_three {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Channel.choiRank (nonDiagonalMap x) = 3 :=
  choiRank_mapLM_eq_card_of_linearIndependent _
    (nonDiagonalKraus_linearIndependent hx0 hx1)

/-- The two nonzero Kraus operators left by Equation (19) at `x = 1`. -/
def nonDiagonalBoundaryKraus : Fin 2 → QubitMatrix
  | 0 => nonDiagonalKraus 1 0
  | 1 => nonDiagonalKraus 1 2

/-- The middle operator in Equation (19) vanishes at the endpoint `x = 1`. -/
@[simp] theorem nonDiagonalKraus_one_one : nonDiagonalKraus 1 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nonDiagonalKraus, nonDiagonalKrausCoefficient]

/-- At `x = 1`, the middle operator in Equation (19) vanishes and the
three-operator map equals the displayed two-nonzero-operator map. -/
theorem nonDiagonalMap_one_eq_boundaryMap :
    nonDiagonalMap 1 = Kraus.mapLM nonDiagonalBoundaryKraus := by
  apply LinearMap.ext
  intro X
  simp [nonDiagonalMap, Kraus.map_apply, Fin.sum_univ_three,
    Fin.sum_univ_two, nonDiagonalBoundaryKraus, nonDiagonalKraus,
    nonDiagonalKrausCoefficient]
  norm_cast

private theorem nonDiagonalBoundaryKraus_linearIndependent :
    LinearIndependent ℂ nonDiagonalBoundaryKraus := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrArg (fun M : QubitMatrix ↦ M 0 0) hg
  have h01 := congrArg (fun M : QubitMatrix ↦ M 0 1) hg
  have hg0 : g 0 = 0 := by
    simpa [Fin.sum_univ_two, nonDiagonalBoundaryKraus, nonDiagonalKraus,
      nonDiagonalKrausCoefficient, nonDiagonalKrausBase] using h00
  have hg1 : g 1 = 0 := by
    simpa [Fin.sum_univ_two, nonDiagonalBoundaryKraus, nonDiagonalKraus,
      nonDiagonalKrausCoefficient, nonDiagonalKrausBase] using h01
  fin_cases i
  · exact hg0
  · exact hg1

/-- At the endpoint `x = 1`, the canonical non-diagonal channel has
Choi/Kraus rank two, as stated in Wolf, Proposition 2.11. -/
theorem choiRank_nonDiagonalMap_one :
    Channel.choiRank (nonDiagonalMap 1) = 2 := by
  rw [nonDiagonalMap_one_eq_boundaryMap]
  exact choiRank_mapLM_eq_card_of_linearIndependent _
    nonDiagonalBoundaryKraus_linearIndependent

/-! ## The singular constant-output representative -/

/-- The two Kraus operators of the singular representative:
`|0><0|` and `|0><1|`. -/
def singularKraus : Fin 2 → QubitMatrix
  | 0 => !![1, 0; 0, 0]
  | 1 => !![0, 1; 0, 0]

/-- The singular qubit channel of Wolf, Proposition 2.11 case 3. -/
def singularMap : QubitMap :=
  Kraus.mapLM singularKraus

/-- The singular two-operator family is trace preserving. -/
theorem singularKraus_isTP : Kraus.IsTP singularKraus := by
  rw [Kraus.IsTP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [singularKraus, Fin.sum_univ_two, Matrix.mul_apply,
      Matrix.conjTranspose_apply]

/-- The singular representative is a channel. -/
theorem singularMap_isChannel : IsChannel singularMap :=
  Kraus.isChannel_mapLM _ singularKraus_isTP

/-- Exact action of the singular representative on arbitrary matrices.
On density matrices this is the constant output `|0><0|`; on arbitrary
matrices the output is scaled by the input trace. -/
theorem singularMap_apply (X : QubitMatrix) :
    singularMap X = Matrix.trace X • !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [singularMap, Kraus.map_apply, singularKraus, Fin.sum_univ_two,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Matrix.trace_fin_two]

/-- Exact Pauli-transfer matrix of the singular representative in Wolf,
Proposition 2.11 case 3. -/
theorem pauliTransferMatrix_singularMap :
    pauliTransferMatrix singularMap =
      !![1, 0, 0, 0;
         0, 0, 0, 0;
         0, 0, 0, 0;
         1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliTransferMatrix, pauliTransferEntry, singularMap_apply,
      pauliMatrices, Matrix.trace_fin_two, Matrix.mul_apply]

/-- The singular map satisfies the existing singular normal-form predicate. -/
theorem isLorentzSingular_singularMap : IsLorentzSingular singularMap := by
  refine ⟨singularMap_isChannel, ?_, ?_⟩
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M 3 0)
      pauliTransferMatrix_singularMap
    simpa [pauliTransferMatrix] using h
  · intro i j hij
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ ↦ M i j)
      pauliTransferMatrix_singularMap
    fin_cases i <;> fin_cases j <;> simp_all [pauliTransferMatrix]

private theorem singularKraus_linearIndependent :
    LinearIndependent ℂ singularKraus := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h00 := congrArg (fun M : QubitMatrix ↦ M 0 0) hg
  have h01 := congrArg (fun M : QubitMatrix ↦ M 0 1) hg
  have hg0 : g 0 = 0 := by
    simpa [Fin.sum_univ_two, singularKraus] using h00
  have hg1 : g 1 = 0 := by
    simpa [Fin.sum_univ_two, singularKraus] using h01
  fin_cases i
  · exact hg0
  · exact hg1

/-- The singular constant-output channel has Choi/Kraus rank two. -/
theorem choiRank_singularMap : Channel.choiRank singularMap = 2 :=
  choiRank_mapLM_eq_card_of_linearIndependent _ singularKraus_linearIndependent

end Wolf
