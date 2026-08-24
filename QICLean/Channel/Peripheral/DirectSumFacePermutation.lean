/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.FixedPoint.ExtremeDensityStates
import QICLean.Channel.FixedPoint.TraceNonincreasingDirectSum
import QICLean.Channel.Peripheral.PureStateFace
import QICLean.Channel.Wigner.ProjectivePureState

/-!
# Permutation of pure-state faces in finite matrix direct sums

This module follows the extreme-state and continuity argument in Wolf's proof
of Theorem 6.16, lines 1641--1659. Mutually inverse positive
trace-preserving maps between finite direct sums preserve relative pure states.
Connectedness makes the target summand independent of the pure state inside a
fixed source summand, and the inverse map then gives a permutation of summands
with equal full-matrix dimensions.

Only the full-matrix dimensions are compared here. No multiplicity dimension,
complete-positivity hypothesis, Kraus representation, or classification of
the induced block maps is used.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators

noncomputable section

namespace Matrix

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {d : ι → ℕ} {e : κ → ℕ}
variable [∀ i, NeZero (d i)] [∀ j, NeZero (e j)]

/-- Positivity for a linear map between two finite direct sums of full matrix
algebras. -/
def IsPositiveBetweenDirectSums
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)) : Prop :=
  ∀ A, (∀ i, (A i).PosSemidef) → ∀ j, (T A j).PosSemidef

/-- The component from source block `i` to target block `j` of a linear map
between finite matrix direct sums. -/
def directSumBlockMap
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (i : ι) (j : κ) :
    Matrix (Fin (d i)) (Fin (d i)) ℂ →ₗ[ℂ]
      Matrix (Fin (e j)) (Fin (e j)) ℂ where
  toFun X := T (Pi.single i X) j
  map_add' X Y := by
    simp only [Pi.single_add, map_add, Pi.add_apply]
  map_smul' c X := by
    simp only [Pi.single_smul, map_smul, Pi.smul_apply, RingHom.id_apply]

omit [DecidableEq ι] [DecidableEq κ]
    [∀ i, NeZero (d i)] [∀ j, NeZero (e j)] in
/-- A positive total-trace-preserving map sends direct-sum density states to
direct-sum density states. -/
theorem IsPositiveBetweenDirectSums.mapsTo_directSumDensityMatrices
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    (hT : IsPositiveBetweenDirectSums T)
    (hTP : IsTracePreservingBetweenDirectSums T) :
    Set.MapsTo T (directSumDensityMatrices d) (directSumDensityMatrices e) := by
  intro A hA
  exact ⟨hT A hA.1, (hTP A).trans hA.2⟩

omit [DecidableEq ι] [DecidableEq κ]
    [∀ i, NeZero (d i)] [∀ j, NeZero (e j)] in
/-- Mutually inverse positive trace-preserving maps preserve relative pure
states in the forward direction. -/
theorem mapsTo_extremePoints_directSumDensityMatrices_of_mutualInverse
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (hT : IsPositiveBetweenDirectSums T)
    (hS : IsPositiveBetweenDirectSums S)
    (hTTP : IsTracePreservingBetweenDirectSums T)
    (hSTP : IsTracePreservingBetweenDirectSums S)
    (hST : S.comp T = LinearMap.id)
    (hTS : T.comp S = LinearMap.id) :
    Set.MapsTo T
      (Set.extremePoints ℝ (directSumDensityMatrices d))
      (Set.extremePoints ℝ (directSumDensityMatrices e)) := by
  intro P hP
  refine mem_extremePoints_iff_left.mpr ?_
  refine ⟨hT.mapsTo_directSumDensityMatrices hTTP hP.1, ?_⟩
  intro A hA B hB hsegment
  have hSA : S A ∈ directSumDensityMatrices d :=
    hS.mapsTo_directSumDensityMatrices hSTP hA
  have hSB : S B ∈ directSumDensityMatrices d :=
    hS.mapsTo_directSumDensityMatrices hSTP hB
  rcases hsegment with ⟨a, b, ha, hb, hab, hcombo⟩
  have hsegmentS : P ∈ openSegment ℝ (S A) (S B) := by
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hcomboC : (a : ℂ) • A + (b : ℂ) • B = T P := by
      simpa only [Complex.coe_smul] using hcombo
    calc
      a • S A + b • S B = (a : ℂ) • S A + (b : ℂ) • S B := by
        simp only [Complex.coe_smul]
      _ = S ((a : ℂ) • A + (b : ℂ) • B) := by
        rw [map_add, map_smul, map_smul]
      _ = S (T P) := congrArg S hcomboC
      _ = P := LinearMap.congr_fun hST P
  have hSAeq : S A = P := hP.2 hSA hSB hsegmentS
  calc
    A = T (S A) := (LinearMap.congr_fun hTS A).symm
    _ = T P := congrArg T hSAeq

omit [∀ i, NeZero (d i)] [∀ j, NeZero (e j)] in
private theorem exists_targetBlock_of_rankOne
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    (hT : Set.MapsTo T
      (Set.extremePoints ℝ (directSumDensityMatrices d))
      (Set.extremePoints ℝ (directSumDensityMatrices e)))
    (i : ι) {P : Matrix (Fin (d i)) (Fin (d i)) ℂ}
    (hP : IsRankOneOrthogonalProjection P) :
    ∃ j Q, IsRankOneOrthogonalProjection Q ∧
      T (Pi.single i P) = Pi.single j Q := by
  have hout := hT
    ((mem_extremePoints_directSumDensityMatrices_iff (d := d)).mpr
      ⟨i, P, hP, rfl⟩)
  exact (mem_extremePoints_directSumDensityMatrices_iff (d := e)).mp hout

omit [∀ j, NeZero (e j)] in
private theorem exists_targetBlock_assignment
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    (hT : Set.MapsTo T
      (Set.extremePoints ℝ (directSumDensityMatrices d))
      (Set.extremePoints ℝ (directSumDensityMatrices e))) :
    ∃ τ : ι → κ, ∀ i P, IsRankOneOrthogonalProjection P →
      ∃ Q, IsRankOneOrthogonalProjection Q ∧
        T (Pi.single i P) = Pi.single (τ i) Q := by
  classical
  have hassignment : ∀ i, ∃ j, ∀ P, IsRankOneOrthogonalProjection P →
      ∃ Q, IsRankOneOrthogonalProjection Q ∧
        T (Pi.single i P) = Pi.single j Q := by
    intro i
    let C : Set (Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
      pureStateProj '' {psi : Fin (d i) → ℂ | IsUnitVector psi}
    have hC : IsConnected C := isConnected_pureStateProj_image (NeZero.pos (d i))
    obtain ⟨P₀, hP₀⟩ := hC.nonempty
    rcases hP₀ with ⟨psi₀, hpsi₀, rfl⟩
    have hproj₀ : IsRankOneOrthogonalProjection (pureStateProj psi₀) :=
      hpsi₀.isRankOneOrthogonalProjection_pureStateProj
    obtain ⟨j₀, Q₀, hQ₀, hout₀⟩ := exists_targetBlock_of_rankOne hT i hproj₀
    refine ⟨j₀, ?_⟩
    intro P hP
    obtain ⟨psi, hpsi, hpsiP⟩ :=
      IsRankOneOrthogonalProjection.exists_isUnitVector_pureStateProj hP
    subst P
    obtain ⟨j, Q, hQ, hout⟩ := exists_targetBlock_of_rankOne hT i
      hpsi.isRankOneOrthogonalProjection_pureStateProj
    have hfContinuous : Continuous (fun X : Matrix (Fin (d i)) (Fin (d i)) ℂ ↦
        (T (Pi.single i X) j₀).trace.re) :=
      Complex.continuous_re.comp
        ((directSumBlockMap T i j₀).continuous_of_finiteDimensional.matrix_trace)
    have hfMapsTo : Set.MapsTo
        (fun X : Matrix (Fin (d i)) (Fin (d i)) ℂ ↦
          (T (Pi.single i X) j₀).trace.re)
        C ({0, 1} : Set ℝ) := by
      rintro X ⟨phi, hphi, rfl⟩
      obtain ⟨l, R, hR, houtR⟩ := exists_targetBlock_of_rankOne hT i
        hphi.isRankOneOrthogonalProjection_pureStateProj
      change (T (Pi.single i (pureStateProj phi)) j₀).trace.re ∈ ({0, 1} : Set ℝ)
      by_cases hl : j₀ = l
      · subst l
        rw [houtR, Pi.single_eq_same]
        simp [IsRankOneOrthogonalProjection.mem_densityMatrices hR |>.2]
      · rw [houtR, Pi.single_eq_of_ne hl]
        simp
    have hfEq := hC.isPreconnected.constant_of_mapsTo
      (Set.toFinite ({0, 1} : Set ℝ)).isDiscrete hfContinuous.continuousOn hfMapsTo
      ⟨psi, hpsi, rfl⟩ ⟨psi₀, hpsi₀, rfl⟩
    have hf₀ : (T (Pi.single i (pureStateProj psi₀)) j₀).trace.re = 1 := by
      rw [hout₀, Pi.single_eq_same]
      simp [IsRankOneOrthogonalProjection.mem_densityMatrices hQ₀ |>.2]
    have hf : (T (Pi.single i (pureStateProj psi)) j₀).trace.re = 1 := hfEq.trans hf₀
    have hj : j = j₀ := by
      by_contra hj
      have hj₀ : j₀ ≠ j := Ne.symm hj
      have hfzero : (T (Pi.single i (pureStateProj psi)) j₀).trace.re = 0 := by
        rw [hout, Pi.single_eq_of_ne hj₀]
        simp
      linarith
    subst j
    exact ⟨Q, hQ, hout⟩
  choose τ hτ using hassignment
  exact ⟨τ, hτ⟩

private theorem isRankOneOrthogonalProjection_pureStateMatrix
    (p : Projectivization ℂ (Fin D → ℂ)) :
    IsRankOneOrthogonalProjection (Projectivization.pureStateMatrix p) := by
  have hP := Projectivization.isOrthogonalProjection_pureStateMatrix p
  refine ⟨hP, ?_⟩
  have hrank := hP.1.rank_eq_trace_re_of_idem hP.2
  rw [Projectivization.trace_pureStateMatrix] at hrank
  norm_num at hrank ⊢
  exact_mod_cast hrank

omit [Fintype ι] [Fintype κ]
    [∀ i, NeZero (d i)] [∀ j, NeZero (e j)] in
private theorem directSumBlockMap_eq_zero_of_ne
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {τ : ι → κ}
    (hτ : ∀ i P, IsRankOneOrthogonalProjection P →
      ∃ Q, IsRankOneOrthogonalProjection Q ∧
        T (Pi.single i P) = Pi.single (τ i) Q)
    (i : ι) {j : κ} (hj : j ≠ τ i) :
    directSumBlockMap T i j = 0 := by
  apply Projectivization.linearMap_eq_of_eq_on_pureStateMatrix
  intro p
  obtain ⟨Q, hQ, hout⟩ := hτ i (Projectivization.pureStateMatrix p)
    (isRankOneOrthogonalProjection_pureStateMatrix p)
  change T (Pi.single i (Projectivization.pureStateMatrix p)) j = 0
  rw [hout, Pi.single_eq_of_ne hj]

omit [Fintype ι] [Fintype κ]
    [∀ i, NeZero (d i)] [∀ j, NeZero (e j)] in
private theorem map_single_eq_single_targetBlock
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {τ : ι → κ}
    (hτ : ∀ i P, IsRankOneOrthogonalProjection P →
      ∃ Q, IsRankOneOrthogonalProjection Q ∧
        T (Pi.single i P) = Pi.single (τ i) Q)
    (i : ι) (X : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    T (Pi.single i X) = Pi.single (τ i) (directSumBlockMap T i (τ i) X) := by
  classical
  funext j
  by_cases hj : j = τ i
  · subst j
    rw [Pi.single_eq_same]
    rfl
  · rw [Pi.single_eq_of_ne hj]
    exact LinearMap.congr_fun (directSumBlockMap_eq_zero_of_ne hτ i hj) X

private theorem exists_rankOneOrthogonalProjection (D : ℕ) [NeZero D] :
    ∃ P : Matrix (Fin D) (Fin D) ℂ, IsRankOneOrthogonalProjection P := by
  have hC := isConnected_pureStateProj_image (NeZero.pos D)
  obtain ⟨P, psi, hpsi, rfl⟩ := hC.nonempty
  exact ⟨pureStateProj psi,
    hpsi.isRankOneOrthogonalProjection_pureStateProj⟩

omit [Fintype ι] [∀ i, NeZero (d i)] in
private theorem index_eq_of_single_eq_single_rankOne
    {a b : ι} {P : Matrix (Fin (d a)) (Fin (d a)) ℂ}
    {Q : Matrix (Fin (d b)) (Fin (d b)) ℂ}
    (hP : IsRankOneOrthogonalProjection P)
    (heq : (Pi.single a P : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) =
      Pi.single b Q) : a = b := by
  classical
  by_contra hab
  have hsame :
      (Pi.single a P : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) a = P :=
    by simp only [Pi.single_eq_same]
  have hdiff :
      (Pi.single b Q : ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) a = 0 :=
    by simp only [Pi.single_eq_of_ne hab]
  have hzero : P = 0 := hsame.symm.trans ((congrFun heq a).trans hdiff)
  have hrank := hP.2
  rw [hzero] at hrank
  simp at hrank

omit [∀ i, NeZero (d i)] in
private theorem sum_trace_pi_single
    (i : ι) (X : Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    ∑ k, ((Pi.single i X : ∀ l, Matrix (Fin (d l)) (Fin (d l)) ℂ) k).trace =
      X.trace := by
  classical
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro k _ hki
    rw [Pi.single_eq_of_ne hki, Matrix.trace_zero]
  · simp

/-- The block permutation and the induced maps supplied by Wolf's pure-face
argument for mutually inverse positive trace-preserving direct-sum maps.

The field `dimension_eq` compares only the full-matrix dimensions. -/
structure DirectSumFacePermutation
    (T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ))
    (S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) where
  /-- The permutation of full-matrix summands. -/
  blockEquiv : ι ≃ κ
  /-- The forward map is supported on the matched target summand. -/
  map_single : ∀ i X,
    T (Pi.single i X) =
      Pi.single (blockEquiv i) (directSumBlockMap T i (blockEquiv i) X)
  /-- The inverse map is supported on the matched source summand. -/
  inverse_map_single : ∀ j Y,
    S (Pi.single j Y) =
      Pi.single (blockEquiv.symm j)
        (directSumBlockMap S j (blockEquiv.symm j) Y)
  /-- A matched forward block map is positive. -/
  blockMap_pos : ∀ i X, X.PosSemidef →
    (directSumBlockMap T i (blockEquiv i) X).PosSemidef
  /-- A matched inverse block map is positive. -/
  inverseBlockMap_pos : ∀ j Y, Y.PosSemidef →
    (directSumBlockMap S j (blockEquiv.symm j) Y).PosSemidef
  /-- A matched forward block map preserves the ordinary matrix trace. -/
  blockMap_trace : ∀ i X,
    (directSumBlockMap T i (blockEquiv i) X).trace = X.trace
  /-- A matched inverse block map preserves the ordinary matrix trace. -/
  inverseBlockMap_trace : ∀ j Y,
    (directSumBlockMap S j (blockEquiv.symm j) Y).trace = Y.trace
  /-- The matched inverse block map is a left inverse. -/
  blockMap_leftInverse : ∀ i X,
    directSumBlockMap S (blockEquiv i) i
      (directSumBlockMap T i (blockEquiv i) X) = X
  /-- The matched inverse block map is a right inverse. -/
  blockMap_rightInverse : ∀ i Y,
    directSumBlockMap T i (blockEquiv i)
      (directSumBlockMap S (blockEquiv i) i Y) = Y
  /-- Matched full-matrix summands have equal dimensions. -/
  dimension_eq : ∀ i, d i = e (blockEquiv i)

/-- Mutually inverse positive trace-preserving maps between finite direct sums
permute the full-matrix summands and induce mutually inverse positive
trace-preserving maps on each matched pair.

This is the pure-state-face and dimension-matching conclusion in Wolf's proof
of Theorem 6.16, lines 1641--1659. It does not compare the later multiplicity
dimensions. -/
theorem exists_directSumFacePermutation_of_mutualInverse
    {T : (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₗ[ℂ]
      (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ)}
    {S : (∀ j, Matrix (Fin (e j)) (Fin (e j)) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)}
    (hT : IsPositiveBetweenDirectSums T)
    (hS : IsPositiveBetweenDirectSums S)
    (hTTP : IsTracePreservingBetweenDirectSums T)
    (hSTP : IsTracePreservingBetweenDirectSums S)
    (hST : S.comp T = LinearMap.id)
    (hTS : T.comp S = LinearMap.id) :
    Nonempty (DirectSumFacePermutation T S) := by
  classical
  have hTextreme :=
    mapsTo_extremePoints_directSumDensityMatrices_of_mutualInverse
      hT hS hTTP hSTP hST hTS
  have hSextreme :=
    mapsTo_extremePoints_directSumDensityMatrices_of_mutualInverse
      hS hT hSTP hTTP hTS hST
  obtain ⟨τ, hτ⟩ := exists_targetBlock_assignment hTextreme
  obtain ⟨υ, hυ⟩ := exists_targetBlock_assignment hSextreme
  have hυτ : Function.LeftInverse υ τ := by
    intro i
    obtain ⟨P, hP⟩ := exists_rankOneOrthogonalProjection (d i)
    obtain ⟨Q, hQ, houtT⟩ := hτ i P hP
    obtain ⟨R, hR, houtS⟩ := hυ (τ i) Q hQ
    symm
    apply index_eq_of_single_eq_single_rankOne hP
    calc
      Pi.single i P = S (T (Pi.single i P)) :=
        (LinearMap.congr_fun hST (Pi.single i P)).symm
      _ = S (Pi.single (τ i) Q) := congrArg S houtT
      _ = Pi.single (υ (τ i)) R := houtS
  have hτυ : Function.RightInverse υ τ := by
    intro j
    obtain ⟨Q, hQ⟩ := exists_rankOneOrthogonalProjection (e j)
    obtain ⟨P, hP, houtS⟩ := hυ j Q hQ
    obtain ⟨R, hR, houtT⟩ := hτ (υ j) P hP
    symm
    apply index_eq_of_single_eq_single_rankOne hQ
    calc
      Pi.single j Q = T (S (Pi.single j Q)) :=
        (LinearMap.congr_fun hTS (Pi.single j Q)).symm
      _ = T (Pi.single (υ j) P) := congrArg T houtS
      _ = Pi.single (τ (υ j)) R := houtT
  let σ : ι ≃ κ := ⟨τ, υ, hυτ, hτυ⟩
  have hmap : ∀ i X,
      T (Pi.single i X) =
        Pi.single (σ i) (directSumBlockMap T i (σ i) X) := by
    intro i X
    exact map_single_eq_single_targetBlock hτ i X
  have hmapS : ∀ j Y,
      S (Pi.single j Y) =
        Pi.single (σ.symm j) (directSumBlockMap S j (σ.symm j) Y) := by
    intro j Y
    exact map_single_eq_single_targetBlock hυ j Y
  have hposT : ∀ i X, X.PosSemidef →
      (directSumBlockMap T i (σ i) X).PosSemidef := by
    intro i X hX
    apply hT (Pi.single i X) _ (σ i)
    intro k
    by_cases hk : k = i
    · subst k
      simpa only [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hk]
      exact PosSemidef.zero
  have hposS : ∀ j Y, Y.PosSemidef →
      (directSumBlockMap S j (σ.symm j) Y).PosSemidef := by
    intro j Y hY
    apply hS (Pi.single j Y) _ (σ.symm j)
    intro l
    by_cases hl : l = j
    · subst l
      simpa only [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hl]
      exact PosSemidef.zero
  have htraceT : ∀ i X,
      (directSumBlockMap T i (σ i) X).trace = X.trace := by
    intro i X
    calc
      (directSumBlockMap T i (σ i) X).trace =
          ∑ j, ((Pi.single (σ i) (directSumBlockMap T i (σ i) X) :
            ∀ l, Matrix (Fin (e l)) (Fin (e l)) ℂ) j).trace :=
        (sum_trace_pi_single (σ i) (directSumBlockMap T i (σ i) X)).symm
      _ = ∑ j, (T (Pi.single i X) j).trace :=
        congrArg (fun A ↦ ∑ j, (A j).trace) (hmap i X).symm
      _ = ∑ k, ((Pi.single i X :
          ∀ l, Matrix (Fin (d l)) (Fin (d l)) ℂ) k).trace :=
        hTTP (Pi.single i X)
      _ = X.trace := sum_trace_pi_single i X
  have htraceS : ∀ j Y,
      (directSumBlockMap S j (σ.symm j) Y).trace = Y.trace := by
    intro j Y
    calc
      (directSumBlockMap S j (σ.symm j) Y).trace =
          ∑ i, ((Pi.single (σ.symm j)
            (directSumBlockMap S j (σ.symm j) Y) :
              ∀ l, Matrix (Fin (d l)) (Fin (d l)) ℂ) i).trace :=
        (sum_trace_pi_single (σ.symm j)
          (directSumBlockMap S j (σ.symm j) Y)).symm
      _ = ∑ i, (S (Pi.single j Y) i).trace :=
        congrArg (fun A ↦ ∑ i, (A i).trace) (hmapS j Y).symm
      _ = ∑ l, ((Pi.single j Y :
          ∀ k, Matrix (Fin (e k)) (Fin (e k)) ℂ) l).trace :=
        hSTP (Pi.single j Y)
      _ = Y.trace := sum_trace_pi_single j Y
  have hleftBlock : ∀ i X,
      directSumBlockMap S (σ i) i
        (directSumBlockMap T i (σ i) X) = X := by
    intro i X
    change S (Pi.single (σ i) (directSumBlockMap T i (σ i) X)) i = X
    calc
      S (Pi.single (σ i) (directSumBlockMap T i (σ i) X)) i =
          S (T (Pi.single i X)) i := congrFun (congrArg S (hmap i X).symm) i
      _ = ((Pi.single i X :
          ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ) i) := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          congrFun (LinearMap.congr_fun hST (Pi.single i X)) i
      _ = X := by simp only [Pi.single_eq_same]
  have hTblockInjective : ∀ i,
      Function.Injective (directSumBlockMap T i (σ i)) := by
    intro i X Y hXY
    calc
      X = directSumBlockMap S (σ i) i
          (directSumBlockMap T i (σ i) X) := (hleftBlock i X).symm
      _ = directSumBlockMap S (σ i) i
          (directSumBlockMap T i (σ i) Y) := congrArg _ hXY
      _ = Y := hleftBlock i Y
  have hSinjective : Function.Injective S := by
    intro A B hAB
    calc
      A = T (S A) := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          (LinearMap.congr_fun hTS A).symm
      _ = T (S B) := congrArg T hAB
      _ = B := by
        simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
          LinearMap.congr_fun hTS B
  have hSblockInjective : ∀ j,
      Function.Injective (directSumBlockMap S j (σ.symm j)) := by
    intro j X Y hXY
    have hfull : S (Pi.single j X) = S (Pi.single j Y) := by
      calc
        S (Pi.single j X) = Pi.single (σ.symm j)
            (directSumBlockMap S j (σ.symm j) X) := hmapS j X
        _ = Pi.single (σ.symm j)
            (directSumBlockMap S j (σ.symm j) Y) :=
          congrArg (fun Z ↦ (Pi.single (σ.symm j) Z :
            ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)) hXY
        _ = S (Pi.single j Y) := (hmapS j Y).symm
    have hsingle := hSinjective hfull
    have hcoord := congrFun hsingle j
    simpa only [Pi.single_eq_same] using hcoord
  have hdim : ∀ i, d i = e (σ i) := by
    intro i
    have hleT := LinearMap.finrank_le_finrank_of_injective
      (hTblockInjective i)
    have hleS := LinearMap.finrank_le_finrank_of_injective
      (hSblockInjective (σ i))
    rw [Module.finrank_matrix, Module.finrank_matrix] at hleT hleS
    simp only [Module.finrank_self, Fintype.card_fin, mul_one,
      Equiv.symm_apply_apply] at hleT hleS
    exact Nat.mul_self_inj.mp (le_antisymm hleT hleS)
  have hrightBlock : ∀ i Y,
      directSumBlockMap T i (σ i)
        (directSumBlockMap S (σ i) i Y) = Y := by
    intro i Y
    have hfinrank : Module.finrank ℂ
        (Matrix (Fin (d i)) (Fin (d i)) ℂ) =
        Module.finrank ℂ (Matrix (Fin (e (σ i))) (Fin (e (σ i))) ℂ) := by
      rw [Module.finrank_matrix, Module.finrank_matrix]
      simp only [Module.finrank_self, Fintype.card_fin, mul_one, hdim i]
    have hsurjective : Function.Surjective (directSumBlockMap T i (σ i)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfinrank).mp
        (hTblockInjective i)
    obtain ⟨X, hX⟩ := hsurjective Y
    rw [← hX, hleftBlock]
  exact ⟨{
    blockEquiv := σ
    map_single := hmap
    inverse_map_single := hmapS
    blockMap_pos := hposT
    inverseBlockMap_pos := hposS
    blockMap_trace := htraceT
    inverseBlockMap_trace := htraceS
    blockMap_leftInverse := hleftBlock
    blockMap_rightInverse := hrightBlock
    dimension_eq := hdim }⟩

end Matrix
