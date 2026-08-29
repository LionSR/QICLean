/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Semigroup.KossakowskiRank
import QICLean.Channel.Semigroup.ReducibleQDS.Equivalence

/-!
# Wolf Corollary 7.2 — Sufficient conditions for non-reducibility

This module states three standard sufficient-condition patterns from
Wolf Corollary 7.2, each using the already formalized implication

`¬ HasBlockUpperTriangularLindblad L → ¬ IsReducibleQDS L`.

The conversion from each algebraic hypothesis to
`¬ HasBlockUpperTriangularLindblad` is stated as auxiliary lemmas
(`*_implies_no_blockUpperTriangular`) so later files can use uniform
non-reducibility consequences.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace
open Matrix Finset Module

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The Lindblad span is closed under Hermitian conjugation, i.e. the `ℂ`-span
of the Lindblad operators `{Lⱼ}` forms a `*`-subspace of `Mₐ(ℂ)`:
for every `X = ∑ xⱼ Lⱼ` there exist `yⱼ` such that `X† = ∑ yⱼ Lⱼ`.
This is the Hermiticity condition appearing in Wolf Corollary 7.2(2). -/
def IsLindbladSpanHermitianClosed (F : LindbladForm D) : Prop :=
  ∀ A : Mat, A ∈ lindbladSpan F → Aᴴ ∈ lindbladSpan F

/-- The commutant of the Lindblad family contains only scalar multiples of the
identity: `{Lⱼ}' = ℂ · 𝟙`.  This means the Lindblad operators act
irreducibly on the matrix algebra `Mₐ(ℂ)`.
This is the trivial-commutant condition appearing in Wolf Corollary 7.2(2). -/
def HasLindbladSpanTrivialCommutant (F : LindbladForm D) : Prop :=
  ∀ A : Mat,
    (∀ j : Fin F.r, A * F.L j = F.L j * A) →
      ∃ c : ℂ, A = c • (1 : Mat)

private theorem lower_left_block_vanishes_on_lindbladSpan
    {P : Mat} (F : LindbladForm D)
    (hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0) :
    ∀ A : Mat, A ∈ lindbladSpan F → (1 - P) * A * P = 0 := by
  intro A hA
  induction hA using Submodule.span_induction with
  | mem B hB =>
      rcases hB with ⟨j, rfl⟩
      exact hblock j
  | zero =>
      simp
  | add A B _ _ hA hB =>
      rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
      simp
  | smul c A _ hA =>
      rw [mul_smul_comm, smul_mul_assoc, hA, smul_zero]

private theorem not_isNontrivialProjection_of_eq_smul_one
    {P : Mat} (hP_nt : IsNontrivialProjection P) {c : ℂ}
    (hP : P = c • (1 : Mat)) : False := by
  by_cases hD : D = 0
  · subst hD
    exact hP_nt.2.1 (Subsingleton.elim _ _)
  · have : NeZero D := ⟨hD⟩
    have hIdem : (c • (1 : Mat)) * (c • (1 : Mat)) = c • (1 : Mat) := by
      simpa [hP] using hP_nt.1.2
    have hc : c * c = c := by
      have h00 := congrFun (congrFun hIdem 0) 0
      simpa using h00
    have hc01 : c = 0 ∨ c = 1 :=
      IsIdempotentElem.iff_eq_zero_or_one.mp hc
    rcases hc01 with hc0 | hc1
    · exact hP_nt.2.1 (by rw [hP, hc0, zero_smul])
    · exact hP_nt.2.2 (by rw [hP, hc1, one_smul])

/-- If an orthogonal projection has vanishing lower-left block on a set of
matrices, then that block vanishes on the entire unital algebra they generate. -/
theorem lower_left_block_vanishes_on_adjoin
    {P : Mat} (hP : IsOrthogonalProjection P) (S : Set Mat)
    (hS : ∀ A : Mat, A ∈ S → (1 - P) * A * P = 0) :
    ∀ A : Mat, A ∈ Algebra.adjoin ℂ S → (1 - P) * A * P = 0 := by
  have hQP := IsIdempotentElem.one_sub_mul_self hP.2
  have hblock_mul :
      ∀ A B : Mat,
        (1 - P) * A * P = 0 →
          (1 - P) * B * P = 0 →
            (1 - P) * (A * B) * P = 0 := by
    intro A B hA hB
    calc
      (1 - P) * (A * B) * P = (1 - P) * A * B * P := by
        simp [Matrix.mul_assoc]
      _ = (1 - P) * A * (P + (1 - P)) * B * P := by
        rw [show (1 : Mat) = P + (1 - P) by abel]
        simp [Matrix.mul_assoc]
      _ = (1 - P) * A * P * B * P + (1 - P) * A * (1 - P) * B * P := by
        noncomm_ring
      _ = (1 - P) * A * (1 - P) * B * P := by
        simp [hA, Matrix.mul_assoc]
      _ = (1 - P) * A * ((1 - P) * B * P) := by
        simp [Matrix.mul_assoc]
      _ = 0 := by simp [hB]
  intro A hA
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
      exact hS A hA
  | algebraMap c =>
      calc
        (1 - P) * algebraMap ℂ Mat c * P = (1 - P) * (c • (1 : Mat)) * P := by
          rw [Algebra.algebraMap_eq_smul_one]
        _ = c • ((1 - P) * (1 : Mat) * P) := by
          simp
        _ = 0 := by simp [hQP]
  | add A B _ _ hA hB =>
      rw [Matrix.mul_add, Matrix.add_mul, hA, hB]
      simp
  | mul A B _ _ hA hB =>
      exact hblock_mul A B hA hB

/--
Condition (1): full algebra generation by the Lindblad operators together with
`κ = F.toGeneratorDecomp.κ` forbids block-upper-triangular Lindblad
decompositions.
-/
theorem full_algebra_generation_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hGen : Algebra.adjoin ℂ
      (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) = ⊤) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  intro hBlock
  obtain ⟨P, hP_nt, hT⟩ :=
    hasInvariantCompression_of_hasBlockUpperTriangularLindblad hBlock
  have hgen : GeneratorPreservesCompression F.toLinearMap P :=
    generatorPreservesCompression_of_semigroupPreservesCompression hP_nt.1 hT
  have hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0 :=
    lindblad_block_of_generatorPreservesCompression hP_nt.1 F hgen
  have hκ_block : (1 - P) * F.toGeneratorDecomp.κ * P = 0 :=
    kappa_block_of_generatorPreservesCompression hP_nt.1 F hgen hblock
  have hblock_adjoin :
      ∀ A : Mat, A ∈ Algebra.adjoin ℂ
        (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) →
          (1 - P) * A * P = 0 := by
    apply lower_left_block_vanishes_on_adjoin hP_nt.1
    intro A hA
    rcases hA with hA | hA
    · rcases hA with ⟨j, rfl⟩
      exact hblock j
    · simp only [Set.mem_singleton_iff] at hA
      rw [hA]
      exact hκ_block
  have hall : ∀ A : Mat, (1 - P) * A * P = 0 := by
    intro A
    exact hblock_adjoin A (hGen ▸ Algebra.mem_top)
  rcases proj_zero_or_one_of_sandwich P hall with hP0 | hP1
  · exact hP_nt.2.1 hP0
  · exact hP_nt.2.2 hP1

/--
Condition (2): Hermitian closure of the Lindblad span together with trivial
commutant forbids block-upper-triangular Lindblad decompositions.
-/
theorem hermitian_span_trivial_commutant_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hHerm : IsLindbladSpanHermitianClosed F)
    (hComm : HasLindbladSpanTrivialCommutant F) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  intro hBlock
  obtain ⟨P, hP_nt, hT⟩ :=
    hasInvariantCompression_of_hasBlockUpperTriangularLindblad hBlock
  have hgen : GeneratorPreservesCompression F.toLinearMap P :=
    generatorPreservesCompression_of_semigroupPreservesCompression hP_nt.1 hT
  have hblock : ∀ j : Fin F.r, (1 - P) * F.L j * P = 0 :=
    lindblad_block_of_generatorPreservesCompression hP_nt.1 F hgen
  have hblock_span : ∀ A : Mat, A ∈ lindbladSpan F → (1 - P) * A * P = 0 :=
    lower_left_block_vanishes_on_lindbladSpan F hblock
  have hP_herm : Pᴴ = P := hP_nt.1.1
  have hP_add_compl : P + (1 - P) = (1 : Mat) := by
    abel
  have hcommP : ∀ j : Fin F.r, P * F.L j = F.L j * P := by
    intro j
    have hLj_mem : F.L j ∈ lindbladSpan F :=
      Submodule.subset_span ⟨j, rfl⟩
    have hLj_star_mem : (F.L j)ᴴ ∈ lindbladSpan F := hHerm _ hLj_mem
    have hPAQ : P * F.L j * (1 - P) = 0 := by
      have hct := congrArg Matrix.conjTranspose (hblock_span _ hLj_star_mem)
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_one, Matrix.conjTranspose_zero, hP_herm] at hct
      simpa [Matrix.mul_assoc] using hct
    have hleft : P * F.L j = P * F.L j * P := by
      calc
        P * F.L j = P * F.L j * 1 := by simp
        _ = P * F.L j * (P + (1 - P)) := by
          rw [hP_add_compl]
        _ = P * F.L j * P + P * F.L j * (1 - P) := by rw [Matrix.mul_add]
        _ = P * F.L j * P := by rw [hPAQ, add_zero]
    have hright : F.L j * P = P * F.L j * P := by
      calc
        F.L j * P = 1 * (F.L j * P) := by simp
        _ = (P + (1 - P)) * (F.L j * P) := by
          rw [hP_add_compl]
        _ = P * (F.L j * P) + (1 - P) * (F.L j * P) := by rw [Matrix.add_mul]
        _ = P * F.L j * P + (1 - P) * F.L j * P := by simp [Matrix.mul_assoc]
        _ = P * F.L j * P := by rw [hblock j, add_zero]
    exact hleft.trans hright.symm
  obtain ⟨c, hP_scalar⟩ := hComm P hcommP
  exact not_isNontrivialProjection_of_eq_smul_one hP_nt hP_scalar

/-- If `1 ∈ ker φ`, then every matrix splits as a scalar multiple of `1`
plus a traceless element, so `ker φ ⊔ ker(trace) = ⊤`. -/
private theorem ker_sup_traceless_eq_top_of_one_mem_ker
    (φ : Mat →ₗ[ℂ] Mat)
    (hφ_one : φ (1 : Mat) = 0)
    (hD_ne : (D : ℂ) ≠ 0) :
    LinearMap.ker φ ⊔
      LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ) = ⊤ := by
  let τ : Mat →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin D) ℂ ℂ
  have hI_in_ker : (1 : Mat) ∈ LinearMap.ker φ := LinearMap.mem_ker.mpr hφ_one
  have htrI : τ (1 : Mat) = (D : ℂ) := by
    change Matrix.trace (1 : Mat) = _
    simp [Matrix.trace_one, Fintype.card_fin]
  rw [eq_top_iff]
  intro x _
  have hmem_trace :
      x - (τ x / (D : ℂ)) • (1 : Mat) ∈ LinearMap.ker τ := by
    rw [LinearMap.mem_ker, map_sub, map_smul, htrI, smul_eq_mul,
      div_mul_cancel₀ _ hD_ne, sub_self]
  have hmem_phi : ((τ x / (D : ℂ)) • (1 : Mat)) ∈ LinearMap.ker φ :=
    Submodule.smul_mem _ _ hI_in_ker
  have hdecomp :
      x = (τ x / (D : ℂ)) • (1 : Mat) +
        (x - (τ x / (D : ℂ)) • (1 : Mat)) := by
    rw [add_sub_cancel]
  rw [hdecomp]
  exact Submodule.add_mem_sup hmem_phi hmem_trace

/-- The traceless subspace of `Mat` has codimension `1`. -/
private theorem finrank_traceless_submodule
    (hD : D ≠ 0) :
    Module.finrank ℂ
      (LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ)) = D * D - 1 := by
  have : NeZero D := ⟨hD⟩
  let τ : Mat →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin D) ℂ ℂ
  have hfin_mat : Module.finrank ℂ Mat = D * D := by
    simp [Module.finrank_matrix, Fintype.card_fin]
  have hD_ne : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have htrI : τ (1 : Mat) = (D : ℂ) := by
    change Matrix.trace (1 : Mat) = _
    simp [Matrix.trace_one, Fintype.card_fin]
  have h_rn := τ.finrank_range_add_finrank_ker
  rw [hfin_mat] at h_rn
  have h_range : Module.finrank ℂ (LinearMap.range τ) = 1 := by
    have : LinearMap.range τ = ⊤ := by
      rw [LinearMap.range_eq_top]
      intro c
      refine ⟨(c / (D : ℂ)) • (1 : Mat), ?_⟩
      rw [map_smul, htrI, smul_eq_mul, div_mul_cancel₀ c hD_ne]
    rw [this, finrank_top]
    exact Module.finrank_self ℂ
  rw [h_range] at h_rn
  change Module.finrank ℂ (LinearMap.ker τ) = D * D - 1
  omega

/-- The eigenvalues of an orthogonal projection are all `0` or `1`. -/
private theorem projection_eigenvalues_zero_or_one
    {P : Mat} (hP : IsNontrivialProjection P) :
    ∀ i : Fin D, hP.1.1.eigenvalues i = 0 ∨ hP.1.1.eigenvalues i = 1 := by
  intro i
  have hIdem : IsIdempotentElem P := hP.1.2
  have := hIdem.spectrum_subset ℝ
    (hP.1.1.eigenvalues_mem_spectrum_real i)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  exact this

/-- A nontrivial orthogonal projection has both a `1`-eigenvalue and a
missing `1`-eigenvalue. -/
private theorem projection_one_eigenvalue_card_bounds
    {P : Mat} (hP : IsNontrivialProjection P) :
    let eig := hP.1.1.eigenvalues
    let k := (Finset.univ.filter (fun i => eig i = 1)).card
    1 ≤ k ∧ k < D := by
  set eig := hP.1.1.eigenvalues
  set k := (Finset.univ.filter (fun i => eig i = 1)).card
  have heig_01 : ∀ i : Fin D, eig i = 0 ∨ eig i = 1 := by
    simpa [eig] using projection_eigenvalues_zero_or_one (D := D) hP
  have hk_le : k ≤ D := Finset.card_filter_le _ _ |>.trans (by simp [Fintype.card_fin])
  have hk_pos : 1 ≤ k := by
    by_contra h
    push Not at h
    have hk_zero : k = 0 := by omega
    have hall_zero : ∀ i, eig i = 0 := by
      intro i
      rcases heig_01 i with hi | hi
      · exact hi
      · exfalso
        have : i ∈ Finset.univ.filter (fun i => eig i = 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        simp [Finset.card_eq_zero.mp hk_zero] at this
    have htr : P.trace = 0 := by
      rw [hP.1.1.trace_eq_sum_eigenvalues]
      simp [eig, hall_zero]
    exact hP.2.1 ((isOrthogonalProjection_posSemidef hP.1).trace_eq_zero_iff.mp htr)
  have hk_lt_D : k < D := by
    by_contra h
    push Not at h
    have hk_eq : k = D := le_antisymm hk_le h
    have hall_one : ∀ i, eig i = 1 := by
      intro i
      rcases heig_01 i with hi | hi
      · exfalso
        have hi_not : i ∉ Finset.univ.filter (fun j => eig j = 1) :=
          Finset.mem_filter.not.mpr (by
            push Not
            intro _
            linarith)
        have : (Finset.univ.filter (fun j => eig j = 1)).card < Finset.univ.card :=
          Finset.card_lt_card ⟨
            Finset.filter_subset _ _,
            fun hsub => hi_not (hsub (Finset.mem_univ _))⟩
        have hk_lt : k < D := by
          simpa [k, Fintype.card_fin] using this
        omega
      · exact hi
    have : P = 1 := by
      conv_lhs => rw [hP.1.1.spectral_theorem]
      have hdiag : RCLike.ofReal ∘ eig = fun _ => (1 : ℂ) :=
        funext (fun i => by simp [hall_one i])
      rw [hdiag, Matrix.diagonal_one]
      simp [Unitary.conjStarAlgAut]
    exact hP.2.2 this
  simpa [eig, k] using And.intro hk_pos hk_lt_D

/-- If `1 ≤ k < D`, then the rectangle count `k(D-k)` is at least `D-1`. -/
private theorem one_eigenvalue_card_mul_sub_ge
    {k : ℕ} (hk_pos : 1 ≤ k) (hk_lt_D : k < D) :
    D - 1 ≤ k * (D - k) := by
  have hDk : 1 ≤ D - k := Nat.sub_pos_of_lt hk_lt_D
  have hstep1 : k - 1 ≤ (k - 1) * (D - k) := Nat.le_mul_of_pos_right _ hDk
  have hstep2 : (k - 1) * (D - k) + (D - k) ≤ k * (D - k) := by
    rw [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (by omega : k ≠ 0))]
    simp [Nat.succ_mul]
  have hstep3 : (k - 1) + (D - k) = D - 1 := by
    omega
  calc
    D - 1 = (k - 1) + (D - k) := hstep3.symm
    _ ≤ (k - 1) * (D - k) + (D - k) := Nat.add_le_add_right hstep1 _
    _ ≤ k * (D - k) := hstep2

/-- The block-compression map `M ↦ (1-P)MP` has range dimension at least
`D - 1` for any nontrivial orthogonal projection `P`. -/
private theorem finrank_range_block_compression_ge
    {P : Mat} (hP : IsNontrivialProjection P) :
    let φ : Mat →ₗ[ℂ] Mat := (LinearMap.mulLeft ℂ (1 - P)).comp (LinearMap.mulRight ℂ P)
    D - 1 ≤ Module.finrank ℂ (LinearMap.range φ) := by
  classical
  set φ : Mat →ₗ[ℂ] Mat := (LinearMap.mulLeft ℂ (1 - P)).comp (LinearMap.mulRight ℂ P)
  set eig := hP.1.1.eigenvalues
  set k := (Finset.univ.filter (fun i => eig i = 1)).card
  have hk_bounds := projection_one_eigenvalue_card_bounds hP
  rcases (by simpa [eig, k] using hk_bounds) with ⟨hk_nonempty, hk_lt_D⟩
  have hk_pos : 1 ≤ k := Finset.one_le_card.mpr hk_nonempty
  have hkDk : D - 1 ≤ k * (D - k) := one_eigenvalue_card_mul_sub_ge hk_pos hk_lt_D
  have heig_01 : ∀ i : Fin D, eig i = 0 ∨ eig i = 1 := by
    simpa [eig] using projection_eigenvalues_zero_or_one (D := D) hP
  calc
    D - 1 ≤ k * (D - k) := hkDk
    _ ≤ Module.finrank ℂ (LinearMap.range φ) := by
        set U : Matrix.unitaryGroup (Fin D) ℂ := hP.1.1.eigenvectorUnitary
        have hUU : (star (U : Mat)) * (U : Mat) = 1 := by
          rw [show star (U : Mat) = ↑(star U) from (Unitary.coe_star (U := U)).symm]
          exact Unitary.coe_star_mul_self U
        have hUUs : (U : Mat) * (star (U : Mat)) = 1 := by
          rw [show star (U : Mat) = ↑(star U) from (Unitary.coe_star (U := U)).symm]
          exact Unitary.coe_mul_star_self U
        have hP_spec : P = (U : Mat) *
            Matrix.diagonal (RCLike.ofReal ∘ eig) * (star (U : Mat)) := by
          rw [hP.1.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
        have hPU : P * (U : Mat) = (U : Mat) * Matrix.diagonal (RCLike.ofReal ∘ eig) := by
          have := congrArg (· * (U : Mat)) hP_spec
          simp only [Matrix.mul_assoc, hUU, Matrix.mul_one] at this
          exact this
        have hUsP : (star (U : Mat)) * P =
            Matrix.diagonal (RCLike.ofReal ∘ eig) * (star (U : Mat)) := by
          have := congrArg ((star (U : Mat)) * ·) hP_spec
          simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul] at this
          exact this
        set D₁ : Mat := Matrix.diagonal (RCLike.ofReal ∘ eig)
        have hφ_fix : ∀ a b : Fin D, eig a = 0 → eig b = 1 →
            φ ((U : Mat) * Matrix.single a b (1 : ℂ) * star (U : Mat)) =
            (U : Mat) * Matrix.single a b (1 : ℂ) * star (U : Mat) := by
          intro a b ha hb
          set E := Matrix.single a b (1 : ℂ)
          have hDE : (1 - D₁) * E * D₁ = E := by
            have hD₁_diag : D₁ = Matrix.diagonal (fun i => (eig i : ℂ)) := by
              simp [D₁, Function.comp]
            have h1D₁ : 1 - D₁ = Matrix.diagonal (fun i => 1 - (eig i : ℂ)) := by
              rw [hD₁_diag]
              ext i j
              simp [Matrix.diagonal_apply, Matrix.one_apply]
              split_ifs <;> ring
            rw [h1D₁, hD₁_diag]
            ext i j
            simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, E, Matrix.single_apply]
            split_ifs with hij
            · obtain ⟨rfl, rfl⟩ := hij
              simp [ha, hb]
            · simp
          change (1 - P) * ((U : Mat) * E * star (U : Mat) * P) =
            (U : Mat) * E * star (U : Mat)
          have h1PU : (1 - P) * (U : Mat) = (U : Mat) * (1 - D₁) := by
            rw [Matrix.sub_mul, Matrix.one_mul, hPU, Matrix.mul_sub, Matrix.mul_one]
          calc
            (1 - P) * ((U : Mat) * E * star (U : Mat) * P)
                = ((1 - P) * ((U : Mat) * E * star (U : Mat))) * P := by
                  rw [← Matrix.mul_assoc]
            _ = ((1 - P) * (U : Mat) * E * star (U : Mat)) * P := by
                  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
            _ = ((U : Mat) * (1 - D₁) * E * star (U : Mat)) * P := by
                  rw [h1PU]
            _ = (U : Mat) * (1 - D₁) * E * (star (U : Mat) * P) := by
                  rw [Matrix.mul_assoc]
            _ = (U : Mat) * (1 - D₁) * E * (D₁ * star (U : Mat)) := by
                  rw [hUsP]
            _ = (U : Mat) * ((1 - D₁) * E * D₁) * star (U : Mat) := by
                  rw [← Matrix.mul_assoc ((U : Mat) * (1 - D₁) * E) D₁]
                  congr 1
                  rw [Matrix.mul_assoc (U : Mat) (1 - D₁) E,
                    Matrix.mul_assoc (U : Mat) ((1 - D₁) * E) D₁]
            _ = (U : Mat) * E * star (U : Mat) := by
                  rw [hDE]
        set S₀ := Finset.univ.filter (fun i : Fin D => eig i = 0)
        set S₁ := Finset.univ.filter (fun i : Fin D => eig i = 1)
        have hS₁_card : S₁.card = k := rfl
        have hS₀_card : S₀.card = D - k := by
          have hunion : S₀ ∪ S₁ = Finset.univ := by
            ext i
            simp only [S₀, S₁, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
              true_and, iff_true]
            exact heig_01 i
          have hdisj : Disjoint S₀ S₁ := by
            simp only [S₀, S₁, Finset.disjoint_filter]
            intro i _ h0 h1
            linarith
          have := Finset.card_union_of_disjoint hdisj
          rw [hunion, Finset.card_univ, Fintype.card_fin] at this
          omega
        have hcard : Fintype.card (↥S₀ × ↥S₁) = (D - k) * k := by
          rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_coe, hS₀_card, hS₁_card]
        set fam : (↥S₀ × ↥S₁) → LinearMap.range φ :=
          fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ =>
            ⟨(U : Mat) * Matrix.single a b (1 : ℂ) * star (U : Mat),
             LinearMap.mem_range.mpr ⟨_, hφ_fix a b
               (by simpa [S₀] using ha) (by simpa [S₁] using hb)⟩⟩
        have hfam_li : LinearIndependent ℂ fam := by
          apply LinearIndependent.of_comp (LinearMap.range φ).subtype
          change LinearIndependent ℂ (fun p : ↥S₀ × ↥S₁ => (fam p : Mat))
          have hfam_eq : (fun p : ↥S₀ × ↥S₁ => (fam p : Mat)) =
              (fun M : Mat => (U : Mat) * M * star (U : Mat)) ∘
                (fun p : ↥S₀ × ↥S₁ => Matrix.single p.1.1 p.2.1 (1 : ℂ)) := by
            ext ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
            rfl
          rw [hfam_eq]
          set conjMap : Mat →ₗ[ℂ] Mat :=
            (LinearMap.mulLeft ℂ (U : Mat)).comp (LinearMap.mulRight ℂ (star (U : Mat)))
          have hconj_ker : LinearMap.ker conjMap = ⊥ := by
            rw [LinearMap.ker_eq_bot]
            intro M₁ M₂ h
            simp only [conjMap, LinearMap.comp_apply, LinearMap.mulLeft_apply,
              LinearMap.mulRight_apply] at h
            have := congrArg ((star (U : Mat)) * · * (U : Mat)) h
            simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul] at this
            simpa [Matrix.mul_assoc, hUUs, Matrix.mul_one] using this
          have hfam_eq2 :
              (fun M : Mat => (U : Mat) * M * star (U : Mat)) = conjMap := by
            ext M
            simp only [conjMap, LinearMap.comp_apply, LinearMap.mulLeft_apply,
              LinearMap.mulRight_apply, Matrix.mul_assoc]
          rw [hfam_eq2]
          apply LinearIndependent.map' _ conjMap hconj_ker
          let ι : ↥S₀ × ↥S₁ → Fin D × Fin D := fun p => (p.1.1, p.2.1)
          have hι_inj : Function.Injective ι := by
            intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
            simp only [ι, Prod.mk.injEq] at h
            exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
          have hv_eq : (fun p : ↥S₀ × ↥S₁ => Matrix.single p.1.1 p.2.1 (1 : ℂ)) =
              (fun ij : Fin D × Fin D => Matrix.stdBasis ℂ (Fin D) (Fin D) ij) ∘ ι := by
            ext ⟨⟨a, _⟩, ⟨b, _⟩⟩
            simp [ι, Matrix.stdBasis_eq_single]
          rw [hv_eq]
          exact ((Matrix.stdBasis ℂ (Fin D) (Fin D)).linearIndependent).comp ι hι_inj
        calc
          k * (D - k) = (D - k) * k := Nat.mul_comm k (D - k)
          _ = Fintype.card (↥S₀ × ↥S₁) := hcard.symm
          _ ≤ Module.finrank ℂ (LinearMap.range φ) := hfam_li.fintype_card_le_finrank

/-- For a nontrivial projection `P`, the traceless block-upper-triangular
subspace `{M | (1-P)*M*P = 0 ∧ trace M = 0}` has `finrank ≤ D² - D`.
Equivalently, `finrank + D ≤ D²`. -/
private theorem finrank_traceless_blockUT_add_D_le
    {P : Mat} (hP : IsNontrivialProjection P) :
    Module.finrank ℂ
      ((LinearMap.ker ((LinearMap.mulLeft ℂ (1 - P)).comp
        (LinearMap.mulRight ℂ P))) ⊓
        (LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ)) :
        Submodule ℂ Mat) + D ≤ D ^ 2 := by
  set φ : Mat →ₗ[ℂ] Mat := (LinearMap.mulLeft ℂ (1 - P)).comp (LinearMap.mulRight ℂ P)
  set τ : Mat →ₗ[ℂ] ℂ := Matrix.traceLinearMap (Fin D) ℂ ℂ
  set K_φ := LinearMap.ker φ
  set K_τ := LinearMap.ker τ
  by_cases hD : D = 0
  · subst hD; exact absurd (Subsingleton.elim P 0) hP.2.1
  have : NeZero D := ⟨hD⟩
  have hD_ne : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hfin_mat : Module.finrank ℂ Mat = D * D := by
    simp [Module.finrank_matrix, Fintype.card_fin]
  have hφ_apply : ∀ M : Mat, φ M = (1 - P) * (M * P) := by
    intro M; rfl
  have hφ_one : φ (1 : Mat) = 0 := by
    rw [hφ_apply, Matrix.one_mul]
    exact IsIdempotentElem.one_sub_mul_self hP.1.2
  have h_sup : K_φ ⊔ K_τ = ⊤ := by
    simpa [φ, τ, K_φ, K_τ] using
      ker_sup_traceless_eq_top_of_one_mem_ker φ hφ_one hD_ne
  have hfin_Kτ : Module.finrank ℂ K_τ = D * D - 1 := by
    simpa [τ, K_τ] using finrank_traceless_submodule (D := D) hD
  have hfin_sup : Module.finrank ℂ ↥(K_φ ⊔ K_τ) = D * D := by
    rw [h_sup, finrank_top]
    exact hfin_mat
  have hdim :
      D * D + Module.finrank ℂ ↥(K_φ ⊓ K_τ) =
        Module.finrank ℂ ↥K_φ + (D * D - 1) := by
    have hdim0 := Submodule.finrank_sup_add_finrank_inf_eq K_φ K_τ
    rw [hfin_sup, hfin_Kτ] at hdim0
    exact hdim0
  have h_rn_φ :
      Module.finrank ℂ (LinearMap.range φ) + Module.finrank ℂ ↥K_φ = D * D := by
    simpa [K_φ, hfin_mat] using φ.finrank_range_add_finrank_ker
  suffices h_range_lb : Module.finrank ℂ (LinearMap.range φ) ≥ D - 1 by
    have hD_pos : 0 < D := Nat.pos_of_ne_zero hD
    set n := D * D
    have hn_pos : 1 ≤ n := by
      dsimp [n]
      exact Nat.succ_le_of_lt (Nat.mul_pos hD_pos hD_pos)
    have hdim_n :
        n + Module.finrank ℂ ↥(K_φ ⊓ K_τ) =
          Module.finrank ℂ ↥K_φ + (n - 1) := by
      simpa [n] using hdim
    have h_rn_φ_n :
        Module.finrank ℂ (LinearMap.range φ) + Module.finrank ℂ ↥K_φ = n := by
      simpa [n] using h_rn_φ
    have hfin_inf : Module.finrank ℂ ↥(K_φ ⊓ K_τ) + 1 = Module.finrank ℂ ↥K_φ := by
      omega
    have hKφ_le : Module.finrank ℂ ↥K_φ ≤ n - (D - 1) := by
      omega
    have hgoal : Module.finrank ℂ ↥(K_φ ⊓ K_τ) + D ≤ n := by
      omega
    simpa [n, Nat.pow_two] using hgoal
  simpa [φ] using finrank_range_block_compression_ge (D := D) hP

/-- Shifting Lindblad operators by scalar multiples of identity preserves
`toLinearMap` while making operators traceless.  Block-UT is preserved. -/
private theorem exists_traceless_blockUT_lindblad_form
    {P : Mat} (hP : IsNontrivialProjection P)
    (G : LindbladForm D)
    (L : Mat →ₗ[ℂ] Mat)
    (hL_eq : L = G.toLinearMap)
    (hBlock : ∀ j : Fin G.r, (1 - P) * G.L j * P = 0) :
    ∃ G' : LindbladForm D,
      G'.toLinearMap = L ∧
      (∀ j : Fin G'.r, G'.L j ∈
        ((LinearMap.ker ((LinearMap.mulLeft ℂ (1 - P)).comp
          (LinearMap.mulRight ℂ P))) ⊓
         (LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ)) :
          Submodule ℂ Mat)) := by
  by_cases hD : D = 0
  · subst D
    exact absurd (Subsingleton.elim P 0) hP.2.1
  let _ : NeZero D := ⟨hD⟩
  let V : Submodule ℂ Mat :=
    LinearMap.ker ((LinearMap.mulLeft ℂ (1 - P)).comp
      (LinearMap.mulRight ℂ P))
  have hone : (1 : Mat) ∈ V := by
    change (1 - P) * ((1 : Mat) * P) = 0
    rw [Matrix.one_mul]
    exact IsIdempotentElem.one_sub_mul_self hP.1.2
  have hmem : ∀ j : Fin G.r, G.L j ∈ V := by
    intro j
    change (1 - P) * (G.L j * P) = 0
    rw [← Matrix.mul_assoc]
    exact hBlock j
  obtain ⟨G', hmap, htrace, hV⟩ :=
    G.exists_traceless_in_submodule V hone hmem
  refine ⟨G', hmap.trans hL_eq.symm, ?_⟩
  intro j
  rw [Submodule.mem_inf]
  constructor
  · simpa [V] using hV j
  · rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply]
    exact htrace j

/-- A minimum Lindblad rank greater than `D ^ 2 - D` forbids
block-upper-triangular Lindblad decompositions.

The hypothesis is stated as `rank + D ≥ D ^ 2 + 1`, an equivalent form that
avoids truncated subtraction on natural numbers. The source-facing
Kossakowski-matrix formulation of Wolf, Corollary 7.2(3), is
`TracelessBasisKossakowskiForm.large_rank_implies_no_blockUpperTriangular`. -/
theorem large_kossakowski_rank_implies_no_blockUpperTriangular
    (F : LindbladForm D)
    (hRank : kossakowskiRank F.toLinearMap + D ≥ D ^ 2 + 1) :
    ¬ HasBlockUpperTriangularLindblad F.toLinearMap := by
  intro ⟨P, G, hP_nt, hL_eq, hBlock, _hκ_block⟩
  -- The traceless block-UT subspace
  set V : Submodule ℂ Mat :=
    (LinearMap.ker ((LinearMap.mulLeft ℂ (1 - P)).comp
      (LinearMap.mulRight ℂ P))) ⊓
    (LinearMap.ker (Matrix.traceLinearMap (Fin D) ℂ ℂ))
  -- Get a traceless block-UT form
  obtain ⟨G', hG'_eq, hG'_mem⟩ :=
    exists_traceless_blockUT_lindblad_form hP_nt G F.toLinearMap hL_eq hBlock
  -- Construct a form with rank ≤ finrank V
  obtain ⟨G'', hG''_eq, hG''_r⟩ :=
    G'.exists_equivalent_rank_le_finrank V hG'_mem
  -- kossakowskiRank ≤ G''.r
  have hkr : kossakowskiRank F.toLinearMap ≤ G''.r := by
    apply Nat.sInf_le
    exact ⟨G'', by rw [hG''_eq, hG'_eq], rfl⟩
  -- finrank V + D ≤ D²
  have hfin : Module.finrank ℂ V + D ≤ D ^ 2 :=
    finrank_traceless_blockUT_add_D_le hP_nt
  -- But kossakowskiRank + D ≥ D² + 1
  omega

/-- Wolf, Corollary 7.2(3), with the source hypothesis
`D ^ 2 - D < rank(C)`: a Kossakowski matrix of this rank cannot admit a
block-upper-triangular Lindblad representation. -/
theorem TracelessBasisKossakowskiForm.large_rank_implies_no_blockUpperTriangular
    (K : TracelessBasisKossakowskiForm D)
    (hRank : D ^ 2 - D < K.C.rank) :
    ¬ HasBlockUpperTriangularLindblad K.toLinearMap := by
  have hRank' : kossakowskiRank K.toLinearMap + D ≥ D ^ 2 + 1 := by
    rw [K.kossakowskiRank_toLinearMap_eq_rank]
    omega
  have hNoBlock := large_kossakowski_rank_implies_no_blockUpperTriangular
    K.sqrtLindbladForm (by
      rw [← K.toLinearMap_eq_sqrtLindbladForm]
      exact hRank')
  rwa [← K.toLinearMap_eq_sqrtLindbladForm] at hNoBlock

/--
If a GKSL generator has no block-upper-triangular Lindblad decomposition,
then the generated quantum dynamical semigroup is not reducible.
-/
theorem not_isReducibleQDS_of_no_blockUpperTriangular_lindblad
    {L : Mat →ₗ[ℂ] Mat}
    (hGKSL : IsGKSLGenerator L)
    (hNoBlockUT : ¬ HasBlockUpperTriangularLindblad L) :
    ¬ IsReducibleQDS L := by
  intro hReducible
  exact hNoBlockUT (wolf_prop_7_6_three_implies_four hGKSL hReducible)

/-- Wolf Corollary 7.2 condition (1): full algebra generation implies
non-reducibility. -/
theorem not_isReducible_of_generates_full_algebra
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hGen : Algebra.adjoin ℂ
      (Set.range F.L ∪ ({F.toGeneratorDecomp.κ} : Set Mat)) = ⊤) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact full_algebra_generation_implies_no_blockUpperTriangular F hGen

/-- Wolf Corollary 7.2 condition (2): Hermitian Lindblad span + trivial
commutant implies non-reducibility. -/
theorem not_isReducible_of_hermitian_span_trivial_commutant
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hHerm : IsLindbladSpanHermitianClosed F)
    (hComm : HasLindbladSpanTrivialCommutant F) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact hermitian_span_trivial_commutant_implies_no_blockUpperTriangular F hHerm hComm

/-- Wolf Corollary 7.2 condition (3): large Kossakowski rank implies
non-reducibility. -/
theorem not_isReducible_of_kossakowski_rank_ge
    (F : LindbladForm D)
    (hGKSL : IsGKSLGenerator F.toLinearMap)
    (hRank : kossakowskiRank F.toLinearMap + D ≥ D ^ 2 + 1) :
    ¬ IsReducibleQDS F.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad hGKSL
  exact large_kossakowski_rank_implies_no_blockUpperTriangular F hRank

/-- Wolf, Corollary 7.2(3), in the source notation: if
`rank(C) > D ^ 2 - D`, then the quantum dynamical semigroup is not reducible. -/
theorem TracelessBasisKossakowskiForm.not_isReducible_of_rank_gt
    (K : TracelessBasisKossakowskiForm D)
    (hRank : D ^ 2 - D < K.C.rank) :
    ¬ IsReducibleQDS K.toLinearMap := by
  apply not_isReducibleQDS_of_no_blockUpperTriangular_lindblad
  · exact (gksl_iff_tracelessBasisKossakowskiForm K.toLinearMap).2 ⟨K, rfl⟩
  · exact K.large_rank_implies_no_blockUpperTriangular hRank

end -- noncomputable section
