/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaPermutationCovariance
import QICLean.Analysis.ReplicaExcitationCompression
import QICLean.Representation.TrivialLabel

/-!
# The low-defect projection in the two original auxiliary sectors

The physical defect cutoff, the two whole-copy auxiliary label projections,
and simultaneous copy symmetry are commuting orthogonal projections. Their
product is the projection used in the lower norm comparison. Its range
retains the original auxiliary labels and simultaneous symmetry, and its
expectation on a vector in these sectors equals the expectation of the
physical cutoff alone.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 421–456, `comparator:defect-mass`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TensorPower

/-- Simultaneous permutations of the physical copies and the two original
auxiliary copy spaces. Source: `07-comparators.tex`, lines 421–456. -/
def replicaJointCopyPerm (A C R : Type*) (k : ℕ) :
    Equiv.Perm (Fin k) →* Equiv.Perm ((Fin k → A) × ((Fin k → C) × (Fin k → R))) where
  toFun σ := (copyPerm A k σ).prodCongr
    ((copyPerm C k σ).prodCongr (copyPerm R k σ))
  map_one' := by ext <;> simp
  map_mul' σ π := by ext <;> simp [Equiv.Perm.mul_apply]

/-- The simultaneous permutation operator is the literal product of the
three copy actions. Source: `07-comparators.tex`, lines 427–456. -/
theorem permOp_replicaJointCopyPerm
    (A C R : Type*) [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    permOp (replicaJointCopyPerm A C R k) σ =
      permOp (copyPerm A k) σ ⊗ₖ
        (permOp (copyPerm C k) σ ⊗ₖ permOp (copyPerm R k) σ) := by
  classical
  ext x y
  simp only [permOp_apply_apply, replicaJointCopyPerm, MonoidHom.coe_mk,
    OneHom.coe_mk, Equiv.prodCongr_apply, Prod.mk.injEq, kroneckerMap_apply]
  split_ifs <;> simp_all

end TensorPower

namespace Matrix

private theorem starProjection_tensor
    {n m : Type*} [Fintype n] [Fintype m]
    {P : Matrix n n ℂ} {Q : Matrix m m ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    IsStarProjection (P ⊗ₖ Q) := by
  refine ⟨?_, ?_⟩
  · change (P ⊗ₖ Q) * (P ⊗ₖ Q) = P ⊗ₖ Q
    rw [← mul_kronecker_mul, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  · change (P ⊗ₖ Q)ᴴ = P ⊗ₖ Q
    rw [conjTranspose_kronecker, hP.isSelfAdjoint.isHermitian.eq,
      hQ.isSelfAdjoint.isHermitian.eq]

private theorem starProjection_closedCutoff
    {n : Type*} [Fintype n] [DecidableEq n]
    {D : Matrix n n ℂ} (hD : D.IsHermitian) (b : ℝ) :
    IsStarProjection (cfc (fun x : ℝ => if x ≤ b then 1 else 0) D) := by
  refine ⟨?_, cfc_predicate _ _⟩
  change cfc (fun x : ℝ => if x ≤ b then 1 else 0) D *
    cfc (fun x : ℝ => if x ≤ b then 1 else 0) D = _
  simp only [hD.cfc_eq, ← hD.cfc_mul]
  congr 1
  funext x
  split_ifs <;> norm_num

variable {A C R : Type*} [Fintype A] [DecidableEq A]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local instance replicaLowDefectProjection_decidableEqCopies (k : ℕ) :
    DecidableEq (Fin k → A) := Fintype.decidablePiFintype

/-- The actual closed defect cutoff, restricted to the two original
auxiliary labels and simultaneous copy symmetry. No metric occurs in
this projection. Source: `07-comparators.tex`, lines 421–456. -/
def replicaLowDefectProjection (Ω : A → ℂ) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ) :
    Matrix ((Fin k → A) × ((Fin k → C) × (Fin k → R)))
      ((Fin k → A) × ((Fin k → C) × (Fin k → R))) ℂ :=
  (cfc (fun x : ℝ => if x ≤ τ * k then 1 else 0) (replicaDefectCount Ω k) ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) *
    ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) ellC ⊗ₖ labelProj (copyPerm R k) ellR)) *
    symProj (replicaJointCopyPerm A C R k)

private theorem lowDefect_factors (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ) :
    let Q := cfc (fun x : ℝ => if x ≤ τ * k then 1 else 0)
      (replicaDefectCount Ω k) ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)
    let L := (1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) ellC ⊗ₖ labelProj (copyPerm R k) ellR)
    let S := symProj (replicaJointCopyPerm A C R k)
    IsStarProjection Q ∧ IsStarProjection L ∧ IsStarProjection S ∧
      Commute Q L ∧ Commute Q S ∧ Commute L S := by
  classical
  intro Q L S
  have hQ : IsStarProjection Q := starProjection_tensor
    (starProjection_closedCutoff (posSemidef_replicaDefectCount Ω hΩ k).isHermitian _)
    (IsStarProjection.one _)
  have hC : IsStarProjection (labelProj (copyPerm C k) ellC) :=
    ⟨labelProj_mul_self _ _, (isHermitian_labelProj _ _).isSelfAdjoint⟩
  have hR : IsStarProjection (labelProj (copyPerm R k) ellR) :=
    ⟨labelProj_mul_self _ _, (isHermitian_labelProj _ _).isSelfAdjoint⟩
  have hL : IsStarProjection L :=
    starProjection_tensor (IsStarProjection.one _) (starProjection_tensor hC hR)
  have hQL : Commute Q L := by
    change Q * L = L * Q
    simp only [Q, L, ← mul_kronecker_mul, one_mul, mul_one]
  have hQperm (σ : Equiv.Perm (Fin k)) :
      Commute Q (permOp (replicaJointCopyPerm A C R k) σ) := by
    rw [permOp_replicaJointCopyPerm]
    exact commute_cfc_replicaDefectCount_kronecker Ω k _ σ _
  have hLperm (σ : Equiv.Perm (Fin k)) :
      Commute L (permOp (replicaJointCopyPerm A C R k) σ) := by
    rw [permOp_replicaJointCopyPerm]
    change L * _ = _ * L
    simp only [L, ← mul_kronecker_mul, one_mul, mul_one,
      (commute_labelProj_permOp (copyPerm C k) ellC σ).eq,
      (commute_labelProj_permOp (copyPerm R k) ellR σ).eq]
  have hQS : Commute Q S := by
    exact (Commute.sum_right _ _ _ fun σ _ => hQperm σ).smul_right _
  have hLS : Commute L S := by
    exact (Commute.sum_right _ _ _ fun σ _ => hLperm σ).smul_right _
  exact ⟨hQ, hL,
    (exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k))
      (X := (Fin k → A) × ((Fin k → C) × (Fin k → R)))).elim (fun l hl =>
        hl (replicaJointCopyPerm A C R k) ▸
          (show IsStarProjection (labelProj (replicaJointCopyPerm A C R k) l) from
            ⟨labelProj_mul_self _ l, (isHermitian_labelProj _ l).isSelfAdjoint⟩)),
    hQL, hQS, hLS⟩

/-- The actual low-defect sector is an orthogonal projection; all three
commutations follow from the literal copy actions and the central
auxiliary labels. Source: `07-comparators.tex`, lines 421–443. -/
theorem isStarProjection_replicaLowDefectProjection
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ) :
    IsStarProjection (replicaLowDefectProjection (C := C) (R := R) Ω k ellC ellR τ) := by
  obtain ⟨hQ, hL, hS, hQL, hQS, hLS⟩ :=
    lowDefect_factors (C := C) (R := R) Ω hΩ k ellC ellR τ
  exact (hQ.mul hL hQL).mul hS (hQS.mul_left hLS)

/-- On a vector with the two original labels and simultaneous symmetry,
the full low-defect projection acts exactly as its physical cutoff.
Source: `07-comparators.tex`, lines 421–443. -/
theorem replicaLowDefectProjection_mulVec_of_sector
    (Ω : A → ℂ) (k : ℕ) (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ)
    (u : (Fin k → A) × ((Fin k → C) × (Fin k → R)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm A k) σ ⊗ₖ
        (permOp (copyPerm C k) σ ⊗ₖ permOp (copyPerm R k) σ)) *ᵥ u = u)
    (huC : ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) ellC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ))) *ᵥ u = u)
    (huR : ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ labelProj (copyPerm R k) ellR)) *ᵥ u = u) :
    replicaLowDefectProjection Ω k ellC ellR τ *ᵥ u =
      (cfc (fun x : ℝ => if x ≤ τ * k then 1 else 0) (replicaDefectCount Ω k) ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) *ᵥ u := by
  have hS : symProj (replicaJointCopyPerm A C R k) *ᵥ u = u :=
    symProj_mulVec_of_mem _ fun σ => by rw [permOp_replicaJointCopyPerm]; exact hu σ
  have hL : ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) ellC ⊗ₖ labelProj (copyPerm R k) ellR)) *ᵥ u = u := by
    have h := congrArg (fun v => ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) ellC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ))) *ᵥ v) huR
    rw [mulVec_mulVec] at h
    simpa only [← mul_kronecker_mul, one_mul, mul_one, huC] using h
  rw [replicaLowDefectProjection, ← mulVec_mulVec, hS, ← mulVec_mulVec, hL]

/-- The range of the actual low-defect projection lies in the physical
cutoff and both original auxiliary label sectors, and is simultaneously
symmetric. These conditions are derived from the projection itself.
Source: `07-comparators.tex`, lines 421–456. -/
theorem replicaLowDefectProjection_fixed_conditions
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) (τ : ℝ)
    (u : (Fin k → A) × ((Fin k → C) × (Fin k → R)) → ℂ)
    (hu : replicaLowDefectProjection Ω k ellC ellR τ *ᵥ u = u) :
    (cfc (fun x : ℝ => if x ≤ τ * k then 1 else 0) (replicaDefectCount Ω k) ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) *ᵥ u = u ∧
    (((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) ellC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ))) *ᵥ u = u) ∧
    (((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ labelProj (copyPerm R k) ellR)) *ᵥ u = u) ∧
    (∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm A k) σ ⊗ₖ
        (permOp (copyPerm C k) σ ⊗ₖ permOp (copyPerm R k) σ)) *ᵥ u = u) := by
  let Q := cfc (fun x : ℝ => if x ≤ τ * k then 1 else 0) (replicaDefectCount Ω k) ⊗ₖ
    (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)
  let L := (1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
    (labelProj (copyPerm C k) ellC ⊗ₖ labelProj (copyPerm R k) ellR)
  let S := symProj (replicaJointCopyPerm A C R k)
  let P := Q * L * S
  have hu' : P *ᵥ u = u := hu
  obtain ⟨hQ, hL, hS, hQL, hQS, hLS⟩ :=
    lowDefect_factors (C := C) (R := R) Ω hΩ k ellC ellR τ
  have hQP : Q * P = P := by
    dsimp only [P]
    rw [← mul_assoc, ← mul_assoc, hQ.isIdempotentElem.eq]
  have hLP : L * P = P := by
    dsimp only [P]
    rw [← mul_assoc, ← mul_assoc, ← hQL.eq, mul_assoc Q L L,
      hL.isIdempotentElem.eq]
  have hSP : S * P = P := by
    dsimp only [P]
    rw [← mul_assoc, ← (hQS.mul_left hLS).eq, mul_assoc,
      hS.isIdempotentElem.eq]
  have hfixed (M : Matrix ((Fin k → A) × ((Fin k → C) × (Fin k → R)))
      ((Fin k → A) × ((Fin k → C) × (Fin k → R))) ℂ) (hMP : M * P = P) :
      M *ᵥ u = u := by
    calc
      M *ᵥ u = M *ᵥ (P *ᵥ u) := by rw [hu']
      _ = u := by rw [mulVec_mulVec, hMP, hu']
  have hLu : L *ᵥ u = u := hfixed L hLP
  refine ⟨hfixed Q hQP, ?_, ?_, ?_⟩
  · let LC := (1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) ellC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ))
    have hLCL : LC * L = L := by
      simp only [LC, L, ← mul_kronecker_mul, one_mul, labelProj_mul_self]
    change LC *ᵥ u = u
    calc
      LC *ᵥ u = LC *ᵥ (L *ᵥ u) := by rw [hLu]
      _ = u := by rw [mulVec_mulVec, hLCL, hLu]
  · let LR := (1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ labelProj (copyPerm R k) ellR)
    have hLRL : LR * L = L := by
      simp only [LR, L, ← mul_kronecker_mul, one_mul, labelProj_mul_self]
    change LR *ᵥ u = u
    calc
      LR *ᵥ u = LR *ᵥ (L *ᵥ u) := by rw [hLu]
      _ = u := by rw [mulVec_mulVec, hLRL, hLu]
  · intro σ
    rw [← permOp_replicaJointCopyPerm]
    have hs := symProj_mulVec_mem (replicaJointCopyPerm A C R k) u σ
    simpa only [hfixed S hSP] using hs

/-- The original physical gap gives the required retained mass for the
actual symmetric, fixed-label low-defect projection.
Source: `07-comparators.tex`, lines 421–443, `comparator:defect-mass`. -/
theorem replicaLowDefectProjection_gap_mass_ge
    {H : Matrix A A ℂ} {Ω : A → ℂ} {E₀ g : ℝ}
    (hgap : (H - (E₀ : ℂ) • 1 -
      (g : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (hg : 0 < g) {k : ℕ} (hk : 0 < k)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) {τ : ℝ} (hτ : 0 < τ)
    (v : EuclideanSpace ℂ ((Fin k → A) × ((Fin k → C) × (Fin k → R)))) (hv : ‖v‖ = 1)
    (hsym : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm A k) σ ⊗ₖ
        (permOp (copyPerm C k) σ ⊗ₖ permOp (copyPerm R k) σ)) *ᵥ v = v)
    (hC : ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (labelProj (copyPerm C k) ellC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ))) *ᵥ v = v)
    (hR : ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ labelProj (copyPerm R k) ellR)) *ᵥ v = v) :
    1 - ((star v ⬝ᵥ (((((k : ℝ)⁻¹) • replicaHamiltonian H k) ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) *ᵥ v)).re - E₀) / g / τ ≤
      (star v ⬝ᵥ (replicaLowDefectProjection Ω k ellC ellR τ *ᵥ v)).re := by
  rw [replicaLowDefectProjection_mulVec_of_sector Ω k ellC ellR τ v hsym hC hR]
  exact spectralCutoff_replica_gap_mass_ge hgap hΩ hg hk hτ v hv

/-- Uniform bounds on the actual excitation components of original
symmetric, fixed-label vectors imply the compressed operator bound on
the actual low-defect projection. All projection, cutoff and sector
conditions are derived. The component estimate remains an explicit
input of this auxiliary implication.
Source: `07-comparators.tex`, lines 577–590, `comparator:inverse-compression`. -/
theorem replicaLowDefectProjection_compression_le_of_component_bounds
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
    {τ c : ℝ} (hτ : 0 ≤ τ) (hτhalf : τ ≤ 1 / 2) (hc : 0 ≤ c)
    {H : Matrix ((Fin k → A) × ((Fin k → C) × (Fin k → R)))
      ((Fin k → A) × ((Fin k → C) × (Fin k → R))) ℂ}
    (hH : H.PosSemidef)
    (hcomponent : ∀ u : (Fin k → A) × ((Fin k → C) × (Fin k → R)) → ℂ,
      (∀ σ : Equiv.Perm (Fin k),
        (permOp (copyPerm A k) σ ⊗ₖ
          (permOp (copyPerm C k) σ ⊗ₖ permOp (copyPerm R k) σ)) *ᵥ u = u) →
      (((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
        (labelProj (copyPerm C k) ellC ⊗ₖ
          (1 : Matrix (Fin k → R) (Fin k → R) ℂ))) *ᵥ u = u) →
      (((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ
          labelProj (copyPerm R k) ellR)) *ᵥ u = u) →
      ∀ B : Finset (Fin k), (B.card : ℝ) ≤ τ * k →
        let w := (replicaExcitationProjection Ω k B ⊗ₖ
          (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) *ᵥ u
        (star w ⬝ᵥ (H *ᵥ w)).re ≤ c * ‖WithLp.toLp 2 w‖ ^ 2) :
    let P := replicaLowDefectProjection Ω k ellC ellR τ
    P * H * P ≤ (((k : ℝ) + 1) * Real.exp (k * Real.binEntropy τ) * c) • P := by
  intro P
  have hP : IsStarProjection P :=
    isStarProjection_replicaLowDefectProjection Ω hΩ k ellC ellR τ
  have hcut : (cfc (fun x : ℝ => if x ≤ τ * k then 1 else 0)
      (replicaDefectCount Ω k) ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) * P = P := by
    apply Matrix.ext_iff_mulVec.mpr
    intro u
    rw [← mulVec_mulVec]
    exact (replicaLowDefectProjection_fixed_conditions Ω hΩ k ellC ellR τ (P *ᵥ u)
      (by rw [mulVec_mulVec, hP.isIdempotentElem.eq])).1
  apply compression_le_of_replicaExcitationComponent_bounds Ω hΩ k
    hτ hτhalf hc hH hP hcut
  intro u hu B hB
  obtain ⟨_, huC, huR, hsym⟩ :=
    replicaLowDefectProjection_fixed_conditions Ω hΩ k ellC ellR τ u hu
  exact hcomponent u hsym huC huR B hB

end Matrix
