/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.KroneckerFactorPositivity
import QICLean.Algebra.HermitianHelpers
import QICLean.Algebra.MatrixAux
import QICLean.Analysis.GlobalGap
import QICLean.Analysis.SpectralCutoffMass
import QICLean.Analysis.CfcKronecker

/-!
# Physical excitation counts on finitely many replicas

The Hamiltonian sum and excitation count act on the actual physical replica
space. Each summand acts on one copy and is the identity on every other copy.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 421–456, `comparator:defect-mass`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Copy-permutation compatibility, ground-factor decomposition and metric estimates
are separate steps of the source argument.

Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:defect-mass.
Label: comparator:prevector.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder

noncomputable section

namespace Matrix

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The sum of the Hamiltonian acting on each physical copy.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 421–438. -/
def replicaHamiltonian (H : Matrix A A ℂ) (k : ℕ) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  ∑ i : Fin k, finKronecker (fun j : Fin k ↦ if j = i then H else 1)

/-- The sum of the actual one-copy ground-complement projections.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 421–438. -/
def replicaDefectCount (Ω : A → ℂ) (k : ℕ) :
    Matrix (Fin k → A) (Fin k → A) ℂ :=
  ∑ i : Fin k, finKronecker (fun j : Fin k ↦
    if j = i then 1 - vecMulVec Ω (star Ω) else 1)

private theorem singleReplica_entry {k : ℕ} (i : Fin k) (K : Matrix A A ℂ)
    (x y : Fin k → A) :
    finKronecker (fun j : Fin k ↦ if j = i then K else 1) x y =
      K (x i) (y i) * ∏ j ∈ Finset.univ.erase i, (1 : Matrix A A ℂ) (x j) (y j) := by
  rw [finKronecker_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [ite_true]
  congr 1
  apply Finset.prod_congr rfl
  exact fun j hj ↦ congrArg (fun M : Matrix A A ℂ ↦ M (x j) (y j))
    (ite_eq_right (Finset.mem_erase.mp hj).1)

private def singleReplicaLinearMap {k : ℕ} (i : Fin k) :
    Matrix A A ℂ →ₗ[ℂ] Matrix (Fin k → A) (Fin k → A) ℂ where
  toFun K := finKronecker (fun j : Fin k ↦ if j = i then K else 1)
  map_add' K L := by
    ext x y
    simp only [add_apply, singleReplica_entry, add_mul]
  map_smul' c K := by
    ext x y
    simp only [singleReplica_entry, smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

private theorem singleReplicaLinearMap_one {k : ℕ} (i : Fin k) :
    singleReplicaLinearMap (A := A) i 1 = 1 := by
  ext x y
  simp only [singleReplicaLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    ite_self, finKronecker_apply, one_apply, Fintype.prod_boole, ← funext_iff]

private theorem singleReplicaLinearMap_posSemidef {k : ℕ} (i : Fin k)
    {K : Matrix A A ℂ} (hK : K.PosSemidef) :
    (singleReplicaLinearMap i K).PosSemidef := by
  exact finKronecker_posSemidef _ (fun j ↦
    if h : j = i then (ite_eq_left h).symm ▸ hK
    else (ite_eq_right h).symm ▸ PosSemidef.one)

/-- A literal product of one-copy eigenvectors is an eigenvector of the actual
replica Hamiltonian sum. OpenAI area-law manuscript, lines 130–147. -/
theorem replicaHamiltonian_mulVec_prod {H : Matrix A A ℂ} {Ω : A → ℂ} {E₀ : ℂ}
    (hΩ : H *ᵥ Ω = E₀ • Ω) (k : ℕ) :
    replicaHamiltonian H k *ᵥ (fun x : Fin k → A ↦ ∏ i, Ω (x i)) =
      ((k : ℂ) * E₀) • (fun x : Fin k → A ↦ ∏ i, Ω (x i)) := by
  have hterm (i : Fin k) : finKronecker (fun j : Fin k ↦ if j = i then H else 1) *ᵥ
      (fun x : Fin k → A ↦ ∏ j, Ω (x j)) =
      E₀ • (fun x : Fin k → A ↦ ∏ j, Ω (x j)) := by
    ext x
    change ((fun x y ↦ ∏ j, (if j = i then H else 1) (x j) (y j)) *ᵥ
      (fun x : Fin k → A ↦ ∏ j, Ω (x j))) x = _
    rw [piProduct_mulVec_pureTensor]
    simp only [apply_ite (fun M : Matrix A A ℂ ↦ M *ᵥ Ω), hΩ, one_mulVec,
      ite_apply, Pi.smul_apply, smul_eq_mul]
    have hfactor (j : Fin k) : (if j = i then E₀ * Ω (x j) else Ω (x j)) =
        (if j = i then E₀ else 1) * Ω (x j) := by
      split <;> simp_all
    simp only [hfactor, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  simp only [replicaHamiltonian, sum_mulVec, hterm, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

/-- The physical mean Hamiltonian has the one-copy ground energy on the literal
product ground vector tensored with any auxiliary vector.
OpenAI area-law manuscript, lines 130–147. -/
theorem replicaMeanHamiltonian_kronecker_mulVec_prod {C : Type*} [Fintype C]
    [DecidableEq C] {H : Matrix A A ℂ} {Ω : A → ℂ} {E₀ : ℝ}
    (hΩ : H *ᵥ Ω = (E₀ : ℂ) • Ω) {k : ℕ} (hk : 0 < k) (w : C → ℂ) :
    (((k : ℝ)⁻¹ • replicaHamiltonian H k) ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ
      (fun x : (Fin k → A) × C ↦ (∏ i, Ω (x.1 i)) * w x.2) =
      (E₀ : ℂ) • (fun x : (Fin k → A) × C ↦ (∏ i, Ω (x.1 i)) * w x.2) := by
  have hprod (x : (Fin k → A) × C) :
      ((replicaHamiltonian H k ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ
        (fun y : (Fin k → A) × C ↦ (∏ i, Ω (y.1 i)) * w y.2)) x =
        (replicaHamiltonian H k *ᵥ (fun y : Fin k → A ↦ ∏ i, Ω (y i))) x.1 * w x.2 := by
    simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
      one_apply, mul_ite, mul_zero, mul_one, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_mul, mul_assoc]
  ext x
  simp only [smul_kronecker, smul_mulVec, Pi.smul_apply, hprod,
    replicaHamiltonian_mulVec_prod hΩ k, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_inv, Complex.ofReal_natCast]
  simp only [← mul_assoc, inv_mul_cancel₀ (show (k : ℂ) ≠ 0 from
    Nat.cast_ne_zero.mpr hk.ne'), one_mul]

/-- The full one-copy gap bounds the actual sum of excitation projections on replicas.
Neither normalization nor a ground-eigenvector equation is needed for this operator inequality.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 421–438. -/
theorem PosSemidef.replica_gap {H : Matrix A A ℂ} {Ω : A → ℂ} {E₀ g : ℝ}
    (hgap : (H - (E₀ : ℂ) • 1 -
      (g : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef) (k : ℕ) :
    (replicaHamiltonian H k - ((k * E₀ : ℝ) : ℂ) • 1 -
      (g : ℂ) • replicaDefectCount Ω k).PosSemidef := by
  have hsum := posSemidef_sum (Finset.univ : Finset (Fin k))
    (fun i _ ↦ singleReplicaLinearMap_posSemidef i hgap)
  simp only [map_sub, map_smul, singleReplicaLinearMap_one, Finset.sum_sub_distrib,
    ← Finset.smul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsum
  have hcount : replicaDefectCount Ω k = k • (1 : Matrix (Fin k → A) (Fin k → A) ℂ) -
      ∑ i : Fin k, singleReplicaLinearMap i (vecMulVec Ω (star Ω)) := by
    change (∑ i : Fin k, singleReplicaLinearMap i (1 - vecMulVec Ω (star Ω))) = _
    simp only [map_sub, singleReplicaLinearMap_one, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← hcount] at hsum
  simpa only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Complex.ofReal_mul,
    Complex.ofReal_natCast, mul_comm, replicaHamiltonian, singleReplicaLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk] using hsum

/-- The actual excitation count of a normalized ground vector is positive semidefinite.
OpenAI area-law manuscript, `comparator:defect-mass`, lines 421–438. -/
theorem posSemidef_replicaDefectCount (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) : (replicaDefectCount Ω k).PosSemidef := by
  have hnorm : ∑ a, ‖Ω a‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq (𝕜 := ℂ), hΩ]
    norm_num
  simpa only [singleReplicaLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    replicaDefectCount] using posSemidef_sum (Finset.univ : Finset (Fin k))
      (fun i _ ↦ singleReplicaLinearMap_posSemidef i
        (one_sub_vecMulVec_posSemidef_of_sum_normSq_le_one Ω hnorm.le))

/-- The actual replica cutoff retains mass bounded below by the mean excess energy.
The auxiliary factors are arbitrary and the original one-copy full gap is the sole
energy assumption. OpenAI area-law manuscript, `comparator:defect-mass`, lines 421–438. -/
theorem spectralCutoff_replica_gap_mass_ge {C : Type*} [Fintype C] [DecidableEq C]
    {H : Matrix A A ℂ} {Ω : A → ℂ} {E₀ g : ℝ}
    (hgap : (H - (E₀ : ℂ) • 1 -
      (g : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (hg : 0 < g) {k : ℕ} (hk : 0 < k)
    {τ : ℝ} (hτ : 0 < τ) (v : EuclideanSpace ℂ ((Fin k → A) × C)) (hv : ‖v‖ = 1) :
    1 - ((star v ⬝ᵥ (((((k : ℝ)⁻¹) • replicaHamiltonian H k) ⊗ₖ
      (1 : Matrix C C ℂ)) *ᵥ v)).re - E₀) / g / τ ≤
      (star v ⬝ᵥ ((cfc (fun r : ℝ ↦ if r ≤ τ * k then 1 else 0)
        (replicaDefectCount Ω k) ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ v)).re := by
  have hN := posSemidef_replicaDefectCount Ω hΩ k
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hcut := PosSemidef.spectralCutoff_mass_ge
    (hN.kronecker (PosSemidef.one : (1 : Matrix C C ℂ).PosSemidef))
    (mul_pos hτ hkR) v hv
  rw [cfc_kronecker_one hN.isHermitian] at hcut
  have hreal := (Complex.nonneg_iff.mp
    (((hgap.replica_gap k).kronecker
      (PosSemidef.one : (1 : Matrix C C ℂ).PosSemidef)).dotProduct_mulVec_nonneg v)).1
  change 0 ≤ (star v ⬝ᵥ (leftKroneckerEmbed (n := C)
    (replicaHamiltonian H k - ((k * E₀ : ℝ) : ℂ) • 1 -
      (g : ℂ) • replicaDefectCount Ω k) *ᵥ v)).re at hreal
  simp only [map_sub, map_smul, map_one, leftKroneckerEmbed_apply,
    smul_kronecker, sub_mulVec, smul_mulVec,
    dotProduct_sub, dotProduct_smul, one_mulVec, Complex.sub_re, Complex.real_smul,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hreal ⊢
  have hn : (star v ⬝ᵥ v).re = 1 := by
    simpa only [RCLike.re_to_complex, PiLp.coe_symm_continuousLinearEquiv,
      WithLp.toLp_ofLp, hv, one_pow] using re_star_dotProduct_self_eq_norm_sq v
  rw [hn, mul_one] at hreal
  have hbound : (star v ⬝ᵥ ((replicaDefectCount Ω k ⊗ₖ
      (1 : Matrix C C ℂ)) *ᵥ v)).re ≤
      ((star v ⬝ᵥ ((replicaHamiltonian H k ⊗ₖ
        (1 : Matrix C C ℂ)) *ᵥ v)).re - k * E₀) / g := by
    apply (le_div_iff₀ hg).mpr
    linarith only [hreal]
  have hscaled := div_le_div_of_nonneg_right hbound (mul_pos hτ hkR).le
  have harith : (((k : ℝ)⁻¹ * (star v ⬝ᵥ ((replicaHamiltonian H k ⊗ₖ
      (1 : Matrix C C ℂ)) *ᵥ v)).re - E₀) / g) / τ =
      (((star v ⬝ᵥ ((replicaHamiltonian H k ⊗ₖ
        (1 : Matrix C C ℂ)) *ᵥ v)).re - k * E₀) / g) / (τ * k) := by
    field_simp
  rw [harith]
  linarith only [hscaled, hcut]

end Matrix
