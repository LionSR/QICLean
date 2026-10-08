/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaMarkedRatioInverse
import QICLean.Representation.ReplicaSiteOp
import QICLean.Entropy.RegionUnion
import QICLean.Analysis.PosSemidefCommute

/-!
# Similarity transforms of copy means by the partition metric

Let `V = ⨂_v ℂ^{n_v}` with every `n_v ≥ 1`, let `P, Y, F` be disjoint subsystems and let
`0 < t < 1/2`. The area-law paper (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, equation `replicas:leaf-metric`, lines 459–473, and Lemma 6.4,
lines 615–631) defines the partition metric `A_k = (W_{P,k}^{-1} W_{F,k}^{-1} W_{Y,k})²` and,
for a one-copy operator `h` supported on `P ∪ Y`, the similarity transform of its copy mean

`O_k = A_k^{-1/2} hbar A_k^{1/2}`, `hbar = k^{-1} ∑_j h^{(j)}`,

on the symmetric subspace `𝒮_k`. This file proves the first assertion of Lemma 6.4:
`sup_k ‖O_k‖ < ∞` on `𝒮_k`. The proof follows lines 666–692: between symmetric vectors
`h^{(k)}` may replace `hbar`, the `F` factors cancel, the remaining form is the compression of
`R_{P,k} R_{Y,k}^{-1} h^{(k)} R_{P,k}^{-1} R_{Y,k}`, and after writing `h` as a sum of products
`e_Y c_P` both inverses act directly on symmetric vectors, where Lemma 6.2 bounds them.

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.leafRoot`, `TensorPower.leafMetric`, `TensorPower.copyMean`,
  `TensorPower.markedSimilarity`.
* `TensorPower.sqrt_leafMetric` — `A_k^{1/2} = W_{P,k}^{-1} W_{F,k}^{-1} W_{Y,k}`.
* `TensorPower.exists_norm_markedSimilarity_mulVec_le` — `‖O_k z‖ ≤ C ‖z‖` on `𝒮_k`.
-/

open Matrix PermutationRepresentation Entropy
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- **Product decomposition across disjoint regions.** An operator supported on `X ∪ T`, with
`X, T` disjoint, is a finite sum of products `a_i b_i` with `a_i` supported on `X` and `b_i`
supported on `T` (`05-replicas.tex`, lines 678–681). -/
theorem IsSupportedOn.exists_sum_mul {M : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    {X T : Finset V} (hXT : Disjoint X T) (hM : IsSupportedOn M (X ∪ T)) (σ₀ : SiteConfig n) :
    ∃ (N : ℕ) (a b : Fin N → Matrix (SiteConfig n) (SiteConfig n) ℂ),
      (∀ i, IsSupportedOn (a i) X) ∧ (∀ i, IsSupportedOn (b i) T) ∧
        M = ∑ i, a i * b i := by
  classical
  obtain ⟨K, rfl⟩ := hM.exists_localLift σ₀
  set e := regionUnionEquiv (n := n) hXT
  set K' := reindex e e K
  set I := (RegionConfig n X × RegionConfig n T) × (RegionConfig n X × RegionConfig n T)
  set g := Fintype.equivFin I
  set A : I → Matrix (SiteConfig n) (SiteConfig n) ℂ := fun p =>
    K' p.1 p.2 • localLift X (single p.1.1 p.2.1 1)
  set B : I → Matrix (SiteConfig n) (SiteConfig n) ℂ := fun p =>
    localLift T (single p.1.2 p.2.2 1)
  refine ⟨Fintype.card I, fun i => A (g.symm i), fun i => B (g.symm i), fun i => ?_,
    fun i => isSupportedOn_localLift _, ?_⟩
  · simp only [A, ← localLift_smul]
    exact isSupportedOn_localLift _
  · have hK : K = reindex e.symm e.symm K' := by simp [K']
    -- The lift of a reindexed matrix is linear in that matrix.
    let Ψ : Matrix (RegionConfig n X × RegionConfig n T) (RegionConfig n X × RegionConfig n T) ℂ
        →ₗ[ℂ] Matrix (SiteConfig n) (SiteConfig n) ℂ :=
      { toFun := fun L => localLift (X ∪ T) (reindex e.symm e.symm L)
        map_add' := fun L L' => by
          rw [← localLift_add]
          congr 1
        map_smul' := fun c L => by
          rw [RingHom.id_apply, ← localLift_smul]
          congr 1 }
    have hΨ : ∀ L, Ψ L = localLift (X ∪ T) (reindex e.symm e.symm L) := fun _ => rfl
    rw [Equiv.sum_comp g.symm (fun p => A p * B p), hK, ← hΨ, matrix_eq_sum_single K',
      map_sum]
    conv_rhs => rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : single i j (K' i j) = K' i j • (single i.1 j.1 (1 : ℂ) ⊗ₖ single i.2 j.2 1) := by
      rw [single_kronecker_single, one_mul, smul_single, smul_eq_mul, mul_one]
    rw [h1, map_smul, hΨ, localLift_union_kronecker hXT]
    simp only [A, B, smul_mul_assoc]

end Entropy

namespace PermutationRepresentation

variable {G H X : Type*} [Group G] [Fintype G] [Group H] [Fintype H] [Fintype X]
  [DecidableEq X]

/-- Label observables of pointwise-commuting actions commute. -/
theorem commute_labelObservable_of_commute (φ : G →* Equiv.Perm X) (ψ : H →* Equiv.Perm X)
    (h : ∀ g g', Commute (φ g) (ψ g')) (f : IrrepLabel G → ℝ) (f' : IrrepLabel H → ℝ) :
    Commute (labelObservable φ f) (labelObservable ψ f') := by
  rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep]
  exact commute_groupAlgebraRep_of_commute φ ψ h _ _

theorem labelObservable_mul_inv {φ : G →* Equiv.Perm X} {f : IrrepLabel G → ℝ}
    (hf : ∀ l, f l ≠ 0) : labelObservable φ f * labelObservable φ (fun l => (f l)⁻¹) = 1 := by
  rw [labelObservable_eq_hom, labelObservable_eq_hom, ← map_mul,
    ← map_one (isOrthogonalResolution_labelProj φ).hom]
  congr 1
  ext l
  simp [hf l]

theorem labelObservable_inv_mul' {φ : G →* Equiv.Perm X} {f : IrrepLabel G → ℝ}
    (hf : ∀ l, f l ≠ 0) : labelObservable φ (fun l => (f l)⁻¹) * labelObservable φ f = 1 := by
  rw [labelObservable_eq_hom, labelObservable_eq_hom, ← map_mul,
    ← map_one (isOrthogonalResolution_labelProj φ).hom]
  congr 1
  ext l
  simp [hf l]

/-- The inverse of a label observable with nonzero values is the label observable of the
reciprocal. -/
theorem labelObservable_inv (φ : G →* Equiv.Perm X) {f : IrrepLabel G → ℝ}
    (hf : ∀ l, f l ≠ 0) : (labelObservable φ f)⁻¹ = labelObservable φ fun l => (f l)⁻¹ :=
  Matrix.inv_eq_left_inv (labelObservable_inv_mul' hf)

theorem labelObservable_mul_inv_self (φ : G →* Equiv.Perm X) {f : IrrepLabel G → ℝ}
    (hf : ∀ l, f l ≠ 0) : labelObservable φ f * (labelObservable φ f)⁻¹ = 1 := by
  rw [labelObservable_inv φ hf]; exact labelObservable_mul_inv hf

theorem labelObservable_inv_mul_self (φ : G →* Equiv.Perm X) {f : IrrepLabel G → ℝ}
    (hf : ∀ l, f l ≠ 0) : (labelObservable φ f)⁻¹ * labelObservable φ f = 1 := by
  rw [labelObservable_inv φ hf]; exact labelObservable_inv_mul' hf

end PermutationRepresentation

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ)

/-- `A_k^{1/2} = W_{P,k}^{-1} W_{F,k}^{-1} W_{Y,k}` (`05-replicas.tex`, line 462). -/
noncomputable def leafRoot (t : ℝ) (k : ℕ) (P Y F : Finset V) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  (replicaMetric (fun v => Fin (n v)) t k P)⁻¹ * (replicaMetric (fun v => Fin (n v)) t k F)⁻¹ *
    replicaMetric (fun v => Fin (n v)) t k Y

/-- The partition metric `A_k(P, Y, F) = (W_{P,k}^{-1} W_{F,k}^{-1} W_{Y,k})²`
(`05-replicas.tex`, equation `replicas:leaf-metric`). -/
noncomputable def leafMetric (t : ℝ) (k : ℕ) (P Y F : Finset V) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  leafRoot n t k P Y F ^ 2

/-- The copy mean `hbar = k^{-1} ∑_j h^{(j)}` of a one-copy operator (`05-replicas.tex`,
line 470). -/
noncomputable def copyMean (k : ℕ) (h : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  ((k : ℂ))⁻¹ • ∑ j, siteOp j h

/-- The similarity transform `O_k = A_k^{-1/2} hbar A_k^{1/2}` (`05-replicas.tex`, Lemma 6.4,
line 621). -/
noncomputable def markedSimilarity (t : ℝ) (k : ℕ) (P Y F : Finset V)
    (h : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  (CFC.sqrt (leafMetric n t k P Y F))⁻¹ * copyMean n k h * CFC.sqrt (leafMetric n t k P Y F)

variable {n} [∀ v, NeZero (n v)]

theorem replicaMetric_inv_eq {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (Q : Finset V) :
    (replicaMetric (fun v => Fin (n v)) t k Q)⁻¹ =
      labelObservable (subsystemPerm k (fun v => Fin (n v)) Q)
        fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ :=
  labelObservable_inv _ fun l => (replicaLabelWeight_pos _ ht l).ne'

omit [∀ v, NeZero (n v)] in
theorem commute_replicaMetric_of_disjoint' (k : ℕ) {Q Q' : Finset V}
    (h : Disjoint Q Q') (f f' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f)
      (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q') f') :=
  commute_labelObservable_of_commute _ _ (commute_subsystemPerm_of_disjoint k _ h) f f'

theorem posDef_leafRoot {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V} (hPY : Disjoint P Y)
    (hPF : Disjoint P F) (hYF : Disjoint Y F) : (leafRoot n t k P Y F).PosDef := by
  have hP := posDef_replicaMetric (fun v => Fin (n v)) ht k P
  have hF := posDef_replicaMetric (fun v => Fin (n v)) ht k F
  have hY := posDef_replicaMetric (fun v => Fin (n v)) ht k Y
  have hPF' : Commute (replicaMetric (fun v => Fin (n v)) t k P)⁻¹
      (replicaMetric (fun v => Fin (n v)) t k F)⁻¹ := by
    rw [replicaMetric_inv_eq ht, replicaMetric_inv_eq ht]
    exact commute_replicaMetric_of_disjoint' k hPF _ _
  have hPFY : Commute ((replicaMetric (fun v => Fin (n v)) t k P)⁻¹ *
      (replicaMetric (fun v => Fin (n v)) t k F)⁻¹) (replicaMetric (fun v => Fin (n v)) t k Y) := by
    rw [replicaMetric_inv_eq ht, replicaMetric_inv_eq ht]
    exact (commute_replicaMetric_of_disjoint' k hPY _ _).mul_left
      (commute_replicaMetric_of_disjoint' k hYF.symm _ _)
  have h1 := (hP.inv.posSemidef.mul_of_commute hF.inv.posSemidef hPF'.eq)
  have h2 := h1.mul_of_commute hY.posSemidef hPFY.eq
  have hdet : IsUnit (leafRoot n t k P Y F) := by
    rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    simp only [leafRoot, det_mul]
    exact mul_ne_zero (mul_ne_zero hP.inv.det_pos.ne' hF.inv.det_pos.ne') hY.det_pos.ne'
  exact (h2.posDef_iff_isUnit).mpr hdet

/-- `A_k^{1/2} = W_{P,k}^{-1} W_{F,k}^{-1} W_{Y,k}`. -/
theorem sqrt_leafMetric {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V} (hPY : Disjoint P Y)
    (hPF : Disjoint P F) (hYF : Disjoint Y F) :
    CFC.sqrt (leafMetric n t k P Y F) = leafRoot n t k P Y F :=
  CFC.sqrt_sq _ (nonneg_iff_posSemidef.mpr (posDef_leafRoot ht k hPY hPF hYF).posSemidef)

omit [∀ v, NeZero (n v)] in
/-- Label observables of a subsystem commute with the permutations of entire copies. -/
theorem commute_copyPerm_labelObservable (k : ℕ) (Q : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (τ : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (SiteConfig n) k) τ)
      (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f) := by
  rw [permOp_of_eq_mul (subsystemPerm k (fun v => Fin (n v)) Q)
    (subsystemPerm k (fun v => Fin (n v)) Qᶜ) _ (fun g => copyPerm_eq_mul_compl Q g) τ]
  refine Commute.mul_left ?_ ?_
  · rw [labelObservable_eq_groupAlgebraRep]
    exact (commute_groupAlgebraRep_permOp_of_mem_center _
      (sum_smul_centralIdem_mem_center f) τ).symm
  · exact (commute_labelObservable_of_forall_commute _ (fun g =>
      commute_permOp_subsystemPerm_of_disjoint (fun v => Fin (n v)) disjoint_compl_right g τ)
        f).symm

omit [∀ v, NeZero (n v)] in
/-- The copy mean commutes with the permutations of entire copies. -/
theorem commute_copyPerm_copyMean (k : ℕ) (h : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    (τ : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (SiteConfig n) k) τ) (copyMean n k h) := by
  unfold copyMean
  refine Commute.smul_right ?_ _
  rw [Commute, SemiconjBy, Finset.mul_sum, Finset.sum_mul]
  simp_rw [permOp_copyPerm_mul_siteOp h _ τ]
  exact Fintype.sum_equiv τ _ _ fun j => rfl

omit [∀ v, NeZero (n v)] in
/-- **Symmetric replacement** (`05-replicas.tex`, line 668): between symmetric vectors, and
between operators commuting with the permutations of entire copies, `h^{(j)}` may replace
`h^{(j')}`. -/
theorem star_dotProduct_siteOp_eq {k : ℕ} (j j' : Fin k)
    (h : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    {M N : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ}
    (hM : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) k) τ) M)
    (hN : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) k) τ) N)
    {w z : Config k (fun v => Fin (n v)) → ℂ}
    (hw : w ∈ symmetricSubspace k (fun v => Fin (n v)))
    (hz : z ∈ symmetricSubspace k (fun v => Fin (n v))) :
    star w ⬝ᵥ ((M * siteOp j h * N) *ᵥ z) = star w ⬝ᵥ ((M * siteOp j' h * N) *ᵥ z) := by
  set τ := Equiv.swap j j'
  set U := permOp (copyPerm (SiteConfig n) k) τ
  set U' := permOp (copyPerm (SiteConfig n) k) τ⁻¹
  have hs : siteOp j' h = U * siteOp j h * U' := by
    have := permOp_copyPerm_mul_siteOp h j τ
    rw [Equiv.swap_apply_left] at this
    rw [this, mul_assoc, permOp_mul_inv_self, mul_one]
  have hz' : U' *ᵥ z = z := hz τ⁻¹
  have hw' : Uᴴ *ᵥ w = w := by rw [conjTranspose_permOp]; exact hw τ⁻¹
  have hconj : M * (U * siteOp j h * U') * N = U * (M * siteOp j h * N) * U' := by
    have h1 : M * U = U * M := ((hM τ).eq).symm
    have h2 : U' * N = N * U' := (hN τ⁻¹).eq
    calc M * (U * siteOp j h * U') * N = (M * U) * siteOp j h * (U' * N) := by
          simp only [mul_assoc]
      _ = (U * M) * siteOp j h * (N * U') := by rw [h1, h2]
      _ = U * (M * siteOp j h * N) * U' := by simp only [mul_assoc]
  have e : (U * (M * siteOp j h * N) * U') *ᵥ z = U *ᵥ ((M * siteOp j h * N) *ᵥ z) := by
    simp only [← mulVec_mulVec, hz']
  have hU : ∀ v, star w ⬝ᵥ (U *ᵥ v) = star w ⬝ᵥ v := fun v => by
    rw [dotProduct_mulVec, ← conjTranspose_conjTranspose U, ← star_mulVec, hw']
  rw [hs, hconj, e, hU]

omit [∀ v, NeZero (n v)] in
/-- Between symmetric vectors the copy mean may be replaced by any single copy. -/
theorem star_dotProduct_copyMean_eq {m : ℕ} (j : Fin (m + 1))
    (h : Matrix (SiteConfig n) (SiteConfig n) ℂ)
    {M N : Matrix (Config (m + 1) fun v => Fin (n v)) (Config (m + 1) fun v => Fin (n v)) ℂ}
    (hM : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ) M)
    (hN : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ) N)
    {w z : Config (m + 1) (fun v => Fin (n v)) → ℂ}
    (hw : w ∈ symmetricSubspace (m + 1) (fun v => Fin (n v)))
    (hz : z ∈ symmetricSubspace (m + 1) (fun v => Fin (n v))) :
    star w ⬝ᵥ ((M * copyMean n (m + 1) h * N) *ᵥ z) =
      star w ⬝ᵥ ((M * siteOp j h * N) *ᵥ z) := by
  have hterm : ∀ j', star w ⬝ᵥ ((M * siteOp j' h * N) *ᵥ z) =
      star w ⬝ᵥ ((M * siteOp j h * N) *ᵥ z) := fun j' =>
    star_dotProduct_siteOp_eq j' j h hM hN hw hz
  unfold copyMean
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, smul_mulVec, sum_mulVec,
    dotProduct_smul, dotProduct_sum, Finset.sum_congr rfl fun j' _ => hterm j',
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-! ### Uniform boundedness -/

omit [∀ v, NeZero (n v)] in
/-- Bound for a matrix applied to a vector, in Euclidean norms. -/
theorem norm_mulVec_le {X : Type*} [Fintype X] [DecidableEq X] (A : Matrix X X ℂ)
    (v : X → ℂ) :
    ‖(EuclideanSpace.equiv X ℂ).symm (A *ᵥ v)‖ ≤ ‖A‖ * ‖(EuclideanSpace.equiv X ℂ).symm v‖ := by
  simpa using A.l2_opNorm_mulVec ((EuclideanSpace.equiv X ℂ).symm v)

omit [∀ v, NeZero (n v)] in
/-- Cauchy–Schwarz for the dot product, in Euclidean norms. -/
theorem norm_star_dotProduct_le {X : Type*} [Fintype X] (u v : X → ℂ) :
    ‖star u ⬝ᵥ v‖ ≤ ‖(EuclideanSpace.equiv X ℂ).symm u‖ * ‖(EuclideanSpace.equiv X ℂ).symm v‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) ((EuclideanSpace.equiv X ℂ).symm u)
    ((EuclideanSpace.equiv X ℂ).symm v)
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
  simpa using h

omit [∀ v, NeZero (n v)] in
/-- A label observable of a subsystem commutes with one-copy operators supported off it. -/
theorem commute_labelObservable_siteOp_of_disjoint {k : ℕ} {Q D : Finset V}
    {c : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hc : IsSupportedOn c D) (hQD : Disjoint Q D)
    (j : Fin k) (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k (fun v => Fin (n v)) Q) f) (siteOp j c) :=
  commute_labelObservable_of_forall_commute _
    (fun g => commute_permOp_subsystemPerm_siteOp_of_disjoint hc hQD j g) f

omit [∀ v, NeZero (n v)] in
/-- A label observable of the first copies commutes with one-copy operators on the last copy. -/
theorem commute_labelObservable_first_siteOp_last {m : ℕ} (Q : Finset V)
    (c : Matrix (SiteConfig n) (SiteConfig n) ℂ) (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    Commute (labelObservable ((subsystemPerm (m + 1) (fun v => Fin (n v)) Q).comp
      (firstCopies m)) f) (siteOp (Fin.last m) c) :=
  commute_labelObservable_of_forall_commute _ (fun g => by
    have h := commute_permOp_subsystemPerm_siteOp_of_fix (n := n) c Q (π := firstCopies m g)
      (firstCopies_last g)
    simpa only [permOp_apply, MonoidHom.comp_apply] using h) f

omit [∀ v, NeZero (n v)] in
/-- The label observables of all copies and of the first copies of one subsystem commute. -/
theorem commute_labelObservable_first {m : ℕ} (Q : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin (m + 1))) → ℝ) (f' : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    Commute (labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) Q) f)
      (labelObservable ((subsystemPerm (m + 1) (fun v => Fin (n v)) Q).comp
        (firstCopies m)) f') := by
  refine (commute_labelObservable_of_forall_commute _ (fun g => ?_) f').symm
  have h := commute_groupAlgebraRep_permOp_of_mem_center
    (subsystemPerm (m + 1) (fun v => Fin (n v)) Q) (sum_smul_centralIdem_mem_center f)
    (firstCopies m g)
  rw [← labelObservable_eq_groupAlgebraRep] at h
  simpa only [permOp_apply, MonoidHom.comp_apply] using h.symm

omit [∀ v, NeZero (n v)] in
/-- Label observables of the first copies of disjoint subsystems commute with those of all
copies. -/
theorem commute_labelObservable_first_of_disjoint {m : ℕ} {Q Q' : Finset V} (h : Disjoint Q Q')
    (f : IrrepLabel (Equiv.Perm (Fin (m + 1))) → ℝ) (f' : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    Commute (labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) Q) f)
      (labelObservable ((subsystemPerm (m + 1) (fun v => Fin (n v)) Q').comp
        (firstCopies m)) f') :=
  commute_labelObservable_of_commute _ _
    (fun g g' => by
      simpa only [MonoidHom.comp_apply] using
        commute_subsystemPerm_of_disjoint (m + 1) (fun v => Fin (n v)) h g (firstCopies m g'))
    f f'

/-- **Conjugation of a product on the last copy** (`05-replicas.tex`, lines 668–683): for `b`
supported on `Y` and `a` supported on `P`, with `P, Y` disjoint,
`W_Y^{-1} W_P (b a)^{(k)} W_P^{-1} W_Y = (R_Y^{-1} b^{(k)} R_Y)(R_P a^{(k)} R_P^{-1})`. -/
theorem replicaMetric_conj_siteOp_mul {t : ℝ} (ht : 0 ≤ t) (m : ℕ) {P Y : Finset V}
    (hPY : Disjoint P Y) {a b : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (ha : IsSupportedOn a P) (hb : IsSupportedOn b Y) :
    (replicaMetric (fun v => Fin (n v)) t (m + 1) Y)⁻¹ *
        replicaMetric (fun v => Fin (n v)) t (m + 1) P *
          (siteOp (Fin.last m) b * siteOp (Fin.last m) a) *
            (replicaMetric (fun v => Fin (n v)) t (m + 1) P)⁻¹ *
              replicaMetric (fun v => Fin (n v)) t (m + 1) Y =
      ((markedRatio (fun v => Fin (n v)) t m Y)⁻¹ * siteOp (Fin.last m) b *
          markedRatio (fun v => Fin (n v)) t m Y) *
        (markedRatio (fun v => Fin (n v)) t m P * siteOp (Fin.last m) a *
          (markedRatio (fun v => Fin (n v)) t m P)⁻¹) := by
  have hw : ∀ l, replicaLabelWeight (k := m + 1) (fun v => Fin (n v)) t l ≠ 0 :=
    fun l => (replicaLabelWeight_pos _ ht l).ne'
  have hw' : ∀ l, replicaLabelWeight (k := m) (fun v => Fin (n v)) t l ≠ 0 :=
    fun l => (replicaLabelWeight_pos _ ht l).ne'
  -- Names for the six operators.
  set WP := replicaMetric (fun v => Fin (n v)) t (m + 1) P with hWP
  set WY := replicaMetric (fun v => Fin (n v)) t (m + 1) Y with hWY
  set VP := replicaMetricFirst (fun v => Fin (n v)) t m P with hVP
  set VY := replicaMetricFirst (fun v => Fin (n v)) t m Y with hVY
  set a' := siteOp (Fin.last m) a
  set b' := siteOp (Fin.last m) b
  have hWPi : WP⁻¹ = labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) P)
      fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ := labelObservable_inv _ hw
  have hWYi : WY⁻¹ = labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) Y)
      fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ := labelObservable_inv _ hw
  have hVPi : VP⁻¹ = labelObservable ((subsystemPerm (m + 1) (fun v => Fin (n v)) P).comp
      (firstCopies m)) fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ :=
    labelObservable_inv _ hw'
  have hVYi : VY⁻¹ = labelObservable ((subsystemPerm (m + 1) (fun v => Fin (n v)) Y).comp
      (firstCopies m)) fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ :=
    labelObservable_inv _ hw'
  -- Invertibility.
  have hVP1 : VP⁻¹ * VP = 1 := labelObservable_inv_mul_self _ hw'
  have hVY1 : VY * VY⁻¹ = 1 := labelObservable_mul_inv_self _ hw'
  have hVP2 : VP * VP⁻¹ = 1 := labelObservable_mul_inv_self _ hw'
  have hWP1 : WP⁻¹ * WP = 1 := labelObservable_inv_mul_self _ hw
  have hWY1 : WY⁻¹ * WY = 1 := labelObservable_inv_mul_self _ hw
  -- Commutations.
  have c1 : Commute WP b' := commute_labelObservable_siteOp_of_disjoint hb hPY _ _
  have c1' : Commute WP⁻¹ b' := by
    rw [hWPi]; exact commute_labelObservable_siteOp_of_disjoint hb hPY _ _
  have c2 : Commute WY a' := commute_labelObservable_siteOp_of_disjoint ha hPY.symm _ _
  have c3 : Commute WY WP := commute_labelObservable_of_commute _ _
    (commute_subsystemPerm_of_disjoint (m + 1) _ hPY.symm) _ _
  have c3' : Commute WY WP⁻¹ := by
    rw [hWPi]
    exact commute_labelObservable_of_commute _ _
      (commute_subsystemPerm_of_disjoint (m + 1) _ hPY.symm) _ _
  have c4 : Commute VP⁻¹ a' := by
    rw [hVPi]; exact commute_labelObservable_first_siteOp_last P a _
  have c5 : Commute VY b' := commute_labelObservable_first_siteOp_last Y b _
  have c6 : Commute VY WY := (commute_labelObservable_first Y _ _).symm
  have c6' : Commute VY WY⁻¹ := by
    rw [hWYi]; exact (commute_labelObservable_first Y _ _).symm
  -- `R_P a' R_P⁻¹ = W_P a' W_P⁻¹` and `R_Y⁻¹ b' R_Y = W_Y⁻¹ b' W_Y`.
  have hRP : markedRatio (fun v => Fin (n v)) t m P = WP * VP⁻¹ := rfl
  have hRY : markedRatio (fun v => Fin (n v)) t m Y = WY * VY⁻¹ := rfl
  have hRPi : (markedRatio (fun v => Fin (n v)) t m P)⁻¹ = VP * WP⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hRP]
    calc VP * WP⁻¹ * (WP * VP⁻¹) = VP * (WP⁻¹ * WP) * VP⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hWP1, mul_one, hVP2]
  have hRYi : (markedRatio (fun v => Fin (n v)) t m Y)⁻¹ = VY * WY⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [hRY]
    calc VY * WY⁻¹ * (WY * VY⁻¹) = VY * (WY⁻¹ * WY) * VY⁻¹ := by simp only [mul_assoc]
      _ = 1 := by rw [hWY1, mul_one, hVY1]
  have eP : markedRatio (fun v => Fin (n v)) t m P * a' *
      (markedRatio (fun v => Fin (n v)) t m P)⁻¹ = WP * a' * WP⁻¹ := by
    rw [hRPi, hRP]
    calc WP * VP⁻¹ * a' * (VP * WP⁻¹) = WP * (VP⁻¹ * a') * VP * WP⁻¹ := by
          simp only [mul_assoc]
      _ = WP * (a' * VP⁻¹) * VP * WP⁻¹ := by rw [c4.eq]
      _ = WP * a' * (VP⁻¹ * VP) * WP⁻¹ := by simp only [mul_assoc]
      _ = WP * a' * WP⁻¹ := by rw [hVP1, mul_one]
  have eY : (markedRatio (fun v => Fin (n v)) t m Y)⁻¹ * b' *
      markedRatio (fun v => Fin (n v)) t m Y = WY⁻¹ * b' * WY := by
    rw [hRYi, hRY]
    have hX : Commute VY (WY⁻¹ * b' * WY) := (c6'.mul_right c5).mul_right c6
    calc VY * WY⁻¹ * b' * (WY * VY⁻¹) = VY * (WY⁻¹ * b' * WY) * VY⁻¹ := by
          simp only [mul_assoc]
      _ = (WY⁻¹ * b' * WY) * VY * VY⁻¹ := by rw [hX.eq]
      _ = WY⁻¹ * b' * WY := by rw [mul_assoc _ VY, hVY1, mul_one]
  rw [eP, eY]
  have hY : Commute WY (WP * a' * WP⁻¹) := (c3.mul_right c2).mul_right c3'
  calc WY⁻¹ * WP * (b' * a') * WP⁻¹ * WY = WY⁻¹ * (WP * b') * a' * WP⁻¹ * WY := by
        simp only [mul_assoc]
    _ = WY⁻¹ * (b' * WP) * a' * WP⁻¹ * WY := by rw [c1.eq]
    _ = WY⁻¹ * b' * ((WP * a' * WP⁻¹) * WY) := by simp only [mul_assoc]
    _ = WY⁻¹ * b' * (WY * (WP * a' * WP⁻¹)) := by rw [hY.eq]
    _ = WY⁻¹ * b' * WY * (WP * a' * WP⁻¹) := by simp only [mul_assoc]

/-- **Lemma 6.4, uniform boundedness** (`05-replicas.tex`, lines 621–622 and 666–692): for a
one-copy operator `h` supported on `P ∪ Y`, `sup_k ‖O_k‖ < ∞` on the symmetric subspace,
with a bound depending on the fixed system, `t` and `h`. -/
theorem exists_norm_markedSimilarity_mulVec_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2)
    {P Y F : Finset V} (hPY : Disjoint P Y) (hPF : Disjoint P F) (hYF : Disjoint Y F)
    {h : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hh : IsSupportedOn h (P ∪ Y)) :
    ∃ C, ∀ (k : ℕ) (z : Config k (fun v => Fin (n v)) → ℂ),
      z ∈ symmetricSubspace k (fun v => Fin (n v)) →
        ‖(EuclideanSpace.equiv _ ℂ).symm (markedSimilarity n t k P Y F h *ᵥ z)‖ ≤
          C * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ := by
  set ι : V → Type := fun v => Fin (n v)
  have hσ₀ : SiteConfig n := fun _ => 0
  obtain ⟨N, b, a, hb, ha, hdec⟩ :=
    (show IsSupportedOn h (Y ∪ P) by rwa [Finset.union_comm]).exists_sum_mul hPY.symm hσ₀
  obtain ⟨CR, hCR⟩ := exists_l2_opNorm_markedRatio_le ι ht0 (by linarith)
  obtain ⟨CI₀, hCI₀⟩ := exists_norm_markedRatio_inv_mulVec_le ι ht0 ht1
  set CI := max CI₀ 0
  have hCI0 : 0 ≤ CI := le_max_right _ _
  have hCI : ∀ (m : ℕ) (Q : Finset V) (z : Config (m + 1) ι → ℂ),
      z ∈ symmetricSubspace (m + 1) ι →
        ‖(EuclideanSpace.equiv (Config (m + 1) ι) ℂ).symm ((markedRatio ι t m Q)⁻¹ *ᵥ z)‖ ≤
          CI * ‖(EuclideanSpace.equiv (Config (m + 1) ι) ℂ).symm z‖ := fun m Q z hz =>
    (hCI₀ m Q z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set C := ∑ i, (CR * ‖b i‖ * CI) * (CR * ‖a i‖ * CI)
  refine ⟨max C 0, fun k z hz => ?_⟩
  rcases k with _ | m
  · have h0 : copyMean n 0 h = 0 := by simp [copyMean]
    simp only [markedSimilarity, h0, mul_zero, zero_mul, zero_mulVec]
    simp only [map_zero, norm_zero]
    positivity
  have hw : ∀ l, replicaLabelWeight (k := m + 1) (fun v => Fin (n v)) t l ≠ 0 :=
    fun l => (replicaLabelWeight_pos _ ht0.le l).ne'
  set WP := replicaMetric (fun v => Fin (n v)) t (m + 1) P with hWP
  set WF := replicaMetric (fun v => Fin (n v)) t (m + 1) F with hWF
  set WY := replicaMetric (fun v => Fin (n v)) t (m + 1) Y with hWY
  have hWPi : WP⁻¹ = labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) P)
      fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ := labelObservable_inv _ hw
  have hWFi : WF⁻¹ = labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) F)
      fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ := labelObservable_inv _ hw
  have hWYi : WY⁻¹ = labelObservable (subsystemPerm (m + 1) (fun v => Fin (n v)) Y)
      fun l => (replicaLabelWeight (fun v => Fin (n v)) t l)⁻¹ := labelObservable_inv _ hw
  have hWP1 : WP * WP⁻¹ = 1 := labelObservable_mul_inv_self _ hw
  have hWF1 : WF * WF⁻¹ = 1 := labelObservable_mul_inv_self _ hw
  have hWY1 : WY⁻¹ * WY = 1 := labelObservable_inv_mul_self _ hw
  -- The `F` factors cancel.
  have hFP : Commute WF WP := commute_labelObservable_of_commute _ _
    (commute_subsystemPerm_of_disjoint (m + 1) _ hPF.symm) _ _
  have hFPi : Commute WF WP⁻¹ := by
    rw [hWPi]
    exact commute_labelObservable_of_commute _ _
      (commute_subsystemPerm_of_disjoint (m + 1) _ hPF.symm) _ _
  have hFC : Commute WF (copyMean n (m + 1) h) := by
    refine Commute.smul_right (Commute.sum_right _ _ _ fun j _ => ?_) _
    exact commute_labelObservable_siteOp_of_disjoint hh
      (Finset.disjoint_union_right.mpr ⟨hPF.symm, hYF.symm⟩) j _
  have hrootinv : (leafRoot n t (m + 1) P Y F)⁻¹ = WY⁻¹ * WF * WP := by
    refine Matrix.inv_eq_left_inv ?_
    change WY⁻¹ * WF * WP * (WP⁻¹ * WF⁻¹ * WY) = 1
    calc WY⁻¹ * WF * WP * (WP⁻¹ * WF⁻¹ * WY) = WY⁻¹ * WF * (WP * WP⁻¹) * WF⁻¹ * WY := by
          simp only [mul_assoc]
      _ = 1 := by rw [hWP1, mul_one, mul_assoc WY⁻¹, hWF1, mul_one, hWY1]
  have hO : markedSimilarity n t (m + 1) P Y F h =
      WY⁻¹ * WP * copyMean n (m + 1) h * (WP⁻¹ * WY) := by
    rw [markedSimilarity, sqrt_leafMetric ht0.le (m + 1) hPY hPF hYF, hrootinv]
    change WY⁻¹ * WF * WP * copyMean n (m + 1) h * (WP⁻¹ * WF⁻¹ * WY) =
      WY⁻¹ * WP * copyMean n (m + 1) h * (WP⁻¹ * WY)
    have hX : Commute WF (WP * copyMean n (m + 1) h * WP⁻¹) :=
      (hFP.mul_right hFC).mul_right hFPi
    calc WY⁻¹ * WF * WP * copyMean n (m + 1) h * (WP⁻¹ * WF⁻¹ * WY)
        = WY⁻¹ * (WF * (WP * copyMean n (m + 1) h * WP⁻¹)) * WF⁻¹ * WY := by
          simp only [mul_assoc]
      _ = WY⁻¹ * ((WP * copyMean n (m + 1) h * WP⁻¹) * WF) * WF⁻¹ * WY := by rw [hX.eq]
      _ = WY⁻¹ * (WP * copyMean n (m + 1) h * WP⁻¹) * (WF * WF⁻¹) * WY := by
          simp only [mul_assoc]
      _ = WY⁻¹ * WP * copyMean n (m + 1) h * (WP⁻¹ * WY) := by
          rw [hWF1, mul_one]; simp only [mul_assoc]
  -- Commutation with the permutations of entire copies.
  have hcWP : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ) WP := fun τ =>
    commute_copyPerm_labelObservable _ P _ τ
  have hcWY : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ) WY := fun τ =>
    commute_copyPerm_labelObservable _ Y _ τ
  have hcWPi : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ) WP⁻¹ := fun τ => by
    rw [hWPi]; exact commute_copyPerm_labelObservable _ P _ τ
  have hcWYi : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ) WY⁻¹ := fun τ => by
    rw [hWYi]; exact commute_copyPerm_labelObservable _ Y _ τ
  have hcM : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ) (WY⁻¹ * WP) :=
    fun τ => (hcWYi τ).mul_right (hcWP τ)
  have hcN : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ) (WP⁻¹ * WY) :=
    fun τ => (hcWPi τ).mul_right (hcWY τ)
  have hcO : ∀ τ, Commute (permOp (copyPerm (SiteConfig n) (m + 1)) τ)
      (markedSimilarity n t (m + 1) P Y F h) := fun τ => by
    rw [hO]; exact ((hcM τ).mul_right (commute_copyPerm_copyMean _ h τ)).mul_right (hcN τ)
  set u := markedSimilarity n t (m + 1) P Y F h *ᵥ z with hu_def
  have hu : u ∈ symmetricSubspace (m + 1) (fun v => Fin (n v)) := fun τ => by
    change permOp (copyPerm (SiteConfig n) (m + 1)) τ *ᵥ u = u
    rw [hu_def, mulVec_mulVec, (hcO τ).eq, ← mulVec_mulVec, hz τ]
  -- Reduce to the last copy and decompose.
  have hkey : star u ⬝ᵥ u = ∑ i, star u ⬝ᵥ
      ((((markedRatio (fun v => Fin (n v)) t m Y)⁻¹ * siteOp (Fin.last m) (b i) *
          markedRatio (fun v => Fin (n v)) t m Y) *
        (markedRatio (fun v => Fin (n v)) t m P * siteOp (Fin.last m) (a i) *
          (markedRatio (fun v => Fin (n v)) t m P)⁻¹)) *ᵥ z) := by
    change star u ⬝ᵥ (markedSimilarity n t (m + 1) P Y F h *ᵥ z) = _
    rw [hO, star_dotProduct_copyMean_eq (Fin.last m) h hcM hcN hu hz, hdec, siteOp_sum]
    simp_rw [← siteOp_mul_siteOp]
    rw [Finset.mul_sum, Finset.sum_mul, sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← replicaMetric_conj_siteOp_mul ht0.le m hPY (ha i) (hb i)]
    simp only [mul_assoc]
    rfl
  -- Bound each term: both inverses act directly on symmetric vectors.
  have hRherm : ∀ Q, (markedRatio (fun v => Fin (n v)) t m Q).IsHermitian := fun Q => by
    rw [markedRatio_eq_hom _ ht0.le]
    exact (isOrthogonalResolution_branch m Q).isHermitian_hom (isHermitian_branch _ m Q) _
  have hRiherm : ∀ Q, ((markedRatio (fun v => Fin (n v)) t m Q)⁻¹).IsHermitian := fun Q => by
    rw [markedRatio_inv_eq_hom _ ht0.le]
    exact (isOrthogonalResolution_branch m Q).isHermitian_hom (isHermitian_branch _ m Q) _
  have hCR0 : 0 ≤ CR := (norm_nonneg _).trans (hCR m P)
  have hstep : ∀ (Q : Finset V) (c : Matrix (SiteConfig n) (SiteConfig n) ℂ)
      (x : Config (m + 1) (fun v => Fin (n v)) → ℂ),
      x ∈ symmetricSubspace (m + 1) (fun v => Fin (n v)) →
        ‖(EuclideanSpace.equiv _ ℂ).symm ((markedRatio (fun v => Fin (n v)) t m Q *
            siteOp (Fin.last m) c * (markedRatio (fun v => Fin (n v)) t m Q)⁻¹) *ᵥ x)‖ ≤
          CR * ‖c‖ * CI * ‖(EuclideanSpace.equiv _ ℂ).symm x‖ := by
    intro Q c x hx
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    calc _ ≤ ‖markedRatio (fun v => Fin (n v)) t m Q‖ *
          ‖(EuclideanSpace.equiv _ ℂ).symm (siteOp (Fin.last m) c *ᵥ
            ((markedRatio (fun v => Fin (n v)) t m Q)⁻¹ *ᵥ x))‖ := norm_mulVec_le _ _
      _ ≤ CR * (‖siteOp (Fin.last m) c‖ * ‖(EuclideanSpace.equiv _ ℂ).symm
            ((markedRatio (fun v => Fin (n v)) t m Q)⁻¹ *ᵥ x)‖) :=
          mul_le_mul (hCR m Q) (norm_mulVec_le _ _) (norm_nonneg _) hCR0
      _ ≤ CR * (‖c‖ * (CI * ‖(EuclideanSpace.equiv _ ℂ).symm x‖)) := by
          gcongr
          · exact l2_opNorm_siteOp_le _ _
          · exact hCI m Q x hx
      _ = CR * ‖c‖ * CI * ‖(EuclideanSpace.equiv _ ℂ).symm x‖ := by ring
  have hterm : ∀ i, ‖star u ⬝ᵥ
      ((((markedRatio (fun v => Fin (n v)) t m Y)⁻¹ * siteOp (Fin.last m) (b i) *
          markedRatio (fun v => Fin (n v)) t m Y) *
        (markedRatio (fun v => Fin (n v)) t m P * siteOp (Fin.last m) (a i) *
          (markedRatio (fun v => Fin (n v)) t m P)⁻¹)) *ᵥ z)‖ ≤
      CR * ‖b i‖ * CI * (CR * ‖a i‖ * CI) *
        (‖(EuclideanSpace.equiv _ ℂ).symm u‖ * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) := by
    intro i
    set RY := markedRatio (fun v => Fin (n v)) t m Y
    have hadj : (RY⁻¹ * siteOp (Fin.last m) (b i) * RY)ᴴ =
        RY * siteOp (Fin.last m) (b i)ᴴ * RY⁻¹ := by
      rw [conjTranspose_mul, conjTranspose_mul, (hRherm Y).eq, (hRiherm Y).eq,
        conjTranspose_siteOp, mul_assoc]
    rw [← mulVec_mulVec, dotProduct_mulVec, ← conjTranspose_conjTranspose
      (RY⁻¹ * siteOp (Fin.last m) (b i) * RY), ← star_mulVec, hadj]
    refine (norm_star_dotProduct_le _ _).trans ?_
    have h1 := hstep Y (b i)ᴴ u hu
    rw [l2_opNorm_conjTranspose] at h1
    have h2 := hstep P (a i) z hz
    calc _ ≤ (CR * ‖b i‖ * CI * ‖(EuclideanSpace.equiv _ ℂ).symm u‖) *
          (CR * ‖a i‖ * CI * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hsum : ‖star u ⬝ᵥ u‖ ≤
      C * (‖(EuclideanSpace.equiv _ ℂ).symm u‖ * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) := by
    rw [hkey, Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
  have hsq : ‖(EuclideanSpace.equiv _ ℂ).symm u‖ ^ 2 ≤
      C * (‖(EuclideanSpace.equiv _ ℂ).symm u‖ * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) := by
    rw [← re_star_dotProduct_self_eq_norm_sq]
    exact (RCLike.re_le_norm _).trans hsum
  have hz0 := norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm z)
  rcases (norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm u)).eq_or_lt with hu0 | hu0
  · rw [← hu0]; positivity
  · have : ‖(EuclideanSpace.equiv _ ℂ).symm u‖ ≤ C * ‖(EuclideanSpace.equiv _ ℂ).symm z‖ := by
      nlinarith
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hz0)

end TensorPower
