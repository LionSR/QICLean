/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaWholeInverse
import QICLean.Representation.ReplicaSymmetricSupport
import QICLean.Representation.TrivialLabel
import QICLean.Analysis.CompressedInverseFloor
import QICLean.Analysis.FloorPin
import QICLean.Analysis.SpectralExponentialDrop
import QICLean.Representation.ReplicaDisjointMetricPositivity
import QICLean.Representation.GroupedLabelSymmetricSupport
import QICLean.Analysis.ProjectionCfcUpperBound
import QICLean.Analysis.InverseCompressionLowerPin

/-!
# A polynomial floor on simultaneous symmetric copies

The partition metric is the literal squared product of the three replica
metrics. The conclusion concerns its compression to simultaneous symmetric
copies and its extension by the identity on the orthogonal complement.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
`05-replicas.tex`, Lemma 6.1(2–3), lines 99–115; Lemma 6.2,
equation `replicas:W-comparison`, lines 305–316; equation
`replicas:leaf-metric`; and `07-comparators.tex`, lines 454–476.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
  [∀ v, Nonempty (ι v)]

/-- The same polynomial exponent gives the compressed inverse bound,
the symmetric-sector floor, and the floor after identity extension.
The exponent is uniform in the copy number and in the partition.
This is the symmetric restriction of the inverse comparison in OpenAI,
`07-comparators.tex`, lines 454–476, using complementary labels and merge
dimensions from `05-replicas.tex`, Lemma 6.1(2–3), lines 99–115.
-/
theorem exists_replicaMetric_symmetric_floor {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset V),
      Disjoint P Y → Disjoint P F → Disjoint Y F →
      P ∪ Y ∪ F = Finset.univ →
      let S := symProj (copyPerm ((v : V) → ι v) k)
      let W := replicaMetric ι t k
      let A := ((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2
      let c : ℝ := ((k : ℝ) + 2) ^ (-C)
      0 < c ∧ c ≤ 1 ∧
        S * A⁻¹ * S ≤ ((c⁻¹ : ℝ) : ℂ) • S ∧
        (c : ℂ) • S ≤ S * A * S ∧
        (c : ℂ) • (1 : Matrix _ _ ℂ) ≤ S * A * S + (1 - S) := by
  obtain ⟨C, hC, hbound⟩ := exists_replicaMetric_inv_square_le_exp ι ht
  refine ⟨C, hC, ?_⟩
  intro k P Y F hPY hPF hYF hcover S W A c
  have hJS := spectralProjectionGE_labelDeficit_mul_symProj_of_partition
    ι k P Y F hPY hPF hYF hcover
  have hSproj : IsStarProjection S := isStarProjection_symProj _
  let H := labelEntropy (subsystemPerm k ι P) +
    labelEntropy (subsystemPerm k ι F) - labelEntropy (subsystemPerm k ι Y)
  have hH : H.IsHermitian :=
    ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)
  have hSJ : S * spectralProjectionGE H 0 = S := by
    simpa only [star_mul, hSproj.isSelfAdjoint.star_eq,
      (hH.isStarProjection_spectralProjectionGE 0).isSelfAdjoint.star_eq] using
      congrArg star (show spectralProjectionGE H 0 * S = S from hJS)
  have hJE : spectralProjectionGE H 0 *
      NormedSpace.exp (((-(2 * t) : ℝ) : ℂ) • H) * spectralProjectionGE H 0 ≤ 1 := by
    simpa only [zero_sub, smul_neg, Complex.ofReal_neg, neg_smul, smul_zero,
      NormedSpace.exp_zero] using
      Matrix.spectralProjectionGE_exp_smul_sub_le hH Matrix.isHermitian_zero
        (Commute.zero_right H) (a := 2 * t) (mul_nonneg (by norm_num) ht.le)
  have hSE := hSproj.isSelfAdjoint.conjugate_le_conjugate hJE
  simp only [mul_assoc, (show spectralProjectionGE H 0 * S = S from hJS),
    mul_one, hSproj.isIdempotentElem.eq] at hSE
  rw [← mul_assoc, hSJ, ← mul_assoc] at hSE
  have hinvreal : S * A⁻¹ * S ≤ ((k : ℝ) + 2) ^ C •
      (S * NormedSpace.exp (((-(2 * t) : ℝ) : ℂ) • H) * S) := by
    simpa only [A, W, H, mul_smul_comm, smul_mul_assoc,
      RCLike.real_smul_eq_coe_smul (K := ℂ)] using!
        hSproj.isSelfAdjoint.conjugate_le_conjugate (hbound k P Y F hPY hPF hYF)
  have hB : 0 < ((k : ℝ) + 2) ^ C := Real.rpow_pos_of_pos (by positivity) C
  have hinv : S * A⁻¹ * S ≤ ((k : ℝ) + 2) ^ C • S :=
    hinvreal.trans (smul_le_smul_of_nonneg_left hSE hB.le)
  have hInv (Q : Finset V) : (W Q)⁻¹ =
      labelObservable (subsystemPerm k ι Q) (fun l => (replicaLabelWeight ι t l)⁻¹) :=
    labelObservable_inv (subsystemPerm k ι Q)
      (fun l => (replicaLabelWeight_pos ι ht.le l).ne')
  have hPF' : Commute (W P)⁻¹ (W F)⁻¹ := by
    simpa only [hInv P, hInv F] using
      commute_labelObservable_of_commute (subsystemPerm k ι P) (subsystemPerm k ι F)
        (commute_subsystemPerm_of_disjoint k ι hPF)
        (fun l => (replicaLabelWeight ι t l)⁻¹) (fun l => (replicaLabelWeight ι t l)⁻¹)
  have hQY (Q : Finset V) (hQY : Disjoint Q Y) : Commute (W Q)⁻¹ (W Y) := by
    simpa only [hInv Q] using!
      commute_labelObservable_of_commute (subsystemPerm k ι Q) (subsystemPerm k ι Y)
        (commute_subsystemPerm_of_disjoint k ι hQY)
        (fun l => (replicaLabelWeight ι t l)⁻¹) (replicaLabelWeight ι t)
  have hL : ((W P)⁻¹ * (W F)⁻¹ * W Y).IsHermitian :=
    (((((isHermitian_replicaMetric ι t k P).inv).commute_iff
      (isHermitian_replicaMetric ι t k F).inv).mp hPF').commute_iff
        (isHermitian_replicaMetric ι t k Y)).mp
          ((hQY P hPY).mul_left (hQY F hYF.symm))
  have hunit : IsUnit ((W P)⁻¹ * (W F)⁻¹ * W Y) :=
    (((posDef_replicaMetric ι ht.le k P).inv.isUnit).mul
      (posDef_replicaMetric ι ht.le k F).inv.isUnit).mul
        (posDef_replicaMetric ι ht.le k Y).isUnit
  have hQS (Q : Finset V) : Commute (W Q)⁻¹ S := by
    simpa only [hInv Q, S, subsystemPerm_univ k ι] using!
      commute_labelObservable_symProj_of_subset ι k Q Finset.univ
        (Finset.subset_univ Q) (fun l => (replicaLabelWeight ι t l)⁻¹)
  have hYS : Commute (W Y) S := by
    simpa only [S, subsystemPerm_univ k ι] using!
      commute_labelObservable_symProj_of_subset ι k Y Finset.univ
        (Finset.subset_univ Y) (replicaLabelWeight ι t)
  have hfloorB := Matrix.compressed_square_floor_of_inv_le
    ((W P)⁻¹ * (W F)⁻¹ * W Y) S hL.isSelfAdjoint hunit hSproj.isIdempotentElem
      (((hQS P).mul_left (hQS F)).mul_left hYS) hB hinv
  have hc : 0 < c ∧ c ≤ 1 :=
    ⟨Real.rpow_pos_of_pos (by positivity) (-C),
      Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [Nat.cast_nonneg (α := ℝ) k]) (neg_nonpos.mpr hC)⟩
  have hcB : c = (((k : ℝ) + 2) ^ C)⁻¹ := Real.rpow_neg (by positivity) C
  have hfloor : c • S ≤ S * A * S := by
    simpa only [A, hcB] using hfloorB
  have hext := Matrix.identity_extension_floor hSproj.le_one hc.2 hfloor
  refine ⟨hc.1, hc.2, ?_, ?_, ?_⟩
  · simpa only [hcB, inv_inv, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hinv
  · simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hfloor
  · simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hext

section IsometricFloor

open scoped Matrix.Norms.L2Operator

local instance replicaSymmetricMetricFloor_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual inverse squared metric has a polynomial bound on the full
simultaneous symmetric space, and the original metric has the reciprocal
floor there. The three regions form an arbitrary disjoint cover, including
empty regions and zero copies. Source: `07-comparators.tex`, lines 603--615. -/
theorem exists_replicaMetric_symProj_inverse_bound_and_floor
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset V),
      Disjoint P Y → Disjoint P F → Disjoint Y F →
      P ∪ Y ∪ F = Finset.univ →
      let Q := symProj (copyPerm ((v : V) → ι v) k)
      let W := replicaMetric ι t k
      let A := ((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2
      Q * A⁻¹ * Q ≤ ((k : ℝ) + 2) ^ C • Q ∧
        ((k : ℝ) + 2) ^ (-C) • Q ≤ A := by
  obtain ⟨C, hC, hwhole⟩ := exists_replicaMetric_inv_square_le_exp ι ht
  refine ⟨C, hC, ?_⟩
  intro k P Y F hPY hPF hYF hcover Q W A
  have hcover' : Y ∪ (P ∪ F) = Finset.univ := by
    rw [← hcover, Finset.union_left_comm, Finset.union_assoc]
  let L := fun S => labelEntropy (subsystemPerm k ι S)
  let G := L P + L F - L Y
  let p : ℝ := ((k : ℝ) + 2) ^ C
  have hp : 0 < p := Real.rpow_pos_of_pos (by positivity) C
  have hQ : IsStarProjection Q := isStarProjection_symProj _
  have hQH : Q.IsHermitian := hQ.isSelfAdjoint.isHermitian
  have hG : G.IsHermitian :=
    ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)
  have hsupport : Commute G Q ∧ 0 ≤ Q * G * Q := by
    simpa only [MonoidHom.comp_id, subsystemPerm_univ] using
      subgroup_signedLabelEntropy_symProj_nonneg ι
        (MonoidHom.id (Equiv.Perm (Fin k))) P Y F hPY hPF hYF hcover'
  have hexp : Q * NormedSpace.exp ((-(2 * t)) • G) * Q ≤ Q := by
    simpa only [mul_zero, Real.exp_zero, one_smul] using
      hG.compression_exp_neg_smul_le_of_lower_bound (b := 0) hQ hsupport.1
        (by simpa only [zero_smul] using hsupport.2) (show 0 ≤ 2 * t by positivity)
  have hinv : A⁻¹ ≤ p • NormedSpace.exp ((-(2 * t)) • G) := by
    simpa only [Complex.coe_smul] using hwhole k P Y F hPY hPF hYF
  have hcompressed : Q * A⁻¹ * Q ≤
      p • (Q * NormedSpace.exp ((-(2 * t)) • G) * Q) := by
    apply Matrix.le_iff.mpr
    simpa only [hQH.eq, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul] using
      (Matrix.le_iff.mp hinv).conjTranspose_mul_mul_same Q
  have hbound : Q * A⁻¹ * Q ≤ p • Q :=
    hcompressed.trans (smul_le_smul_of_nonneg_left hexp hp.le)
  have hA : A.PosDef :=
    posDef_replicaMetric_disjoint_inv_mul_inv_mul_sq ι ht.le k hPF hPY hYF.symm
  refine ⟨hbound, ?_⟩
  simpa only [p, Real.rpow_neg (by positivity : 0 ≤ (k : ℝ) + 2)] using
    hA.inv_smul_projection_le_of_compression_inv_le hQ hp hbound

/-- Every fixed isometry onto the simultaneous symmetric space inherits
the same metric floor and compressed ambient inverse bound. In particular,
this applies to the coordinates chosen before the exponent, regions and
tree in the common symmetric compression family. Source:
`07-comparators.tex`, lines 603--615. -/
theorem exists_replicaMetric_symProj_isometric_floor
    {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset V),
      Disjoint P Y → Disjoint P F → Disjoint Y F →
      P ∪ Y ∪ F = Finset.univ →
      ∀ (n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ),
      Zᴴ * Z = 1 → Z * Zᴴ = symProj (copyPerm ((v : V) → ι v) k) →
      let W := replicaMetric ι t k
      let A := ((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2
      Zᴴ * A⁻¹ * Z ≤ ((k : ℝ) + 2) ^ C • (1 : Matrix (Fin n) (Fin n) ℂ) ∧
        ((k : ℝ) + 2) ^ (-C) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ Zᴴ * A * Z := by
  obtain ⟨C, hC, hmetric⟩ := exists_replicaMetric_symProj_inverse_bound_and_floor ι ht
  refine ⟨C, hC, ?_⟩
  intro k P Y F hPY hPF hYF hcover n Z hZ hZZ W A
  let Q := symProj (copyPerm ((v : V) → ι v) k)
  obtain ⟨hinv, hfloor⟩ :
      Q * A⁻¹ * Q ≤ ((k : ℝ) + 2) ^ C • Q ∧
        ((k : ℝ) + 2) ^ (-C) • Q ≤ A :=
    hmetric k P Y F hPY hPF hYF hcover
  change Z * Zᴴ = Q at hZZ
  have hQZ : Q * Z = Z := by
    rw [← hZZ, Matrix.mul_assoc, hZ, Matrix.mul_one]
  have hZQ : Zᴴ * Q = Zᴴ := by
    rw [← hZZ, ← Matrix.mul_assoc, hZ, Matrix.one_mul]
  have hZQZ : Zᴴ * Q * Z = 1 := by rw [hZQ, hZ]
  have hcompressed : Zᴴ * (Q * A⁻¹ * Q) * Z = Zᴴ * A⁻¹ * Z := by
    calc
      Zᴴ * (Q * A⁻¹ * Q) * Z = (Zᴴ * Q) * A⁻¹ * (Q * Z) := by
        simp only [Matrix.mul_assoc]
      _ = Zᴴ * A⁻¹ * Z := by rw [hZQ, hQZ]
  constructor
  · apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hZQZ, hcompressed] using
      (Matrix.le_iff.mp hinv).conjTranspose_mul_mul_same Z
  · apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, hZQZ] using
      (Matrix.le_iff.mp hfloor).conjTranspose_mul_mul_same Z

end IsometricFloor

end TensorPower
