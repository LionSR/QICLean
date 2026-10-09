/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaWholeInverse
import QICLean.Representation.ReplicaDisjointMetricPositivity
import QICLean.Representation.GroupedLabelSymmetricSupport
import QICLean.Analysis.ProjectionCfcUpperBound
import QICLean.Analysis.InverseCompressionLowerPin

/-!
# A common floor for symmetric replica metrics

For a disjoint partition of the full site family into three regions, the
signed label entropy is nonnegative on the simultaneous symmetric space.
The whole-space exponential comparison for the inverse metric therefore
gives a polynomial inverse bound on this space, and hence a reciprocal
polynomial floor for the original metric.

The constant depends only on the original local spaces and the fixed
replica exponent. It precedes the copy number and all three regions. The
same floor holds in every fixed isometric coordinate system for the
simultaneous symmetric space; no new choice of coordinates is made.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 585--615, `comparator:lower-pin` and the
common symmetric-space floor preceding `comparator:tree-log-lower`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
variable [∀ v, Nonempty (ι v)]

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
      Y ∪ (P ∪ F) = Finset.univ →
      let Q := symProj (copyPerm ((v : V) → ι v) k)
      let W := replicaMetric ι t k
      let A := ((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2
      Q * A⁻¹ * Q ≤ ((k : ℝ) + 2) ^ C • Q ∧
        ((k : ℝ) + 2) ^ (-C) • Q ≤ A := by
  obtain ⟨C, hC, hwhole⟩ := exists_replicaMetric_inv_square_le_exp ι ht
  refine ⟨C, hC, ?_⟩
  intro k P Y F hPY hPF hYF hcover Q W A
  let L := fun S => labelEntropy (subsystemPerm k ι S)
  let G := L P + L F - L Y
  let p : ℝ := ((k : ℝ) + 2) ^ C
  have hp : 0 < p := Real.rpow_pos_of_pos (by positivity) C
  have hQ : IsStarProjection Q :=
    (exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k))
      (X := Config k ι)).elim (fun l hl =>
        Eq.mp (congrArg IsStarProjection (hl (copyPerm ((v : V) → ι v) k)))
          (show IsStarProjection (labelProj (copyPerm ((v : V) → ι v) k) l) from
            ⟨labelProj_mul_self _ l, (isHermitian_labelProj _ l).isSelfAdjoint⟩))
  have hQH : Q.IsHermitian := hQ.isSelfAdjoint.isHermitian
  have hG : G.IsHermitian :=
    ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)
  have hsupport : Commute G Q ∧ 0 ≤ Q * G * Q := by
    simpa only [MonoidHom.comp_id, subsystemPerm_univ] using
      subgroup_signedLabelEntropy_symProj_nonneg ι
        (MonoidHom.id (Equiv.Perm (Fin k))) P Y F hPY hPF hYF hcover
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
      Y ∪ (P ∪ F) = Finset.univ →
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

end TensorPower
