/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.IsometricDomainExtension
import QICLean.Representation.ReplicaSymmetricMeanTreeProduct

/-!
# Original labels after the common band-product mean

The matrix below is the ordered product of the band roots of one common
weighted tree. Its leaves are the actual original regional metric factors,
compressed by a single isometry onto simultaneous copy symmetry. Positivity,
normalization, symmetry and preservation of the original single-site labels
are conclusions, rather than additional hypotheses on the final vector.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `05-replicas.tex`, lines 101--103; `06-transport.tex`, lines 388--401;
`07-comparators.tex`, lines 421--443, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
variable (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)]

local instance replicaBandLabelPreservationConfigDecidableEq (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The normalized inverse power of the actual common-tree band product
retains each original single-site label. The geometric hypotheses are the
cross-status nesting in `07-comparators.tex`, `comparator:nesting`; label
preservation is used in `comparator:defect-mass`, lines 421--443. -/
theorem replicaMetric_normalized_symProj_bandProduct_mem_original_labels
    (k n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((f : F) → ι f) k))
    {t : ℝ} (ht : 0 ≤ t) {J : Type*} (G : ℕ)
    (Q Y : J → Fin G → Finset F)
    (hdisj : ∀ j g, Disjoint (Q j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h)
    (T : Matrix.MeanTree J) :
    let Pe := symProj (copyPerm ((f : F) → ι f) k)
    let A := fun j g ↦ ((replicaMetric ι t k (Q j g))⁻¹ *
      (replicaMetric ι t k (Q j g ∪ Y j g)ᶜ)⁻¹ *
        replicaMetric ι t k (Y j g)) ^ 2
    let B := fun j g ↦ Zᴴ * A j g * Z
    let M := (List.ofFn (fun g ↦ T.eval (B · g))).prod
    M.PosDef ∧ ∀ (s : ℝ) (ξ : EuclideanSpace ℂ (Config k ι)),
      ξ ≠ 0 → Pe *ᵥ ξ = ξ →
      let w := Matrix.toEuclideanLin (M ^ (-s)) (Matrix.toEuclideanLin Zᴴ ξ)
      let v := Matrix.toEuclideanLin Z ((‖w‖⁻¹ : ℂ) • w)
      w ≠ 0 ∧ ‖v‖ = 1 ∧ Pe *ᵥ v = v ∧
        ∀ (a : F) (ell : IrrepLabel (Equiv.Perm (Fin k))),
          labelProj (subsystemPerm k ι {a}) ell *ᵥ ξ = ξ →
          labelProj (subsystemPerm k ι {a}) ell *ᵥ v = v := by
  intro Pe A B M
  have hM : M.PosDef :=
    (replicaMetric_symProj_meanTree_roots_commute ι k n Z hZ hZZ ht G Q Y
      hdisj hnest).elim (fun hroot hcomm ↦
        Matrix.MeanTree.posDef_listProd_ofFn (fun g ↦ hroot g T)
          (fun g h hgh ↦ hcomm g h hgh T T))
  refine ⟨hM, fun s ξ hξ hPξ ↦ ?_⟩
  intro w v
  have hPZ : Pe * Z = Z := by
    dsimp only [Pe]
    rw [← hZZ, Matrix.mul_assoc, hZ, Matrix.mul_one]
  have hrecover : Z *ᵥ (Zᴴ *ᵥ ξ) = ξ :=
    (Matrix.mulVec_mulVec ξ.ofLp Z Zᴴ).trans
      ((congrArg (fun H ↦ H *ᵥ ξ.ofLp) hZZ).trans hPξ)
  have hcoords : Matrix.toEuclideanLin Zᴴ ξ ≠ 0 :=
    fun h ↦ hξ (WithLp.ofLp_injective 2
      (hrecover.symm.trans
        ((congrArg (fun η : Fin n → ℂ ↦ Z *ᵥ η)
          (congrArg WithLp.ofLp h)).trans (Matrix.mulVec_zero Z))))
  have hw : w ≠ 0 :=
    fun h ↦ hcoords (WithLp.ofLp_injective 2
      ((hM.rpow (-s)).mulVec_injective
        ((congrArg WithLp.ofLp h).trans (Matrix.mulVec_zero (M ^ (-s))).symm)))
  have hv : ‖v‖ = 1 :=
    (Matrix.norm_toLp_mulVec_of_isometry Z hZ ((‖w‖⁻¹ : ℂ) • w)).trans
      (norm_smul_inv_norm (𝕜 := ℂ) hw)
  have hPv : Pe *ᵥ v = v :=
    (Matrix.mulVec_mulVec (((‖w‖⁻¹ : ℂ) • w).ofLp) Pe Z).trans
      (congrArg (fun H ↦ H *ᵥ (((‖w‖⁻¹ : ℂ) • w).ofLp)) hPZ)
  have hsingle (a : F) (ell : IrrepLabel (Equiv.Perm (Fin k)))
      (S : Finset F) (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
      Commute (labelProj (subsystemPerm k ι {a}) ell)
        (labelObservable (subsystemPerm k ι S) f) :=
    Commute.sum_right Finset.univ _ _ fun ell' _ ↦
      (if ha : a ∈ S then
        commute_labelProj_subsystemPerm_of_subset ι k
          (Finset.singleton_subset_iff.mpr ha) ell ell'
      else
        commute_labelProj_subsystemPerm_of_disjoint ι k
          (Finset.disjoint_singleton_left.mpr ha) ell ell').smul_right (f ell' : ℂ)
  done

end TensorPower
