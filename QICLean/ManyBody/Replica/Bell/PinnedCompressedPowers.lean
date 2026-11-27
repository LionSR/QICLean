/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Bell.PinnedTreeAction
import QICLean.ManyBody.Replica.Metric.SymmetricBandCommute
import QICLean.ManyBody.Replica.Metric.RegionalReplicaMetricRegions
import QICLean.Algebra.Matrix.MatrixCyclicPathSum
import QICLean.Analysis.Isometry.IsometricDomainExtension
import QICLean.ManyBody.Replica.Bell.InsertionSymmetry

/-!
# Bell restriction in fixed symmetric coordinates

Fix one isometry onto the simultaneous symmetric space. Each original band
factor is compressed by this same isometry, and the same weighted mean tree
is evaluated in every band. Their ordered product is the matrix used in the
lower norm bounds. Its powers agree with the exterior product through the
actual Bell-inserted symmetric operator. All replica weights belong to the
original full family.

## Main results

* `TensorPower.bellCompressedInverseNormConfigDecidableEq`,
  `TensorPower.exists_replicaMetric_compressed_bell_inverse_norm_bound`: inverse powers in the
  supplied symmetric coordinates.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 80–110, 299–308 and
  370–381, `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped InnerProductSpace ComplexOrder MatrixOrder
open scoped Matrix.Norms.L2Operator

section PinnedCompressedPowers

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => ManyBody.compressedSiteSpace β X R

local instance bellPinnedCompressedPowersConfigDecidableEq (k : ℕ) : DecidableEq (Config k ι₀) :=
  Fintype.decidablePiFintype

/-- The ordered product of the actual compressed band means is positive
and its real powers intertwine with the exterior product through the Bell
operator. The same supplied symmetric coordinates are retained throughout.
The inserted vector is arbitrary; it need not be a unit vector.

Source: area-law manuscript, `07-comparators.tex`, lines 80–110, 299–308
and 370–381, `comparator:pinned-metric`. -/
theorem replicaMetric_compressed_bandProduct_bellPin_rpow {S : Type*}
    [∀ v, Nonempty (ι₀ v)] (k n : ℕ) (Z : Matrix (Config k ι₀) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((v : Option (Option V)) → ι₀ v) k))
    {t : ℝ} (ht : 0 ≤ t) (K : ℕ) (U Y : S → Fin K → Finset V)
    (hdisj : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h)
    (b : (ManyBody.RegionConfig β X × C) → ℂ) (T : Matrix.MeanTree S) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe (ManyBody.RegionConfig β X × C) k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option {v // v ∉ X}) → ιe v) k)
    let P := J * Pe * Jᴴ
    let W := replicaMetric ι₀ t k
    let Q := fun j g ↦ insert (some none)
      ((X ∪ U j g).image fun v ↦ some (some v))
    let F := fun j g ↦ insert none
      (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
    let E := fun B : Finset V ↦ (B \ X).image fun v ↦ some (some v)
    let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (E (Y j g))) ^ 2
    let D := fun j g ↦ ((W (E (U j g)))⁻¹ *
      (W (E (U j g ∪ Y j g)))⁻¹ * W (E (Y j g))) ^ 2
    let B := fun j g ↦ Zᴴ * A j g * Z
    let M := (List.ofFn fun g ↦ T.eval (B · g)).prod
    let N := (List.ofFn fun g ↦ T.eval (D · g)).prod
    M.PosDef ∧ ∀ s : ℝ, (Z * M ^ s * Zᴴ) * P = P * N ^ s := by
  classical
  intro e J Pe P W Q F E A D B M N
  have hgeometry := replicaMetric_lifted_region_geometry K
    (fun j g ↦ X ∪ U j g) (fun j g ↦ Y j g \ X)
    (fun j g ↦ Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_sdiff, (hdisj j g).mono_right Finset.sdiff_subset⟩)
    (fun j j' g h hgh ↦ Finset.union_subset
      (Finset.union_subset_union_right
        (Finset.subset_union_left.trans (hnest j j' g h hgh)))
      ((Finset.sdiff_subset.trans
        (Finset.subset_union_right.trans (hnest j j' g h hgh))).trans
          Finset.subset_union_right))
  have hunion (j : S) (g : Fin K) :
      (X ∪ U j g) ∪ (Y j g \ X) = X ∪ (U j g ∪ Y j g) := by
    simp only [Finset.union_assoc, Finset.union_left_comm X (U j g),
      Finset.union_sdiff_self_eq_union]
  have hfar (j : S) (g : Fin K) : F j g = (Q j g ∪ E (Y j g))ᶜ := by
    simpa only [hunion] using hgeometry.2.1 j g
  have hleaf (j : S) (g : Fin K) :
      (B j g).PosDef ∧ A j g * Z = Z * B j g := by
    simpa only [B, A, W, hfar] using
      (let h := (replicaMetric_symProj_compressions_posDef_commute ι₀ k n Z hZ hZZ ht K
        Q (fun j g ↦ E (Y j g)) hgeometry.1 hgeometry.2.2).1 j g
       And.intro h.1 h.2.1)
  have hM : M.PosDef := by
    simpa only [M, B, A, W, hfar] using
      (let hroots := replicaMetric_symProj_meanTree_roots_commute ι₀ k n Z hZ hZZ ht K
        Q (fun j g ↦ E (Y j g)) hgeometry.1 hgeometry.2.2
       Matrix.MeanTree.posDef_listProd_ofFn (fun g ↦ hroots.1 g T)
         (fun g h hgh ↦ hroots.2 g h hgh T T))
  have hband (g : Fin K) : T.eval (A · g) * Z = Z * T.eval (B · g) :=
    Matrix.MeanTree.eval_intertwine
      (fun j ↦ (posDef_bellMetric_factors β X C R ht k (U j g) (Y j g)
        (hdisj j g)).1)
      (fun j ↦ (hleaf j g).1) Z (fun j ↦ (hleaf j g).2) T
  have hprod :
      (List.ofFn fun g ↦ T.eval (A · g)).prod * Z = Z * M :=
    Matrix.listProd_ofFn_intertwine Z hband
  have hPe : Pe * Pe = Pe :=
    (isStarProjection_symProj
      (copyPerm ((v : Option {v // v ∉ X}) → ιe v) k)).isIdempotentElem.eq
  have hPcontain : Z * Zᴴ * P = P := by
    rw [hZZ]
    change symProj (copyPerm ((v : Option (Option V)) → ι₀ v) k) *
      (J * Pe * Jᴴ) = J * Pe * Jᴴ
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      symProj_mul_bellInsertion β X C R k b, Matrix.mul_assoc J Pe Pe, hPe]
  have hbell : N.PosDef ∧
      (List.ofFn fun g ↦ T.eval (A · g)).prod * P = P * N := by
    have h := replicaMetric_bandProduct_bellPin β X C R ht k K U Y hdisj hnest b T
    exact ⟨h.1, h.2.2.2⟩
  have hL : M * (Zᴴ * P) = Zᴴ * P * N := by
    calc M * (Zᴴ * P) = Zᴴ * (Z * M) * Zᴴ * P := by
          rw [← Matrix.mul_assoc Zᴴ Z M, hZ, Matrix.one_mul, Matrix.mul_assoc]
      _ = Zᴴ * (List.ofFn fun g ↦ T.eval (A · g)).prod * (Z * Zᴴ * P) := by
          rw [← hprod]; simp only [Matrix.mul_assoc]
      _ = Zᴴ * P * N := by
          rw [hPcontain, Matrix.mul_assoc, hbell.2, ← Matrix.mul_assoc]
  refine ⟨hM, fun s ↦ ?_⟩
  have h := Matrix.PosSemidef.rpow_intertwine hM.posSemidef hbell.1.posSemidef
    (Zᴴ * P) hL s
  calc Z * M ^ s * Zᴴ * P = Z * (M ^ s * (Zᴴ * P)) := by simp only [Matrix.mul_assoc]
    _ = P * N ^ s := by rw [h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPcontain]

end TensorPower

end

end PinnedCompressedPowers

section CompressedInverseNorm

/-!
## Inverse powers in the supplied symmetric coordinates

The inverse-power cutoff estimate for the exterior replica metric is
transferred to the actual compressed band product. The same supplied
isometry is used in both the matrix and the vector. All weights belong to
the original full family, and the polynomial constant is uniform before
the copy number, regions, tree, cutoff and vectors are specified.

The estimate is stated for a supplied unit test vector satisfying the
actual exterior cutoffs and a supplied unit inserted vector. Its application
to the selected physical state must derive these conditions separately.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 299–308 and 370–381,
`comparator:pinned-metric`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => ManyBody.compressedSiteSpace β X R

local instance bellCompressedInverseNormConfigDecidableEq (k : ℕ) : DecidableEq (Config k ι₀) :=
  Fintype.decidablePiFintype

/-- The cutoff inverse-norm estimate in the same supplied symmetric
coordinates as the lower bound. The original full-family weights are
retained. Source: area-law manuscript, `07-comparators.tex`, lines 299–308
and 370–381, `comparator:pinned-metric`. -/
theorem exists_replicaMetric_compressed_bell_inverse_norm_bound {S : Type*}
    [Finite S] [∀ v, Nonempty (ι₀ v)] {t : ℝ} (ht : 0 < t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (k n : ℕ) (Z : Matrix (Config k ι₀) (Fin n) ℂ),
      Zᴴ * Z = 1 →
      Z * Zᴴ = symProj (copyPerm ((v : Option (Option V)) → ι₀ v) k) →
      ∀ (K : ℕ) (U Y : S → Fin K → Finset V),
      (∀ j g, Disjoint (U j g) (Y j g)) →
      (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
      ∀ b : (ManyBody.RegionConfig β X × C) → ℂ, ‖WithLp.toLp 2 b‖ = 1 →
      ∀ (T : Matrix.MeanTree S) (a : ℝ) (φ u : EuclideanSpace ℂ (Config k ι₀)),
      ‖φ‖ = 1 →
      let E := fun B : Finset V ↦ (B \ X).image fun v ↦ some (some v)
      (∀ j g,
        toEuclideanLin (labelCutoff (subsystemPerm k ι₀ (E (U j g))) a) φ = φ ∧
        toEuclideanLin (labelCutoff (subsystemPerm k ι₀ (E (U j g ∪ Y j g))) a) φ = φ) →
      ∀ s : ℝ, 2 * s ∈ Set.Icc (0 : ℝ) 1 →
      let e := bellInsertionCopyEquiv β X C R k
      let J := (addedSiteInsertion ιe (ManyBody.RegionConfig β X × C) k b).submatrix e id
      let Pe := symProj (copyPerm ((v : Option {v // v ∉ X}) → ιe v) k)
      let P := J * Pe * Jᴴ
      let W := replicaMetric ι₀ t k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun v ↦ some (some v))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (E (Y j g))) ^ 2
      let B := fun j g ↦ Zᴴ * A j g * Z
      let M := (List.ofFn fun g ↦ T.eval (B · g)).prod
      ‖inner ℂ φ (toEuclideanLin P u)‖ ^ 2 ≤
        (((k : ℝ) + 2) ^ (c * (K : ℝ)) * Real.exp (4 * t * (K : ℝ) * a)) ^
          (2 * s) * ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ u)‖ ^ 2 := by
  classical
  obtain ⟨c, hc, hC⟩ := exists_replicaPinnedTree_inverse_norm_bound (J := S) ι₀ ht
  refine ⟨c, hc, fun k n Z hZ hZZ K U Y hdisj hnest b hb T a φ u hφ ↦ ?_⟩
  intro E hcuts s hs e J Pe P W Q F A B M
  have hnorm :=
    let hp := replicaMetric_compressed_bandProduct_bellPin_rpow
      β X C R k n Z hZ hZZ ht.le K U Y hdisj hnest b T
    let hn := (replicaMetric_bandProduct_bellPin
      β X C R ht.le k K U Y hdisj hnest b T).1
    Matrix.norm_projected_le_of_isometric_intertwine
      (hp.1.rpow_isHermitian (-s)) (hn.rpow_isHermitian (-s))
      (isStarProjection_bellInsertion_symProj β X C R k b hb)
      hZ (hp.2 (-s)) u
  have hupper := hC k K (fun j g ↦ E (U j g)) (fun j g ↦ E (Y j g))
    (fun j g ↦ (Finset.disjoint_image
      ((Option.some_injective (Option V)).comp (Option.some_injective V))).2
        (Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset (hdisj j g)))
    (fun j j' g h hgh ↦ by
      simpa only [E, Finset.union_sdiff_distrib, Finset.image_union] using
        (Finset.image_subset_image (f := fun v : V ↦ some (some v))
          (Finset.sdiff_subset_sdiff_left X (hnest j j' g h hgh))))
    T a φ (toEuclideanLin P u) hφ
    (by simpa only [E, Finset.union_sdiff_distrib, Finset.image_union] using hcuts)
    s hs
  exact hupper.trans (mul_le_mul_of_nonneg_left
    (by simpa only [M, B, A, W, Q, F, E, Finset.union_sdiff_distrib,
      Finset.image_union] using
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (by positivity))

end TensorPower

end

end CompressedInverseNorm
