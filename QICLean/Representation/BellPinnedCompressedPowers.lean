/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellPinnedProductAction
import QICLean.Representation.ReplicaSymmetricBandCommute
import QICLean.Representation.RegionalReplicaMetricRegions

/-!
# Bell restriction in fixed symmetric coordinates

Fix one isometry onto the simultaneous symmetric space. Each original band
factor is compressed by this same isometry, and the same weighted mean tree
is evaluated in every band. Their ordered product is the matrix used in the
lower norm bounds. Its powers agree with the exterior product through the
actual Bell-inserted symmetric operator. All replica weights belong to the
original full family.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 80–110, 299–308 and
  370–381, `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation FiniteProduct
open scoped InnerProductSpace ComplexOrder MatrixOrder
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => compressedSiteSpace β X R

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
    (b : (Configuration β X × C) → ℂ) (T : Matrix.MeanTree S) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe (Configuration β X × C) k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
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
      (List.ofFn fun g ↦ T.eval (A · g)).prod * Z = Z * M := by
    have h := List.prod_hom_rel (List.ofFn (id : Fin K → Fin K))
      (r := fun L R ↦ L * Z = Z * R)
      (f := fun g ↦ T.eval (A · g)) (g := fun g ↦ T.eval (B · g))
      (by simp only [Matrix.one_mul, Matrix.mul_one]) (by
        intro g L R hLR
        rw [Matrix.mul_assoc, hLR, ← Matrix.mul_assoc, hband g, Matrix.mul_assoc])
    simpa only [M, List.map_ofFn, Function.comp_id] using h
  have hPe : Pe * Pe = Pe :=
    (exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k))
      (X := Config k ιe)).elim (fun l hl ↦
        Eq.mp (congrArg (fun H ↦ H * H = H) (hl (copyPerm
          ((v : Option ↥(Xᶜ)) → ιe v) k)))
          (labelProj_mul_self _ l))
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
