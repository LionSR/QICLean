/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSymmetricBandCommute

/-!
# The common-tree product in fixed symmetric coordinates

The actual mean of the compressed ordered multiband leaves equals the
ordered product of the compressed band means. Every band uses the same
weighted tree, exactly as in the comparator proposition. The compression
identity is derived from the original band intertwiners.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, `comparator:metrics`,
  lines 99–121, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
variable (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable [∀ f, Nonempty (ι f)] {J : Type*}

local instance replicaSymmetricMeanTreeProduct_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- For the original nested regional metrics, compression of an ordered
leaf product equals the product of the actual band compressions, and
the same weighted tree commutes with this product. No product identity
or commutation hypothesis is supplied: both follow from the original
regional geometry and the fixed symmetric isometry. -/
theorem replicaMetric_symProj_meanTree_eq_product
    (k n : ℕ) (Z : Matrix (Config k ι) (Fin n) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((f : F) → ι f) k))
    {t : ℝ} (ht : 0 ≤ t) (K : ℕ)
    (Q Y : J → Fin K → Finset F)
    (hdisj : ∀ j g, Disjoint (Q j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → Q j g ∪ Y j g ⊆ Q j' h) :
    let A := fun j g => ((replicaMetric ι t k (Q j g))⁻¹ *
      (replicaMetric ι t k (Q j g ∪ Y j g)ᶜ)⁻¹ *
        replicaMetric ι t k (Y j g)) ^ 2
    let B := fun j g => Zᴴ * A j g * Z
    (∀ j, Zᴴ * (List.ofFn (A j)).prod * Z = (List.ofFn (B j)).prod) ∧
      ∀ T : MeanTree J,
        T.eval (fun j => Zᴴ * (List.ofFn (A j)).prod * Z) =
          (List.ofFn fun g => T.eval (B · g)).prod := by
  intro A B
  obtain ⟨hleaf, hcomm⟩ :=
    replicaMetric_symProj_compressions_posDef_commute ι k n Z hZ hZZ ht K Q Y hdisj hnest
  have hprod (j : J) :
      (List.ofFn (A j)).prod * Z = Z * (List.ofFn (B j)).prod := by
    have h := List.prod_hom_rel (List.ofFn (id : Fin K → Fin K))
      (r := fun L R => L * Z = Z * R) (f := A j) (g := B j)
      (by simp only [Matrix.one_mul, Matrix.mul_one]) (by
        intro g L R hLR
        rw [Matrix.mul_assoc, hLR, ← Matrix.mul_assoc,
          (hleaf j g).2.1, Matrix.mul_assoc])
    simpa only [List.map_ofFn, Function.comp_id] using h
  have hcompression (j : J) :
      Zᴴ * (List.ofFn (A j)).prod * Z = (List.ofFn (B j)).prod := by
    rw [Matrix.mul_assoc, hprod, ← Matrix.mul_assoc, hZ, one_mul]
  refine ⟨hcompression, ?_⟩
  intro T
  simp_rw [hcompression]
  exact MeanTree.eval_listProd_ofFn (fun j g => (hleaf j g).1) hcomm T

end TensorPower
