/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Irreducible.Similarity
import QICLean.Channel.Irreducible.SpectralRadius
import QICLean.Channel.KrausGauge
import QICLean.Kraus.InvariantProjection

/-!
# Irreducibility under Kraus gauge transformations

Positive-definite TP gauging acts on the associated Kraus map by an invertible similarity.
Consequently it preserves map primitivity and irreducibility of the finite matrix family.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace Kraus

variable {d D : ℕ}

/-- The map of a TP-gauged family is the similarity transform of the original map by the
positive square root of the adjoint fixed point. -/
lemma mapLM_tpGauge_eq_similarityMap
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosDef) :
    mapLM (tpGauge K σ) =
      similarityMap (D := D) (CFC.sqrt σ)⁻¹ (mapLM K) := by
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_det : IsUnit S.det := by
    simpa [S] using Matrix.PosDef.isUnit_det_cfc_sqrt hσ
  have hS_herm : Sᴴ = S := by
    simpa [S] using Matrix.conjTranspose_cfc_sqrt σ
  have hS_inv_inv : S⁻¹⁻¹ = S := Matrix.nonsing_inv_nonsing_inv S hS_det
  have hS_inv_herm : (S⁻¹)ᴴ = (Sᴴ)⁻¹ := Matrix.conjTranspose_nonsing_inv S
  have hS_inv_herm' : (S⁻¹)ᴴ = S⁻¹ := by simpa [hS_herm] using hS_inv_herm
  ext X i j
  have hcalc :
      mapLM (tpGauge K σ) X =
        similarityMap (D := D) S⁻¹ (mapLM K) X := by
    calc
      mapLM (tpGauge K σ) X
          = ∑ i : Fin d, (S * K i * S⁻¹) * X * (S * K i * S⁻¹)ᴴ := by
              simp [mapLM_apply, tpGauge, S]
      _ = ∑ i : Fin d, S * (K i * (S⁻¹ * X * S⁻¹ * (K i)ᴴ)) * S := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
              Matrix.conjTranspose_nonsing_inv]
            simp [Matrix.mul_assoc, hS_herm]
      _ = S * (∑ i : Fin d, K i * (S⁻¹ * X * S⁻¹ * (K i)ᴴ)) * S := by
            simp only [← Matrix.sum_mul, ← Matrix.mul_sum]
      _ = similarityMap (D := D) S⁻¹ (mapLM K) X := by
            simp [similarityMap, mapLM_apply, S, hS_inv_inv, hS_inv_herm',
              Matrix.mul_assoc]
  exact congrFun (congrFun hcalc i) j

/-- Positive-definite TP gauging preserves peripheral-spectrum primitivity. -/
lemma isPrimitive_mapLM_tpGauge_iff
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosDef) :
    _root_.IsPrimitive (mapLM (tpGauge K σ)) ↔
      _root_.IsPrimitive (mapLM K) := by
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_det : S.det ≠ 0 := by
    exact (Matrix.PosDef.isUnit_det_cfc_sqrt hσ).ne_zero
  rw [mapLM_tpGauge_eq_similarityMap K σ hσ]
  exact IsPrimitive.similarityMap_iff S⁻¹ (by simpa [Matrix.det_nonsing_inv] using hS_det) _

/-- TP gauging preserves family irreducibility when the original Kraus map is irreducible. -/
lemma isIrreducibleFamily_tpGauge_of_isIrreducibleMap
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (σ : Matrix (Fin D) (Fin D) ℂ)
    (hσ : σ.PosDef)
    (hIrr : IsIrreducibleMap (mapLM K)) :
    Kraus.IsIrreducibleFamily (d := d) (D := D) (tpGauge K σ) := by
  set S : Matrix (Fin D) (Fin D) ℂ := CFC.sqrt σ
  have hS_det : S.det ≠ 0 := by
    exact (Matrix.PosDef.isUnit_det_cfc_sqrt hσ).ne_zero
  have hIrrSim :
      IsIrreducibleMap (similarityMap (D := D) S⁻¹ (mapLM K)) := by
    refine isIrreducibleMap_similarity (D := D) ?_ hIrr
    simpa [S, Matrix.det_nonsing_inv] using inv_ne_zero hS_det
  have hEq :
      mapLM (tpGauge K σ) =
        similarityMap (D := D) S⁻¹ (mapLM K) := by
    simpa [S] using mapLM_tpGauge_eq_similarityMap (K := K) (σ := σ) hσ
  have hIrr' : IsIrreducibleMap
      (mapLM (tpGauge K σ)) := by
    simpa [hEq] using hIrrSim
  exact Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _ hIrr'

/-- Positive-definite TP gauging preserves irreducibility of a finite matrix family. -/
theorem isIrreducibleFamily_tpGauge_iff
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (σ : Matrix (Fin D) (Fin D) ℂ) (hσ : σ.PosDef) :
    IsIrreducibleFamily (tpGauge K σ) ↔ IsIrreducibleFamily K := by
  constructor
  · intro hIrr
    have hMapGauge : IsIrreducibleMap (mapLM (tpGauge K σ)) :=
      isIrreducibleMap_mapLM_of_isIrreducibleFamily _ hIrr
    rw [mapLM_tpGauge_eq_similarityMap K σ hσ] at hMapGauge
    have hS_det : (CFC.sqrt σ)⁻¹.det ≠ 0 := by
      simpa [Matrix.det_nonsing_inv] using
        (Matrix.PosDef.isUnit_det_cfc_sqrt hσ).ne_zero
    have hMap : IsIrreducibleMap (mapLM K) :=
      (isIrreducibleMap_similarity_iff (D := D) hS_det).1 hMapGauge
    exact isIrreducibleFamily_of_isIrreducibleMap_mapLM K hMap
  · intro hIrr
    exact isIrreducibleFamily_tpGauge_of_isIrreducibleMap K σ hσ
      (isIrreducibleMap_mapLM_of_isIrreducibleFamily K hIrr)

end Kraus
