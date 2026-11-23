/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Matrix.MatrixReindex
import QICLean.Channel.FixedPoint.DirectSum.DirectSumExtension
import QICLean.Channel.FixedPoint.DensityBlock.TraceAdjointDensityBlocks

/-!
# Density-block form for fixed points on finite sums of matrix algebras

The canonical full-matrix extension of a map on a finite direct sum may be
reindexed by a finite equivalence and then classified by the full-support
fixed-point theorem. This file carries out that last change of coordinates and
returns the density-block description to the original direct-sum index space.

This is the fixed-point step used in arXiv:1606.00608, Appendix C.4,
lines 1980--1995. The channel hypotheses for the particular transported sector
maps are separate from the result proved here.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators Kronecker

noncomputable section

namespace Matrix

variable {α β : Type*} [Fintype α] [DecidableEq α]
variable [Fintype β] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in
private theorem reindex_conjugation (e : α ≃ β)
    (U A : Matrix α α ℂ) :
    Matrix.reindex e e (star U * A * U) =
      star (Matrix.reindex e e U) * Matrix.reindex e e A *
        Matrix.reindex e e U := by
  have hstar : Matrix.reindex e e (star U) =
      star (Matrix.reindex e e U) := by
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  calc
    Matrix.reindex e e (star U * A * U) =
        Matrix.reindex e e (star U * A) * Matrix.reindex e e U :=
      (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e (star U * A) U).symm
    _ = (Matrix.reindex e e (star U) * Matrix.reindex e e A) *
        Matrix.reindex e e U := by
      exact congrArg (· * Matrix.reindex e e U)
        (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e (star U) A).symm
    _ = _ := by rw [hstar]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
private theorem reindex_symm_reindex (e : α ≃ β) (A : Matrix α α ℂ) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e A) = A := by
  simpa only [Matrix.coe_reindexLinearEquiv,
    Matrix.symm_reindexLinearEquiv] using
    (Matrix.reindexLinearEquiv ℂ ℂ e e).symm_apply_apply A

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
private theorem reindex_reindex {γ : Type*} (e : α ≃ β) (f : β ≃ γ)
    (A : Matrix α α ℂ) :
    Matrix.reindex f f (Matrix.reindex e e A) =
      Matrix.reindex (e.trans f) (e.trans f) A := by
  rfl

end Matrix

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]

omit [∀ k, DecidableEq (n k)] in
/-- The canonical full-matrix extension, after a simultaneous reindexing,
inherits positivity, trace preservation, the Schwarz inequality for its trace
adjoint, and a positive-definite fixed point from a faithful fixed family.

This is the change-of-coordinates step used before applying the fixed-point
classification of Wolf, Theorem 6.14, in arXiv:1606.00608, Appendix C.4,
lines 1980--1995. -/
theorem IsPositiveDirectSumMap.reindexedExtension_properties
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsPositiveDirectSumMap T)
    (hTP : IsTracePreservingDirectSumMap T)
    (hSchwarz : IsSchwarzDirectSumMap (Matrix.directSumTraceAdjointMap T))
    {ρ : ∀ k, Matrix (n k) (n k) ℂ} (hρ : ∀ k, (ρ k).PosDef)
    (hρfix : T ρ = ρ)
    {β : Type*} [Fintype β]
    (e : ((k : ι) × n k) ≃ β) :
    IsPositiveMap (reindexEndomorphism e (directSumExtension T)) ∧
      IsTracePreservingMap (reindexEndomorphism e (directSumExtension T)) ∧
      IsSchwarzMap
          (traceAdjointMap (reindexEndomorphism e (directSumExtension T))) ∧
        (Matrix.reindex e e (directSumDiagonalEmbedding ρ)).PosDef ∧
        reindexEndomorphism e (directSumExtension T)
            (Matrix.reindex e e (directSumDiagonalEmbedding ρ)) =
          Matrix.reindex e e (directSumDiagonalEmbedding ρ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsPositiveMap.reindexEndomorphism
      hT.directSumExtension_isPositiveMap e
  · exact IsTracePreservingMap.reindexEndomorphism
      hTP.directSumExtension_isTracePreservingMap e
  · rw [traceAdjointMap_reindexEndomorphism]
    exact IsSchwarzMap.reindexEndomorphism
      (hSchwarz.traceAdjointMap_directSumExtension_isSchwarzMap hT) e
  · exact (directSumDiagonalEmbedding_posDef hρ).reindex e
  · let Φ := Matrix.reindexLinearEquiv ℂ ℂ e e
    change Φ (directSumExtension T (Φ.symm (Φ
      (directSumDiagonalEmbedding ρ)))) = Φ (directSumDiagonalEmbedding ρ)
    rw [Φ.symm_apply_apply]
    exact congrArg Φ ((directSumExtension_embedding_eq_self_iff T ρ).2 hρfix)

/-- **Density-block form for fixed points on a finite direct sum.**

Let `T` be a positive map of a finite sum of full matrix algebras that
preserves the total trace. If the direct-sum trace adjoint satisfies the
Schwarz inequality and `T` has a positive-definite fixed family, then its
fixed points have the density-block form obtained from Wolf's Theorem 6.14.

This is the finite-index classification step used in arXiv:1606.00608,
Appendix C.4, lines 1980--1995. The hypotheses for the particular sector map
in that argument are not asserted here.

**Scope restriction (full support):** The fixed family is positive definite on
every summand. The maximal-support reduction and complementary zero summand
for a full matrix algebra are completed in
`QICLean.Channel.FixedPoint.DensityBlock.FixedPointDensityBlocks`; the present direct-sum theorem
retains its explicit full-support hypothesis. See
`docs/paper-gaps/wolf_theorem6_14_fixed_point_projection_gap.tex`. -/
theorem IsPositiveDirectSumMap.exists_block_densities_of_fixedPoints
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsPositiveDirectSumMap T)
    (hTP : IsTracePreservingDirectSumMap T)
    (hSchwarz : IsSchwarzDirectSumMap (Matrix.directSumTraceAdjointMap T))
    {ρ : ∀ k, Matrix (n k) (n k) ℂ} (hρ : ∀ k, (ρ k).PosDef)
    (hρfix : T ρ = ρ) :
    ∃ (K : ℕ) (d m : Fin K → ℕ)
      (e : ((k : Fin K) × (Fin (m k) × Fin (d k))) ≃ ((k : ι) × n k))
      (U : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ)
      (σ : ∀ k, Matrix (Fin (m k)) (Fin (m k)) ℂ),
      U ∈ Matrix.unitaryGroup ((k : ι) × n k) ℂ ∧
        (∀ k, 0 < d k) ∧ (∀ k, 0 < m k) ∧
        (∀ k, (σ k).PosSemidef) ∧ (∀ k, (σ k).trace = 1) ∧
        ∀ A, T A = A ↔
          ∃ X : ∀ k, Matrix (Fin (d k)) (Fin (d k)) ℂ,
            star U * directSumDiagonalEmbedding A * U =
              Matrix.reindex e e
                (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
  let s := (k : ι) × n k
  let efin : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let TExt := directSumExtension T
  let TFin := reindexEndomorphism efin TExt
  let ρExt := directSumDiagonalEmbedding ρ
  let ρFin := Matrix.reindex efin efin ρExt
  obtain ⟨hTFin, hTPFin, hSchwarzFin, hρFin, hρFinFix⟩ :
      IsPositiveMap TFin ∧ IsTracePreservingMap TFin ∧
        IsSchwarzMap (Matrix.traceAdjointMap TFin) ∧
        ρFin.PosDef ∧ TFin ρFin = ρFin := by
    simpa only [ρFin, ρExt, TFin, TExt] using
      hT.reindexedExtension_properties hTP hSchwarz hρ hρfix efin
  obtain ⟨K, d, m, eClass, UFin, σ, hUFin, hd, hm, hσpos, hσtrace,
      _, hfixed⟩ :=
    hTFin.exists_block_densities_of_meanErgodicProjection
      hTPFin hSchwarzFin hρFin hρFinFix
  let U := Matrix.reindex efin.symm efin.symm UFin
  let e := eClass.trans efin.symm
  have hU : U ∈ Matrix.unitaryGroup s ℂ := by
    rw [Matrix.mem_unitaryGroup_iff'] at hUFin ⊢
    have hstar : star U = Matrix.reindex efin.symm efin.symm (star UFin) := by
      simp only [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
    rw [hstar]
    have hmul : Matrix.reindex efin.symm efin.symm (star UFin) *
        Matrix.reindex efin.symm efin.symm UFin =
        Matrix.reindex efin.symm efin.symm (star UFin * UFin) := by
      exact Matrix.reindexLinearEquiv_mul ℂ ℂ
        efin.symm efin.symm efin.symm _ _
    rw [hmul, hUFin]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · have heij : efin i ≠ efin j := fun h ↦ hij (efin.injective h)
      simp [hij, heij]
  refine ⟨K, d, m, e, U, σ, hU, hd, hm, hσpos, hσtrace, ?_⟩
  intro A
  rw [← directSumExtension_embedding_eq_self_iff T A]
  have hcoord : TExt (directSumDiagonalEmbedding A) =
        directSumDiagonalEmbedding A ↔
      TFin (Matrix.reindex efin efin (directSumDiagonalEmbedding A)) =
        Matrix.reindex efin efin (directSumDiagonalEmbedding A) := by
    let Φ := Matrix.reindexLinearEquiv ℂ ℂ efin efin
    change TExt (directSumDiagonalEmbedding A) = directSumDiagonalEmbedding A ↔
      Φ (TExt (Φ.symm (Φ (directSumDiagonalEmbedding A)))) =
        Φ (directSumDiagonalEmbedding A)
    rw [Φ.symm_apply_apply]
    exact Φ.injective.eq_iff.symm
  rw [hcoord, hfixed]
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    calc
      star U * directSumDiagonalEmbedding A * U =
          Matrix.reindex efin.symm efin.symm
            (star UFin * Matrix.reindex efin efin
              (directSumDiagonalEmbedding A) * UFin) := by
        dsimp only [U]
        rw [reindex_conjugation]
        rw [reindex_symm_reindex]
      _ = Matrix.reindex efin.symm efin.symm
          (Matrix.reindex eClass eClass
            (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)) := by rw [hX]
      _ = Matrix.reindex e e
          (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
        exact reindex_reindex eClass efin.symm _
  · rintro ⟨X, hX⟩
    refine ⟨X, ?_⟩
    have hUback : Matrix.reindex efin efin U = UFin := by
      dsimp only [U]
      simpa only [Equiv.symm_symm] using
        reindex_symm_reindex efin.symm UFin
    calc
      star UFin * Matrix.reindex efin efin
          (directSumDiagonalEmbedding A) * UFin =
          Matrix.reindex efin efin
            (star U * directSumDiagonalEmbedding A * U) := by
        rw [reindex_conjugation]
        rw [hUback]
      _ = Matrix.reindex efin efin
          (Matrix.reindex e e
            (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k)) := by rw [hX]
      _ = Matrix.reindex eClass eClass
          (Matrix.blockDiagonal' fun k ↦ σ k ⊗ₖ X k) := by
        rw [reindex_reindex]
        congr 1
        ext x
        simp [e]

end Matrix
