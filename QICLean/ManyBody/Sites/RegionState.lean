/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.RegionUnion
import QICLean.Algebra.PureStateExpectation
import QICLean.Analysis.Entropy
import QICLean.Analysis.TraceDistance

/-!
# Regional pure states and expectations

The regional state is the unnormalized partial trace of the outer product of a vector.
Expectations of placed matrices are its trace pairings. The statements allow arbitrary
finite basis types, empty bases and unnormalized vectors. The supported-operator trace
argument needs no reference configuration.

The definitions and proofs generalize `Entropy.LocalLift`; the dimension-indexed API
is retained there as a specialization.
-/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder Kronecker

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : V → Type*} [∀ v, Fintype (X v)]

/-- A vector expressed in the coordinates of a regional cut. -/
noncomputable abbrev cutVector (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    EuclideanSpace ℂ (RegionConfig X D × ComplConfig X D) :=
  WithLp.toLp 2 fun x ↦ φ ((cutEquiv X D).symm x)

/-- Cutting a vector preserves its Euclidean norm. -/
@[simp] theorem norm_cutVector (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    ‖cutVector D φ‖ = ‖φ‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv X D)).norm_map φ

/-- The regional state `ρ_{φ,D} = Tr_{Dᶜ} |φ⟩⟨φ|`. -/
noncomputable def regionState (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    Matrix (RegionConfig X D) (RegionConfig X D) ℂ :=
  partialTraceRight (vecMulVec (WithLp.ofLp (cutVector D φ)) (star (WithLp.ofLp (cutVector D φ))))

/-- Regional pure-state matrices are positive semidefinite. -/
theorem regionState_posSemidef (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    (regionState D φ).PosSemidef :=
  (posSemidef_vecMulVec_self_star _).partialTraceRight

/-- Regional pure-state matrices are Hermitian. -/
theorem regionState_isHermitian (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    (regionState D φ).IsHermitian :=
  (regionState_posSemidef D φ).isHermitian

/-- The trace of a regional state is the squared norm of the original vector. -/
theorem trace_regionState (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    (regionState D φ).trace = ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
  rw [regionState, trace_partialTraceRight, trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, norm_cutVector]
  simp

variable [∀ v, DecidableEq (X v)]

/-- The entropy `S_Ω(D)` of the regional state of `Ω` on `D`. -/
noncomputable def regionEntropy (D : Finset V) (Ω : EuclideanSpace ℂ (Config X)) : ℝ :=
  vonNeumannEntropy (regionState D Ω) (regionState_isHermitian D Ω)

variable {D : Finset V}

/-- **Expectations of lifted operators.** `⟨φ, lift_D K φ⟩ = Tr (ρ_{φ,D} K)`. -/
theorem inner_place (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ)
    (φ : EuclideanSpace ℂ (Config X)) :
    ⟪φ, toEuclideanLin (place D K) φ⟫_ℂ = (regionState D φ * K).trace := by
  rw [inner_toEuclideanLin_eq_trace, regionState, trace_partialTraceRight_mul]
  have hv : vecMulVec (WithLp.ofLp (cutVector D φ)) (star (WithLp.ofLp (cutVector D φ))) =
      (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))).submatrix (cutEquiv X D).symm
        (cutEquiv X D).symm := by
    ext a b; simp [vecMulVec_apply]
  rw [hv, place, reindex_apply, Equiv.symm_symm,
    ← trace_submatrix_equiv (cutEquiv X D).symm,
    ← submatrix_mul_equiv _ _ _ (cutEquiv X D).symm]
  simp

/-- Expectations of reindexed regional states. -/
theorem trace_regionState_submatrix_mul {D : Finset V} {κ : Type*} [Fintype κ]
    (f : RegionConfig X D ≃ κ) (Ω : EuclideanSpace ℂ (Config X)) (K : Matrix κ κ ℂ) :
    ((regionState D Ω).submatrix f.symm f.symm * K).trace =
      ⟪Ω, toEuclideanLin (place D (K.submatrix f f)) Ω⟫_ℂ := by
  rw [inner_place]
  have : (regionState D Ω).submatrix f.symm f.symm * K =
      (regionState D Ω * K.submatrix f f).submatrix f.symm f.symm := by
    rw [← submatrix_mul_equiv _ _ _ f.symm, submatrix_submatrix]
    simp
  rw [this, trace_submatrix_equiv]

omit [∀ v, DecidableEq (X v)] in
/-- The `B` marginal of the `B ∪ C` state. -/
theorem partialTraceRight_regionState_union {B C : Finset V} (hBC : Disjoint B C)
    (Ω : EuclideanSpace ℂ (Config X)) :
    partialTraceRight ((regionState (B ∪ C) Ω).submatrix (regionUnionEquiv hBC).symm
      (regionUnionEquiv hBC).symm) = regionState B Ω := by
  classical
  refine eq_of_forall_trace_mul_eq fun N ↦ ?_
  rw [trace_partialTraceRight_mul, trace_regionState_submatrix_mul, ← inner_place]
  have h : (N ⊗ₖ (1 : Matrix (RegionConfig X C) (RegionConfig X C) ℂ)).submatrix
      (regionUnionEquiv hBC) (regionUnionEquiv hBC) =
      reindex (regionUnionEquiv hBC).symm (regionUnionEquiv hBC).symm
        (N ⊗ₖ (1 : Matrix (RegionConfig X C) (RegionConfig X C) ℂ)) := by
    rw [reindex_apply, Equiv.symm_symm]
  rw [h, place_union_kronecker, place_one, Matrix.mul_one]

/-- **The trace argument.** If `K` is invertible and commutes with the regional state
`ρ_{φ,D}`, then conjugating a lifted observable by the lift of `K` does not change its
expectation in `φ`.
Area-law manuscript, proof of Lemma 3.2, `02-initial.tex`, lines 368–372. -/
theorem inner_place_conj_eq [Fintype (RegionConfig X D)]
    [DecidableEq (RegionConfig X D)] {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ}
    (hK : IsUnit K.det) {φ : EuclideanSpace ℂ (Config X)}
    (hcomm : K * regionState D φ = regionState D φ * K)
    (A : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    ⟪φ, toEuclideanLin (place D K * place D A * place D K⁻¹) φ⟫_ℂ =
      ⟪φ, toEuclideanLin (place D A) φ⟫_ℂ := by
  obtain rfl : ‹Fintype (RegionConfig X D)› = Pi.instFintype := Subsingleton.elim _ _
  obtain rfl : ‹DecidableEq (RegionConfig X D)› = Fintype.decidablePiFintype :=
    Subsingleton.elim _ _
  rw [← place_mul, ← place_mul, inner_place, inner_place]
  have h1 : K⁻¹ * regionState D φ * K = regionState D φ := by
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, nonsing_inv_mul _ hK, Matrix.one_mul]
  calc (regionState D φ * (K * A * K⁻¹)).trace
      = (K⁻¹ * regionState D φ * K * A).trace := by
        rw [show K⁻¹ * regionState D φ * K * A = K⁻¹ * (regionState D φ * K * A) by
          simp only [Matrix.mul_assoc], trace_mul_comm K⁻¹]
        simp only [Matrix.mul_assoc]
    _ = (regionState D φ * A).trace := by rw [h1]

/-- The trace argument for an arbitrary operator supported on `D`. -/
theorem inner_conj_eq_of_mem_supportedOperators [Fintype (RegionConfig X D)]
    [DecidableEq (RegionConfig X D)] {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ}
    (hK : IsUnit K.det) {φ : EuclideanSpace ℂ (Config X)}
    (hcomm : K * regionState D φ = regionState D φ * K)
    {Y : Matrix (Config X) (Config X) ℂ} (hY : Y ∈ supportedOperators X D) :
    ⟪φ, toEuclideanLin (place D K * Y * place D K⁻¹) φ⟫_ℂ =
      ⟪φ, toEuclideanLin Y φ⟫_ℂ := by
  obtain rfl : ‹Fintype (RegionConfig X D)› = Pi.instFintype := Subsingleton.elim _ _
  obtain rfl : ‹DecidableEq (RegionConfig X D)› = Fintype.decidablePiFintype :=
    Subsingleton.elim _ _
  obtain ⟨A, rfl⟩ := exists_eq_place_of_mem_supportedOperators hY
  exact inner_place_conj_eq hK hcomm A

end ManyBody
