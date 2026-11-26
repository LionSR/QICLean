/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.RegionUnion
import QICLean.ManyBody.Sites.RegionMatrix
import QICLean.Algebra.Matrix.MatrixTracePairing
import QICLean.Entropy.VonNeumann.Entropy
import QICLean.Analysis.TraceNorm.TraceDistance
import QICLean.Analysis.Norm.MatrixToEuclidean
import QICLean.Channel.Schmidt.SurprisalMoment
import QICLean.Spectral.Projection.ShiftedDensityTruncation

/-!
# Regional pure states and expectations

The regional state is the unnormalized partial trace of the outer product of a vector.
Expectations of placed matrices are its trace pairings. The statements allow arbitrary
finite basis types, empty bases and unnormalized vectors. The supported-operator trace
argument needs no reference configuration. A unitary supported away from a region leaves
the regional state unchanged, and the regional state is the regional matrix
`ManyBody.regionMatrix` of the projection onto the vector.

The definitions and proofs generalize `Entropy.LocalLift`; the dimension-indexed API
is retained there as a specialization.

Moved from TNLean, `TNLean/MPS/Tensor/VaryingBond/SequentialTruncation.lean` at commit `021ba0bd19`
(Apache-2.0).
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

/-- The regional state `ρ_{φ,D} = Tr_{Dᶜ} |φ⟩⟨φ|`: the regional matrix of the projection onto
`φ`. -/
noncomputable def regionState (φ : EuclideanSpace ℂ (Config X)) (D : Finset V) :
    Matrix (RegionConfig X D) (RegionConfig X D) ℂ :=
  regionMatrix (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) D

/-- The regional state in the coordinates of the cut along `D`: the partial trace of the outer
product of the cut vector. -/
theorem regionState_eq_partialTraceRight_cutVector (D : Finset V)
    (φ : EuclideanSpace ℂ (Config X)) :
    regionState φ D = partialTraceRight
      (vecMulVec (WithLp.ofLp (cutVector D φ)) (star (WithLp.ofLp (cutVector D φ)))) := by
  rfl

/-- Regional pure-state matrices are positive semidefinite. -/
theorem regionState_posSemidef (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    (regionState φ D).PosSemidef :=
  regionMatrix_posSemidef X (posSemidef_vecMulVec_self_star _) D

/-- Regional pure-state matrices are Hermitian. -/
theorem regionState_isHermitian (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    (regionState φ D).IsHermitian :=
  (regionState_posSemidef D φ).isHermitian

/-- The trace of a regional state is the squared norm of the original vector. -/
theorem trace_regionState (D : Finset V) (φ : EuclideanSpace ℂ (Config X)) :
    (regionState φ D).trace = ((‖φ‖ ^ 2 : ℝ) : ℂ) := by
  rw [regionState, trace_regionMatrix, trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K]
  simp

/-- A unit vector has regional states of unit trace. -/
theorem trace_regionState_eq_one {D : Finset V} {φ : EuclideanSpace ℂ (Config X)}
    (hφ : ‖φ‖ = 1) : (regionState φ D).trace = 1 := by
  rw [trace_regionState, hφ]
  simp

variable [∀ v, DecidableEq (X v)]

/-- The entropy `S_Ω(D)` of the regional state of `Ω` on `D`. -/
noncomputable def regionEntropy (Ω : EuclideanSpace ℂ (Config X)) (D : Finset V) : ℝ :=
  vonNeumannEntropy (regionState Ω D) (regionState_isHermitian D Ω)

variable {D : Finset V}

/-- **Expectations of lifted operators.** `⟨φ, lift_D K φ⟩ = Tr (ρ_{φ,D} K)`. -/
theorem inner_place (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ)
    (φ : EuclideanSpace ℂ (Config X)) :
    ⟪φ, toEuclideanLin (place D K) φ⟫_ℂ = (regionState φ D * K).trace := by
  rw [inner_toEuclideanLin_eq_trace, regionState_eq_partialTraceRight_cutVector,
    trace_partialTraceRight_mul]
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
    ((regionState Ω D).submatrix f.symm f.symm * K).trace =
      ⟪Ω, toEuclideanLin (place D (K.submatrix f f)) Ω⟫_ℂ := by
  rw [inner_place]
  have : (regionState Ω D).submatrix f.symm f.symm * K =
      (regionState Ω D * K.submatrix f f).submatrix f.symm f.symm := by
    rw [← submatrix_mul_equiv _ _ _ f.symm, submatrix_submatrix]
    simp
  rw [this, trace_submatrix_equiv]

omit [∀ v, DecidableEq (X v)] in
/-- The `B` marginal of the `B ∪ C` state. -/
theorem partialTraceRight_regionState_union {B C : Finset V} (hBC : Disjoint B C)
    (Ω : EuclideanSpace ℂ (Config X)) :
    partialTraceRight ((regionState Ω (B ∪ C)).submatrix (regionUnionEquiv hBC).symm
      (regionUnionEquiv hBC).symm) = regionState Ω B := by
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
    (hcomm : K * regionState φ D = regionState φ D * K)
    (A : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    ⟪φ, toEuclideanLin (place D K * place D A * place D K⁻¹) φ⟫_ℂ =
      ⟪φ, toEuclideanLin (place D A) φ⟫_ℂ := by
  obtain rfl : ‹Fintype (RegionConfig X D)› = Pi.instFintype := Subsingleton.elim _ _
  obtain rfl : ‹DecidableEq (RegionConfig X D)› = Fintype.decidablePiFintype :=
    Subsingleton.elim _ _
  rw [← place_mul, ← place_mul, inner_place, inner_place]
  have h1 : K⁻¹ * regionState φ D * K = regionState φ D := by
    rw [Matrix.mul_assoc, ← hcomm, ← Matrix.mul_assoc, nonsing_inv_mul _ hK, Matrix.one_mul]
  calc (regionState φ D * (K * A * K⁻¹)).trace
      = (K⁻¹ * regionState φ D * K * A).trace := by
        rw [show K⁻¹ * regionState φ D * K * A = K⁻¹ * (regionState φ D * K * A) by
          simp only [Matrix.mul_assoc], trace_mul_comm K⁻¹]
        simp only [Matrix.mul_assoc]
    _ = (regionState φ D * A).trace := by rw [h1]

/-- The trace argument for an arbitrary operator supported on `D`. -/
theorem inner_conj_eq_of_mem_supportedOperators [Fintype (RegionConfig X D)]
    [DecidableEq (RegionConfig X D)] {K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ}
    (hK : IsUnit K.det) {φ : EuclideanSpace ℂ (Config X)}
    (hcomm : K * regionState φ D = regionState φ D * K)
    {Y : Matrix (Config X) (Config X) ℂ} (hY : Y ∈ supportedOperators X D) :
    ⟪φ, toEuclideanLin (place D K * Y * place D K⁻¹) φ⟫_ℂ =
      ⟪φ, toEuclideanLin Y φ⟫_ℂ := by
  obtain rfl : ‹Fintype (RegionConfig X D)› = Pi.instFintype := Subsingleton.elim _ _
  obtain rfl : ‹DecidableEq (RegionConfig X D)› = Fintype.decidablePiFintype :=
    Subsingleton.elim _ _
  obtain ⟨A, rfl⟩ := exists_eq_place_of_mem_supportedOperators hY
  exact inner_place_conj_eq hK hcomm A

/-- **A unitary away from a region leaves the regional state unchanged.** If `U` is unitary and
supported on a region `S` disjoint from `D`, then `ρ_{Uφ,D} = ρ_{φ,D}` for every vector `φ`,
which may be entangled across the cut. Two-dimensional area law, `09-amplification.tex`,
lines 547–550. -/
theorem regionState_toEuclideanLin_of_mem_supportedOperators {S : Finset V}
    (hSD : Disjoint S D) {U : Matrix (Config X) (Config X) ℂ}
    (hU : U ∈ supportedOperators X S) (hUu : Uᴴ * U = 1) (φ : EuclideanSpace ℂ (Config X)) :
    regionState (toEuclideanLin U φ) D = regionState φ D := by
  have hmul (A B : Matrix (Config X) (Config X) ℂ) (x : EuclideanSpace ℂ (Config X)) :
      toEuclideanLin A (toEuclideanLin B x) = toEuclideanLin (A * B) x := by
    simp [toLpLin_apply, mulVec_mulVec]
  refine eq_of_forall_trace_mul_eq fun N ↦ ?_
  have hc := commute_of_mem_supportedOperators_of_disjoint hU
    (place_mem_supportedOperators (D := D) N) hSD
  rw [← inner_place, ← inner_place, ← LinearMap.adjoint_inner_right,
    ← toEuclideanLin_conjTranspose_eq_adjoint, hmul, hmul, Matrix.mul_assoc, ← hc.eq,
    ← Matrix.mul_assoc, hUu, Matrix.one_mul]

end ManyBody

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- Expectations can be computed in cut coordinates. -/
theorem inner_cutOperator (B : Finset V) (Y : Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ)
    (φ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ⟪ManyBody.cutVector B φ, toEuclideanLin (ManyBody.cutOperator B Y) (ManyBody.cutVector B φ)⟫_ℂ =
      ⟪φ, toEuclideanLin Y φ⟫_ℂ := by
  rw [Matrix.inner_toEuclideanLin_eq_trace, Matrix.inner_toEuclideanLin_eq_trace]
  have hv : vecMulVec (WithLp.ofLp (ManyBody.cutVector B φ))
      (star (WithLp.ofLp (ManyBody.cutVector B φ))) =
      (vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))).submatrix
          (ManyBody.cutEquiv (fun v ↦ Fin (n v)) B).symm
        (ManyBody.cutEquiv (fun v ↦ Fin (n v)) B).symm := by
    ext a b; simp [vecMulVec_apply]
  rw [hv, ManyBody.cutOperator, reindex_apply, submatrix_mul_equiv, trace_submatrix_equiv]

end Entropy

section

open ManyBody (interval interval_mono)

section SequentialTruncation

open Matrix

open scoped ComplexOrder InnerProductSpace Kronecker

open ManyBody (cutMatrix)

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- A lift from a smaller region is a lift from any larger region. -/
theorem exists_localLift_eq_localLift_of_subset {D D' : Finset V} (hDD : D ⊆ D')
    (K : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ) :
    ∃ K' : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D')
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D') ℂ,
      ManyBody.place D K = ManyBody.place D' K' := by
  rcases isEmpty_or_nonempty (∀ v, Fin (n v)) with _ | ⟨⟨σ₀⟩⟩
  · exact ⟨0, Subsingleton.elim _ _⟩
  · exact ManyBody.exists_eq_place_of_mem_supportedOperators
      ((ManyBody.place_mem_supportedOperators K).mono hDD)

omit [Fintype V] in
private theorem conjTranspose_mul_self_of_isStarProjection {D : Finset V}
    {P : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ} (hP : IsStarProjection P) :
    Pᴴ * P = P := by
  have h := hP.isSelfAdjoint.star_eq
  rw [star_eq_conjTranspose] at h
  rw [h, hP.isIdempotentElem.eq]

/-- The squared norm of a lifted star projection applied to a vector is the trace of the
projection against the regional state. -/
theorem norm_sq_toEuclideanLin_localLift_eq_trace {D : Finset V}
    {P : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ} (hP : IsStarProjection P)
    (ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ‖toEuclideanLin (ManyBody.place D P) ψ‖ ^ 2 = (P * ManyBody.regionState ψ D).trace.re := by
  have hPP := conjTranspose_mul_self_of_isStarProjection hP
  have hinner : ⟪toEuclideanLin (ManyBody.place D P) ψ, toEuclideanLin (ManyBody.place D P) ψ⟫_ℂ =
      ⟪ψ, toEuclideanLin (ManyBody.place D P) ψ⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← toEuclideanLin_mul_apply, ← ManyBody.place_conjTranspose, ← ManyBody.place_mul, hPP]
  rw [ManyBody.inner_place, trace_mul_comm] at hinner
  rw [← hinner]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm

/-- A lifted star projection is a contraction. -/
theorem norm_toEuclideanLin_localLift_le {D : Finset V}
    {P : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ} (hP : IsStarProjection P)
    (ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ‖toEuclideanLin (ManyBody.place D P) ψ‖ ≤ ‖ψ‖ := by
  have hPP := conjTranspose_mul_self_of_isStarProjection hP
  set v := toEuclideanLin (ManyBody.place D P) ψ
  have hinner : ⟪v, v⟫_ℂ = ⟪ψ, v⟫_ℂ := by
    simp only [v]
    rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint,
      ← toEuclideanLin_mul_apply, ← ManyBody.place_conjTranspose, ← ManyBody.place_mul, hPP]
  have h1 : ‖v‖ ^ 2 ≤ ‖ψ‖ * ‖v‖ := by
    have h : ‖v‖ ^ 2 = (⟪ψ, v⟫_ℂ).re := by
      rw [← hinner]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
    rw [h]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg v).eq_or_lt with hv | hv
  · rw [← hv]; exact norm_nonneg ψ
  · nlinarith

end Entropy

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- The spectral mass of a positive semidefinite matrix strictly below the threshold
`exp (-(S + w))` is at most the two-sided surprisal tail of its spectrum at centre `S` and
slack `w`: an eigenvalue below the threshold has surprisal above `S + w`. -/
theorem PosSemidef.trace_complement_spectralProjectionGE_le_surprisalTail (hρ : ρ.PosSemidef)
    (S w : ℝ) :
    ((1 - spectralProjectionGE ρ (Real.exp (-(S + w)))) * ρ).trace.re ≤
      Entropy.surprisalTail hρ.isHermitian.eigenvalues S w := by
  rw [hρ.isHermitian.trace_complement_spectralProjectionGE, Entropy.surprisalTail]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hi0 := hρ.eigenvalues_nonneg i
  split_ifs with h1 h2 h2
  · exact hi0
  · exact le_rfl
  · exact le_rfl
  · rcases hi0.eq_or_lt with hz | hp
    · exact hz ▸ le_rfl
    · exfalso
      apply h2
      have hlog : Real.log (hρ.isHermitian.eigenvalues i) < -(S + w) := by
        rw [← Real.log_exp (-(S + w))]
        exact Real.log_lt_log hp (lt_of_not_ge h1)
      exact lt_of_lt_of_le (by linarith) (le_abs_self _)

/-- The rank of the spectral projection of a density matrix above `exp (-(S + w))` is at
most `exp (S + w)`. -/
theorem PosSemidef.rank_spectralProjectionGE_exp_le (hρ : ρ.PosSemidef) (hρ1 : ρ.trace = 1)
    (S w : ℝ) :
    ((spectralProjectionGE ρ (Real.exp (-(S + w)))).rank : ℝ) ≤ Real.exp (S + w) := by
  have hrank := hρ.mul_rank_spectralProjectionGE_le_trace (Real.exp (-(S + w)))
  rw [hρ1, Complex.one_re] at hrank
  have h : ((spectralProjectionGE ρ (Real.exp (-(S + w)))).rank : ℝ) ≤
      1 / Real.exp (-(S + w)) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    simpa only [mul_comm] using hrank
  refine h.trans (le_of_eq ?_)
  rw [one_div, Real.exp_neg, inv_inv]

end Matrix

end SequentialTruncation

end
