/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.VonNeumann.VonNeumannEntropySpectralTail
import QICLean.ManyBody.Entropy.Filter.SchmidtPinning
import QICLean.Entropy.Conditional.ConditionalEntropy
import QICLean.Entropy.VonNeumann.Bipartite
import QICLean.Entropy.StrongSubadditivity.Basic
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.Relabel
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Hamiltonian.KroneckerSum
import QICLean.ManyBody.Hamiltonian.Models

/-!
# Entropies of regions and strong subadditivity

Regional entropy is the von Neumann entropy of the regional state of a pure state.
Complementary regions have equal entropy, and disjoint regions obey subadditivity for normalized
states. Regional mutual information is identified with the bipartite matrix definition after
finite reindexing. The regional states of a vector on nested regions are partial traces of one
    another. For
pairwise disjoint regions `A, B, C`, strong subadditivity therefore holds for the regional
entropies: `S(A ∪ B ∪ C) + S(B) ≤ S(A ∪ B) + S(B ∪ C)`. In particular conditioning on a larger
region decreases the conditional entropy: `S(X | T) ≤ S(X | T')` for `T' ⊆ T` disjoint from `X`,
where `S(X | T) = S(X ∪ T) - S(T)`.

## Main results

* `ManyBody.regionEntropy_compl`, `ManyBody.regionEntropy_union_le`: complementary regions and
  subadditivity.
* `ManyBody.regionMutualInformation`, `ManyBody.regionMutualInformation_eq_matrix`: regional
  mutual information.
* `Entropy.regionEntropy_ssa`: strong subadditivity for regions.
* `Entropy.regionEntropy_cond_anti`: conditioning on a larger region.
* `ManyBody.auxiliaryPair_regionEntropyIdentity`, `ManyBody.auxiliaryPair_pre_nonneg`: the entropy
  cancellation in the auxiliary-pair comparison.
* `ManyBody.regionMutualInformation_relabel`: regional mutual information under bijections of tensor
  factors.
* `ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint`: zero entropy across a cut
  that splits no term.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap* (2026),
  Lemma 11.1 (`geometry:cancellation`): complementary regions, subadditivity and mutual
  information. These proofs are independently written from the paper's entropy argument.
* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 3.2
  (`lem:initial-buffer`), `02-initial.tex`, lines 559–568: strong subadditivity for the
  nested regions `T_j`.

Independently written from the manuscript; no upstream Lean proof text is reused.

Moved from TNLean, `TNLean/MPS/AreaLaw/Entropy/LogarithmicAreaLaw.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

section RegionEntropy

open scoped BigOperators Matrix ComplexOrder

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

omit [∀ v, DecidableEq (β v)] in
/-- Reducing to the complement `Rᶜ` is the left marginal in the cut along `R`, with the
configurations outside `R` read as configurations of `Rᶜ`. -/
theorem regionState_compl_eq_partialTraceLeft
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (R : Finset V) :
    regionState ψ Rᶜ = (Matrix.partialTraceLeft
      (Matrix.vecMulVec (fun x ↦ ψ ((cutEquiv β R).symm x))
        (star (fun x ↦ ψ ((cutEquiv β R).symm x))))).reindex
      (complementEquiv β R) (complementEquiv β R) := by
  let e := (complementEquiv β Rᶜ).trans (configurationCongr β (compl_compl R))
  have hcut (x : RegionConfig β Rᶜ) (c : ComplConfig β Rᶜ) :
      (cutEquiv β Rᶜ).symm (x, c) =
        (cutEquiv β R).symm (e c, (complementEquiv β R).symm x) := by
    funext v
    by_cases hv : v ∈ R
    · rw [cutEquiv_symm_apply_not_mem _ _ (Finset.notMem_compl.mpr hv),
        cutEquiv_symm_apply_mem _ _ hv]
      simp [e, configurationCongr_apply, complementEquiv]
    · rw [cutEquiv_symm_apply_mem _ _ (Finset.mem_compl.mpr hv),
        cutEquiv_symm_apply_not_mem _ _ hv]
      rfl
  ext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, regionState,
    regionMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    Matrix.partialTraceLeft_apply, hcut]
  exact e.sum_comp (fun c ↦ ψ ((cutEquiv β R).symm (c, _)) *
    star (ψ ((cutEquiv β R).symm (c, _))))

/-- Complementary regional entropies of a pure state are equal, without any
normalization or invertibility assumption. -/
@[simp]
theorem regionEntropy_compl (ψ : EuclideanSpace ℂ ((v : V) → β v)) (R : Finset V) :
    regionEntropy ψ Rᶜ = regionEntropy ψ R := by
  unfold regionEntropy
  rw [vonNeumannEntropy_congr ((regionState_compl_eq_partialTraceLeft β ψ R).trans
      (Matrix.reindex_apply _ _ _)) _ ((Matrix.isHermitian_submatrix_equiv _).mpr
        (Matrix.posSemidef_vecMulVec_self_star _).partialTraceLeft.isHermitian),
    vonNeumannEntropy_submatrix_equiv,
    vonNeumannEntropy_congr (regionState_eq_partialTraceRight_cutVector R ψ)]
  exact (Entropy.pure_marginal_entropy_eq _).symm

/-- The empty region has zero entropy for a normalized state. -/
@[simp]
theorem regionEntropy_empty (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) :
    regionEntropy ψ ∅ = 0 := by
  apply vonNeumannEntropy_eq_zero_of_rank_le_one
    (regionState_posSemidef ∅ ψ) (trace_regionState_eq_one hψ (D := ∅))
  calc
    (regionState ψ ∅).rank ≤ Fintype.card (RegionConfig β ∅) :=
      Matrix.rank_le_card_width _
    _ = 1 := by simp [RegionConfig]

/-- The full finite system is pure, so its entropy is zero when normalized. -/
@[simp]
theorem regionEntropy_univ (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) :
    regionEntropy ψ Finset.univ = 0 := by
  simpa only [Finset.compl_empty] using (regionEntropy_compl β ψ ∅).trans
      (regionEntropy_empty β ψ hψ)

/-- Subadditivity for two disjoint regions of a normalized pure state. -/
theorem regionEntropy_union_le (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (R T : Finset V) (h : Disjoint R T) :
    regionEntropy ψ (R ∪ T) ≤ regionEntropy ψ R + regionEntropy ψ T := by
  let e := (regionUnionEquiv (β := β) h).symm
  let ρ := (regionState ψ (R ∪ T)).submatrix e e
  have hρ : ρ.PosSemidef := (regionState_posSemidef (R ∪ T) ψ).submatrix e
  have htr : ρ.trace = 1 := by
    rw [Matrix.trace_submatrix_equiv]
    exact trace_regionState_eq_one hψ (D := (R ∪ T))
  have hR : Matrix.partialTraceRight ρ = regionState ψ R :=
    partialTraceRight_regionMatrix_union β _ R T h
  have hT : Matrix.partialTraceLeft ρ = regionState ψ T :=
    partialTraceLeft_regionMatrix_union β _ R T h
  have hsub := Entropy.subadditivity ρ hρ htr
  rw [vonNeumannEntropy_congr hR _ (regionState_posSemidef R ψ).isHermitian,
    vonNeumannEntropy_congr hT _ (regionState_posSemidef T ψ).isHermitian] at hsub
  dsimp only [ρ] at hsub
  rw [vonNeumannEntropy_submatrix_equiv e _
    (regionState_posSemidef (R ∪ T) ψ).isHermitian] at hsub
  exact hsub

/-- Regional quantum mutual information. For disjoint regions its equality with
canonical matrix mutual information is `ManyBody.regionMutualInformation_eq_matrix`. -/
noncomputable def regionMutualInformation {β : V → Type*} [∀ v, Fintype (β v)]
    [∀ v, DecidableEq (β v)] (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (R T : Finset V) : ℝ :=
  regionEntropy ψ R + regionEntropy ψ T - regionEntropy ψ (R ∪ T)

/-- The actual joint density matrix of two disjoint regions, expressed in the
finite bases used by the canonical quantum mutual information. -/
noncomputable def jointMatrix (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (R T : Finset V) (h : Disjoint R T) :
    Matrix
        (Fin (Fintype.card (RegionConfig β R)) × Fin
        (Fintype.card (RegionConfig β T)))
      (Fin (Fintype.card (RegionConfig β R)) × Fin
          (Fintype.card (RegionConfig β T))) ℂ :=
  let e := ((Fintype.equivFin (RegionConfig β R)).symm.prodCongr
    (Fintype.equivFin (RegionConfig β T)).symm).trans (regionUnionEquiv (β := β) h).symm
  (regionState ψ (R ∪ T)).submatrix e e

omit [∀ v, DecidableEq (β v)] in
/-- The joint regional matrix is positive semidefinite. -/
theorem jointMatrix_posSemidef (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (R T : Finset V) (h : Disjoint R T) : (jointMatrix β ψ R T h).PosSemidef :=
  (regionState_posSemidef (R ∪ T) ψ).submatrix _

/-- The regional entropy formula is precisely canonical quantum mutual
information of the joint regional density matrix. -/
theorem regionMutualInformation_eq_matrix (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (R T : Finset V) (h : Disjoint R T) :
    regionMutualInformation ψ R T = _root_.mutualInformation
        (jointMatrix β ψ R T h)
      (jointMatrix_posSemidef β ψ R T h).isHermitian := by
  let ρ := (regionState ψ (R ∪ T)).submatrix
    (regionUnionEquiv (β := β) h).symm (regionUnionEquiv (β := β) h).symm
  have hρ : ρ.PosSemidef := (regionState_posSemidef (R ∪ T) ψ).submatrix _
  have hR : Matrix.partialTraceRight ρ = regionState ψ R :=
    partialTraceRight_regionMatrix_union β _ R T h
  have hT : Matrix.partialTraceLeft ρ = regionState ψ T :=
    partialTraceLeft_regionMatrix_union β _ R T h
  have heq := Entropy.mutualInformation_submatrix_prod_equiv
    (Fintype.equivFin (RegionConfig β R)).symm
    (Fintype.equivFin (RegionConfig β T)).symm ρ hρ.isHermitian
  rw [vonNeumannEntropy_congr hR _ (regionState_posSemidef R ψ).isHermitian,
    vonNeumannEntropy_congr hT _ (regionState_posSemidef T ψ).isHermitian] at heq
  dsimp only [ρ] at heq
  rw [vonNeumannEntropy_submatrix_equiv (regionUnionEquiv (β := β) h).symm _
    (regionState_posSemidef (R ∪ T) ψ).isHermitian] at heq
  simpa only [jointMatrix, Matrix.submatrix_submatrix, regionMutualInformation,
      regionEntropy,
    Equiv.coe_trans] using heq.symm

/-- Mutual information of disjoint regions is nonnegative. -/
theorem regionMutualInformation_nonneg (ψ : EuclideanSpace ℂ ((v : V) → β v))
    (hψ : ‖ψ‖ = 1) (R T : Finset V) (h : Disjoint R T) :
    0 ≤ regionMutualInformation ψ R T := by
  exact sub_nonneg.mpr (regionEntropy_union_le β ψ hψ R T h)

/-- A supplied spectral-tail mass bounds the entropy of a region of a finite system
with local dimension `q`. This is an auxiliary concentration estimate for the entropy obstruction in
SWVC08, arXiv:0705.0292v2, lines 278–305. It does not infer the tail mass from a
matrix approximation error. -/
theorem regionEntropy_le_log_rank_add_spectral_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q D : ℕ}
    (ψ : EuclideanSpace ℂ (ι → Fin q))
    (hψ : ‖ψ‖ = 1) (R : Finset ι) {ε : ℝ}
    (htail : ∑ i ∈ Finset.Ico D (Fintype.card (ManyBody.RegionConfig (fun _ ↦ Fin q) R)),
      (ManyBody.regionState_posSemidef (X := fun _ ↦ Fin q) R ψ).isHermitian.descEigenvalue i
        ≤ ε) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin q) ψ R ≤
      Real.log D + ε * (R.card : ℝ) * Real.log q + Real.log 2 := by
  have hρ := ManyBody.regionState_posSemidef (X := fun _ ↦ Fin q) R ψ
  have hb := hρ.vonNeumannEntropy_le_log_rank_add_tail
    (by simp [ManyBody.trace_regionState, hψ]) htail
  simpa [ManyBody.regionEntropy, ManyBody.RegionConfig, Fintype.card_pi,
    Real.log_pow, mul_assoc] using hb

end ManyBody

open Complex Matrix
open scoped InnerProductSpace ComplexOrder Kronecker
open ManyBody (regionUnionEquiv)

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

export ManyBody (trace_regionState_submatrix_mul)

section Triple

variable {A B C : Finset V} (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)

omit [Fintype V] in
/-- `A` is disjoint from `B ∪ C`. -/
theorem disjoint_union_of_disjoint (hAB : Disjoint A B) (hAC : Disjoint A C) :
    Disjoint A (B ∪ C) := Finset.disjoint_union_right.mpr ⟨hAB, hAC⟩

/-- The configurations of `A ∪ (B ∪ C)` as triples. -/
def tripleEquiv : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (A ∪ (B ∪ C))) ≃
    (ManyBody.RegionConfig (fun v ↦ Fin (n v)) A) ×
        ((ManyBody.RegionConfig (fun v ↦ Fin (n v)) B) ×
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) C)) :=
  (regionUnionEquiv (disjoint_union_of_disjoint hAB hAC)).trans
    (Equiv.prodCongr (Equiv.refl _) (regionUnionEquiv hBC))

omit [Fintype V] in
theorem tripleEquiv_apply (σ : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (A ∪ (B ∪ C)))) :
    tripleEquiv hAB hAC hBC σ =
      ((fun v ↦ σ ⟨v.1, Finset.mem_union_left _ v.2⟩ :
          (ManyBody.RegionConfig (fun v ↦ Fin (n v)) A)),
        ((fun v ↦ σ ⟨v.1, Finset.mem_union_right _ (Finset.mem_union_left _ v.2)⟩ :
          (ManyBody.RegionConfig (fun v ↦ Fin (n v)) B)),
          (fun v ↦ σ ⟨v.1, Finset.mem_union_right _ (Finset.mem_union_right _ v.2)⟩ :
            (ManyBody.RegionConfig (fun v ↦ Fin (n v)) C)))) := rfl

/-- The lift of `M ⊗ 1_C` from `A ∪ (B ∪ C)` is the lift of `M` from `A ∪ B`. -/
theorem localLift_tripleEquiv_kronecker_one
    (M : Matrix
        ((ManyBody.RegionConfig (fun v ↦ Fin (n v)) A) ×
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) B))
        ((ManyBody.RegionConfig (fun v ↦ Fin (n v)) A) ×
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) B)) ℂ) :
    ManyBody.place (A ∪ (B ∪ C))
        (((M ⊗ₖ
        (1 : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) C)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) C) ℂ)).submatrix
      (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm).submatrix
        (tripleEquiv hAB hAC hBC) (tripleEquiv hAB hAC hBC)) =
      ManyBody.place (A ∪ B) (M.submatrix (regionUnionEquiv hAB) (regionUnionEquiv hAB)) := by
  ext σ τ
  rw [ManyBody.place_apply, ManyBody.place_apply]
  simp only [submatrix_apply, tripleEquiv_apply, Equiv.prodAssoc_symm_apply, kroneckerMap_apply,
    one_apply]
  have hCAB : ∀ v ∈ C, v ∉ A ∪ B := fun v hv hvAB ↦ by
    rcases Finset.mem_union.mp hvAB with h | h
    · exact Finset.disjoint_left.mp hAC h hv
    · exact Finset.disjoint_left.mp hBC h hv
  by_cases h : ∀ v ∉ A ∪ B, σ v = τ v
  · have h1 : ∀ v ∉ A ∪ (B ∪ C), σ v = τ v := fun v hv ↦ h v (by
      simp only [Finset.mem_union, not_or] at hv ⊢; exact ⟨hv.1, hv.2.1⟩)
    have h2 : (fun v ↦ σ v.1 : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) C)) =
        (fun v ↦ τ v.1 : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) C)) :=
      funext fun v ↦ h v.1 (hCAB v.1 v.2)
    rw [ite_eq_left h1, ite_eq_left h]
    simp only [h2, ite_true, mul_one]
    rfl
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨v, hv, hne⟩ := h
    by_cases hvZ : v ∈ A ∪ (B ∪ C)
    · have hvC : v ∈ C := by
        simp only [Finset.mem_union, not_or] at hv hvZ
        tauto
      split_ifs with h1 h2
      · exact absurd (congrFun h2 ⟨v, hvC⟩) hne
      · simp
      · rfl
    · rw [ite_eq_right (fun h1 ↦ hne (h1 v hvZ))]

/-- The regional state of `A ∪ (B ∪ C)` as a tripartite matrix. -/
noncomputable def tripleState (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    Matrix
        ((ManyBody.RegionConfig (fun v ↦ Fin (n v)) A) ×
        ((ManyBody.RegionConfig (fun v ↦ Fin (n v)) B) ×
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) C)))
      ((ManyBody.RegionConfig (fun v ↦ Fin (n v)) A) ×
          ((ManyBody.RegionConfig (fun v ↦ Fin (n v)) B) ×
          (ManyBody.RegionConfig (fun v ↦ Fin (n v)) C))) ℂ :=
  (ManyBody.regionState Ω (A ∪ (B ∪ C))).submatrix (tripleEquiv hAB hAC hBC).symm
    (tripleEquiv hAB hAC hBC).symm

/-- The `B ∪ C` marginal of the tripartite state. -/
theorem partialTraceLeft_tripleState (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    partialTraceLeft (tripleState hAB hAC hBC Ω) =
      (ManyBody.regionState Ω (B ∪ C)).submatrix (regionUnionEquiv hBC).symm
        (regionUnionEquiv hBC).symm := by
  refine eq_of_forall_trace_mul_eq fun N ↦ ?_
  rw [tripleState, trace_partialTraceLeft_mul, trace_regionState_submatrix_mul,
    trace_regionState_submatrix_mul]
  have h :
      ((1 : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) A)
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) A) ℂ) ⊗ₖ N).submatrix
      (tripleEquiv hAB hAC hBC) (tripleEquiv hAB hAC hBC) =
      reindex (regionUnionEquiv (disjoint_union_of_disjoint hAB hAC)).symm
        (regionUnionEquiv (disjoint_union_of_disjoint hAB hAC)).symm
        ((1 : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) A)
            (ManyBody.RegionConfig (fun v ↦ Fin (n v)) A) ℂ) ⊗ₖ
          N.submatrix (regionUnionEquiv hBC) (regionUnionEquiv hBC)) := by
    ext σ τ
    rfl
  rw [h, ManyBody.place_union_kronecker, ManyBody.place_one, Matrix.one_mul]

export ManyBody (partialTraceRight_regionState_union)

/-- The `A ∪ B` marginal of the tripartite state. -/
theorem partialTraceRight_reassoc_tripleState (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    partialTraceRight (reassoc (tripleState hAB hAC hBC Ω)) =
      (ManyBody.regionState Ω (A ∪ B)).submatrix (regionUnionEquiv hAB).symm
        (regionUnionEquiv hAB).symm := by
  refine eq_of_forall_trace_mul_eq fun M ↦ ?_
  have hre : reassoc (tripleState hAB hAC hBC Ω) =
      (ManyBody.regionState Ω (A ∪ (B ∪ C))).submatrix
        ((tripleEquiv hAB hAC hBC).trans (Equiv.prodAssoc _ _ _).symm).symm
        ((tripleEquiv hAB hAC hBC).trans (Equiv.prodAssoc _ _ _).symm).symm := rfl
  rw [trace_partialTraceRight_mul, hre, trace_regionState_submatrix_mul,
    trace_regionState_submatrix_mul]
  exact congrArg (fun K ↦ ⟪Ω, toEuclideanLin K Ω⟫_ℂ)
    (localLift_tripleEquiv_kronecker_one hAB hAC hBC M)

include hAB hAC hBC in
/-- **Strong subadditivity for regions.** For pairwise disjoint regions,
`S(A ∪ B ∪ C) + S(B) ≤ S(A ∪ B) + S(B ∪ C)`. -/
theorem regionEntropy_ssa (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ManyBody.regionEntropy Ω (A ∪ (B ∪ C)) + ManyBody.regionEntropy Ω B ≤
      ManyBody.regionEntropy Ω (A ∪ B) + ManyBody.regionEntropy Ω (B ∪ C) := by
  have hω : (tripleState hAB hAC hBC Ω).PosSemidef :=
      (ManyBody.regionState_posSemidef _ Ω).submatrix _
  have h := strongSubadditivity_of_posSemidef _ hω
  have e1 : _root_.vonNeumannEntropy (tripleState hAB hAC hBC Ω) hω.isHermitian =
      ManyBody.regionEntropy Ω (A ∪ (B ∪ C)) :=
    vonNeumannEntropy_submatrix_equiv _ _ _
  have e2 : _root_.vonNeumannEntropy
      (partialTraceRight (partialTraceLeft (tripleState hAB hAC hBC Ω)))
      (partialTraceRight_isHermitian (partialTraceLeft_isHermitian hω.isHermitian)) =
      ManyBody.regionEntropy Ω B := by
    rw [ManyBody.regionEntropy]
    exact vonNeumannEntropy_congr (by rw [partialTraceLeft_tripleState,
      partialTraceRight_regionState_union]) _ _
  have e3 : _root_.vonNeumannEntropy (partialTraceRight (reassoc (tripleState hAB hAC hBC Ω)))
      (partialTraceRight_isHermitian (hω.isHermitian.submatrix _)) =
      ManyBody.regionEntropy Ω (A ∪ B) := by
    rw [vonNeumannEntropy_congr (partialTraceRight_reassoc_tripleState hAB hAC hBC Ω) _
      ((ManyBody.regionState_isHermitian _ Ω).submatrix _)]
    exact vonNeumannEntropy_submatrix_equiv _ _ _
  have e4 : _root_.vonNeumannEntropy (partialTraceLeft (tripleState hAB hAC hBC Ω))
      (partialTraceLeft_isHermitian hω.isHermitian) = ManyBody.regionEntropy Ω (B ∪ C) := by
    rw [vonNeumannEntropy_congr (partialTraceLeft_tripleState hAB hAC hBC Ω) _
      ((ManyBody.regionState_isHermitian _ Ω).submatrix _)]
    exact vonNeumannEntropy_submatrix_equiv _ _ _
  rw [e1, e2, e3, e4] at h
  exact h

end Triple

/-- **Conditioning on a larger region.** For `T' ⊆ T` disjoint from `X`,
`S(X ∪ T) - S(T) ≤ S(X ∪ T') - S(T')`. -/
theorem regionEntropy_cond_anti {X T' T : Finset V} (hXT : Disjoint X T) (hT' : T' ⊆ T)
    (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ManyBody.regionEntropy Ω (X ∪ T) - ManyBody.regionEntropy Ω T ≤
      ManyBody.regionEntropy Ω (X ∪ T') - ManyBody.regionEntropy Ω T' := by
  have hU : T' ∪ (T \ T') = T := Finset.union_sdiff_of_subset hT'
  have h := regionEntropy_ssa (hXT.mono_right hT') (hXT.mono_right Finset.sdiff_subset)
    Finset.disjoint_sdiff Ω
  rw [hU] at h
  linarith

end Entropy


namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- Mutual information of two regions is symmetric: `I(R : T) = I(T : R)`. -/
theorem regionMutualInformation_comm (ψ : EuclideanSpace ℂ ((v : V) → β v)) (R T : Finset V) :
    regionMutualInformation ψ R T = regionMutualInformation ψ T R := by
  unfold regionMutualInformation
  rw [Finset.union_comm]
  ring

end ManyBody

end RegionEntropy

namespace ManyBody

section AuxiliaryPairEntropy

/-!
## The entropy cancellation in the auxiliary-pair comparison

For a pure vector on a physical partition `X, U, Y, V`, the two regional
entropy expressions occurring before and after the Bell projection differ
by an exact sum of mutual informations. Pure-complement equality proves
this cancellation. For a unit vector, the pre-comparison expression is
nonnegative by subadditivity.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 176–203, `comparator:entropy-identity`, at
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
All entropies are those of the actual regional reduced matrices.

Independently formalized; no upstream Lean proof text reused.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (β : ι → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
private theorem entropy_partition (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    (R T : Finset ι) (hd : Disjoint R T) (hc : R ∪ T = Finset.univ) :
    regionEntropy ψ R = regionEntropy ψ T := by
  have hi : IsCompl R T := IsCompl.of_eq (Finset.disjoint_iff_inter_eq_empty.mp hd) hc
  rw [← hi.compl_eq, regionEntropy_compl]
/-- The exact physical entropy cancellation in the auxiliary-pair comparison.
OpenAI area-law manuscript, `07-comparators.tex`, lines 176–203,
`comparator:entropy-identity`. The expressions are evaluated on the same actual
pure vector; no normalization is needed for this balanced identity. -/
theorem auxiliaryPair_regionEntropyIdentity (ψ : EuclideanSpace ℂ ((v : ι) → β v))
    (X U Y V : Finset ι)
    (hXU : Disjoint X U) (hXY : Disjoint X Y) (hXV : Disjoint X V)
    (hUY : Disjoint U Y) (hUV : Disjoint U V) (hYV : Disjoint Y V)
    (hc : X ∪ U ∪ Y ∪ V = Finset.univ) :
    2 * regionEntropy ψ X +
      (regionEntropy ψ (X ∪ U) + regionEntropy ψ V - regionEntropy ψ Y) -
      (regionEntropy ψ U + regionEntropy ψ (U ∪ Y) - regionEntropy ψ Y) =
        regionMutualInformation ψ X V + regionMutualInformation ψ X (Y ∪ V) := by
  have hXU_YV : regionEntropy ψ (X ∪ U) = regionEntropy ψ (Y ∪ V) := by
    apply entropy_partition β ψ
    · simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
      exact ⟨⟨hXY, hUY⟩, ⟨hXV, hUV⟩⟩
    · simpa only [Finset.union_assoc] using hc
  have hUY_XV : regionEntropy ψ (U ∪ Y) = regionEntropy ψ (X ∪ V) := by
    apply entropy_partition β ψ
    · simp only [Finset.disjoint_union_left, Finset.disjoint_union_right]
      exact ⟨⟨hXU.symm, hXY.symm⟩, ⟨hUV, hYV⟩⟩
    · simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hc
  have hU_XYV : regionEntropy ψ U = regionEntropy ψ (X ∪ (Y ∪ V)) := by
    apply entropy_partition β ψ
    · simp only [Finset.disjoint_union_right]
      exact ⟨hXU.symm, hUY, hUV⟩
    · simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hc
  unfold regionMutualInformation
  rw [hXU_YV, hUY_XV, hU_XYV]
  ring

/-- Nonnegativity of the physical pre-comparison entropy expression.
OpenAI area-law manuscript, `07-comparators.tex`, lines 176–187,
`comparator:sharp-lower`. Pure-complement equality turns this expression into
mutual information of the disjoint regions `X ∪ U` and `V`. -/
theorem auxiliaryPair_pre_nonneg (ψ : EuclideanSpace ℂ ((v : ι) → β v)) (hψ : ‖ψ‖ = 1)
    (X U Y V : Finset ι) (hXY : Disjoint X Y) (hXV : Disjoint X V)
    (hUY : Disjoint U Y) (hUV : Disjoint U V) (hYV : Disjoint Y V)
    (hc : X ∪ U ∪ Y ∪ V = Finset.univ) :
    0 ≤ regionEntropy ψ (X ∪ U) + regionEntropy ψ V
        - regionEntropy ψ Y := by
  have hcompl : regionEntropy ψ ((X ∪ U) ∪ V) = regionEntropy ψ Y := by
    apply entropy_partition β ψ
    · simp only [Finset.disjoint_union_left]
      exact ⟨⟨hXY, hUY⟩, hYV.symm⟩
    · simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hc
  have hsub := regionEntropy_union_le β ψ hψ (X ∪ U) V
    (Finset.disjoint_union_left.mpr ⟨hXV, hUV⟩)
  rw [hcompl] at hsub
  linarith

end AuxiliaryPairEntropy

section RelabelMutualInformation

/-!
## Regional mutual information under bijections of tensor factors

A bijection `e` of the sites, together with bijections of the basis labels, carries regions `D`
and `T` to regions `D'` and `T'`. The mutual information of `D'` and `T'` in the transported
vector is the mutual information of `D` and `T` in the original vector: each of the three
regional entropies is invariant (`ManyBody.regionEntropy_relabel`). No normalization or
disjointness is assumed.

This is TNLean's `ManyBody.regionMutualInformation_relabelSites`
(`Lattice/SiteRelabelEntropy`, at commit `707a50e56c`), stated for the transport
`ManyBody.relabelVector`.

### Main results

* `ManyBody.regionMutualInformation_relabel`.
-/

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  {X : V → Type*} {X' : V' → Type*} [∀ v, Fintype (X v)] [∀ v, Fintype (X' v)]
  [∀ v, DecidableEq (X v)] [∀ v, DecidableEq (X' v)]

/-- **Mutual information is invariant under relabelling.** If `e` carries `D` to `D'` and `T`
to `T'`, the mutual information of `D'` and `T'` in the transported vector is the mutual
information of `D` and `T`. -/
theorem regionMutualInformation_relabel (D T : Finset V) (D' T' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D') (hT : ∀ v, v ∈ T ↔ e v ∈ T') (f : ∀ v, X v ≃ X' (e v))
    (Ω : EuclideanSpace ℂ (Config X)) :
    regionMutualInformation (relabelVector e f Ω) D' T' = regionMutualInformation Ω D T := by
  have hU (v : V) : v ∈ D ∪ T ↔ e v ∈ D' ∪ T' := by
    rw [Finset.mem_union, Finset.mem_union, hD, hT]
  rw [regionMutualInformation, regionMutualInformation, regionEntropy_relabel D D' e hD f,
    regionEntropy_relabel T T' e hT f, regionEntropy_relabel (D ∪ T) (D' ∪ T') e hU f]

end RelabelMutualInformation

end ManyBody

section ZeroEntropy

/-!
## Zero entropy across a cut that splits no term

Let an interaction of Hermitian terms, each supported inside a region `B` or outside it, have a
gapped Hamiltonian, with positive gap and ground space the line through a unit vector `Ω`. In
the coordinates of the cut along `B` the Hamiltonian is `H_B ⊗ 1 + 1 ⊗ H_{Bᶜ}`, so `Ω` is a
product vector across the cut and `S_Ω(B) = 0`. No geometry of the sites enters.

Moved from TNLean, `TNLean/Lattice/ZeroEntropy.lean` at commit `e41c3b63`, restated for an
interaction on an arbitrary family of local alphabets.

### Main results

* `ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint` — zero entropy across a
  cut that splits no term.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 2, `01-preliminaries.tex`, lines 116–134 (Lemma 2.2).
* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, `part1_arealaw.tex`, Section 2 (`sec:setting`), first reduction.
-/

open Matrix
open scoped Kronecker

namespace ManyBody.Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} [Fintype ι] {S : ι → Finset V}

/-- **Zero entropy across a cut that splits no term.** Let the terms of an interaction be
Hermitian and each supported inside the region `B` or outside it, and let its Hamiltonian be
gapped at `E₀` with positive gap and ground space the line through the unit vector `Ω`. Then
`S_Ω(B) = 0`. Two-dimensional area law, `01-preliminaries.tex`, lines 116–134 (Lemma 2.2). -/
theorem entropy_eq_zero_of_forall_subset_or_disjoint {Φ : Interaction X S}
    (hherm : ∀ i, (Φ.term i).IsHermitian) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Ω : EuclideanSpace ℂ (Config X)} (hΩ : ‖Ω‖ = 1) (hgs : IsGapped Φ.hamiltonian E₀ Δ)
    (hspan : groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Ω}) {B : Finset V}
    (hsplit : ∀ i, S i ⊆ B ∨ Disjoint (S i) B) :
    ManyBody.regionEntropy Ω B = 0 := by
  classical
  set c := cutEquiv X B
  obtain ⟨x₀⟩ : Nonempty (Config X) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Ω = 0 := by
      apply WithLp.ofLp_injective 2
      funext x
      exact isEmptyElim x
    simp [this] at hΩ
  set s := Finset.univ.filter fun i ↦ S i ⊆ B
  set Hin := ∑ i ∈ s, Φ.term i
  set Hout := ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ S i ⊆ B), Φ.term i
  have hH : Φ.hamiltonian = Hin + Hout := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hin : Hin ∈ supportedOperators X B :=
    sum_mem fun i hi ↦ supportedOperators_mono (Finset.mem_filter.mp hi).2 (Φ.mem i)
  have hout : Hout ∈ supportedOperators X Bᶜ := by
    refine sum_mem fun i hi ↦ supportedOperators_mono ?_ (Φ.mem i)
    exact Finset.subset_compl_iff_disjoint_right.mpr
      ((hsplit i).resolve_left (Finset.mem_filter.mp hi).2)
  have hsumH (t : Finset ι) : (∑ i ∈ t, Φ.term i).IsHermitian :=
    (isSelfAdjoint_sum _ fun i _ ↦ (hherm i).isSelfAdjoint).isHermitian
  obtain ⟨K, hK⟩ := exists_eq_place_of_mem_supportedOperators hin
  obtain ⟨L, hL⟩ := exists_eq_one_kronecker_of_mem_supportedOperators (D := B)
    disjoint_compl_left hout
  have hA : Hin = (K ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ)).submatrix c c := by
    simp [hK, place, reindex_apply, c]
  have hKherm : K.IsHermitian := by
    have hK' : (K ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ)).IsHermitian := by
      have := (hsumH s).submatrix c.symm
      rwa [show ∑ i ∈ s, Φ.term i = Hin from rfl, hA, submatrix_submatrix,
        Equiv.self_comp_symm, submatrix_id_id] at this
    refine IsHermitian.ext fun i j ↦ ?_
    simpa only [kroneckerMap_apply, one_apply_eq, mul_one] using
      hK'.apply (i, (c x₀).2) (j, (c x₀).2)
  have hLherm : L.IsHermitian := by
    have hL' : ((1 : Matrix (RegionConfig X B) (RegionConfig X B) ℂ) ⊗ₖ L).IsHermitian := by
      have := (hsumH (Finset.univ.filter fun i ↦ ¬ S i ⊆ B)).submatrix c.symm
      rwa [show ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ S i ⊆ B), Φ.term i = Hout from rfl, hL,
        submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at this
    refine IsHermitian.ext fun i j ↦ ?_
    simpa only [kroneckerMap_apply, one_apply_eq, one_mul] using
      hL'.apply ((c x₀).1, i) ((c x₀).1, j)
  have hcut : Φ.hamiltonian.submatrix c.symm c.symm =
      K ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ) +
        (1 : Matrix (RegionConfig X B) (RegionConfig X B) ℂ) ⊗ₖ L := by
    rw [hH, hA, hL]
    ext i j
    simp [c]
  have hgs' := (isGapped_submatrix_iff c.symm).mpr hgs
  have hspan' := groundSpace_submatrix_eq_span c.symm hspan
  rw [hcut] at hgs' hspan'
  have hn' : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ c.symm.symm Ω‖ = 1 :=
    (LinearIsometryEquiv.norm_map _ _).trans hΩ
  obtain ⟨-, -, u, w, -, hprod, -, -⟩ :=
    exists_isGapped_factors_of_kronecker_sum hKherm hLherm hΔ hn' hgs' hspan'
  have hΩc : ∀ p, Ω (c.symm p) = u p.1 * w p.2 := fun p ↦ by
    simpa [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using hprod p
  have hρ : regionState Ω B =
      vecMulVec (WithLp.ofLp u) fun b ↦ star (u b) * ∑ y, w y * star (w y) := by
    ext a b
    simp only [regionState_eq_partialTraceRight_cutVector, partialTraceRight_apply,
      vecMulVec_apply, Pi.star_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [hΩc, hΩc, star_mul']
    ring
  refine vonNeumannEntropy_eq_zero_of_rank_le_one (regionState_posSemidef B Ω)
    (by rw [trace_regionState, hΩ]; simp) ?_
  rw [hρ]
  exact rank_vecMulVec_le _ _

end ManyBody.Interaction

end ZeroEntropy

section

open scoped Matrix.Norms.L2Operator

open ManyBody (ChainSupport DomainSupport DomainSupport.toChainSupport
  DomainSupport.toChainSupport_injective IsDomainSupport boundaryEdges interval sitePos
  ChainInteraction DomainInteraction)

open ManyBody (IsGapped groundSpace)


section

variable {L q R : ℕ} {J Δ : ℝ}

/-- On-site interactions give zero entropy on every region of a gapped ground state.
Source: the one-dimensional note, Section 2 (`sec:setting`), component reduction. -/
theorem ManyBody.ChainInteraction.regionEntropy_eq_zero_of_range_zero
    {L q : ℕ} {Δ : ℝ} (h : ChainInteraction L q 0) (hh : ∀ X, (h.term X).IsHermitian)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΔ : 0 < Δ) (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (A : Finset (Fin L)) :
    ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω A = 0 := by
  refine ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint (Φ := h) hh hΔ hΩ hgap
    hspan (B := A) ?_
  intro X
  have hcard := X.property.card_le
  grind [Finset.card_le_one_iff, Finset.disjoint_left]

end

end
