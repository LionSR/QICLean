/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.RegionState
import QICLean.Channel.PartialTrace.PureTensorPower
import QICLean.Representation.Permutation.SchurSurprisal
import QICLean.Representation.Permutation.PermutationRepresentation
import QICLean.Representation.TensorPower.Action
import Mathlib.LinearAlgebra.Matrix.Kronecker
import QICLean.Representation.Permutation.IsotypicDimension
import QICLean.Representation.Permutation.MergeDimensions
import QICLean.Representation.TensorPower.MergeMoment
import QICLean.Representation.TensorPower.SchurLabelCommutation
import QICLean.Entropy.Surprisal.MarginalTails
import Mathlib.Data.Finset.SymmDiff

/-!
# Regional copy permutations in split coordinates

Splitting each physical copy into a region and its complement identifies the
subsystem copy action with the ordinary copy action on the regional factor.
The complementary factor is placed first to agree with the existing
left-partial-trace formulas for pure tensor powers. Consequently the squared
failure norm of the actual subsystem label cutoff is exactly its trace mass
in the tensor power of the actual regional marginal. The one-copy vector need
not be normalized, and its density need not be invariant under regional copy
permutations. The regional marginal of a compressed selected state is a
separate identification.

It also contains the following results.

* `PermutationRepresentation.dim_le_card_of_labelProj_ne_zero`,
  `TensorPower.dim_le_pow_card_of_subsystem_labelProj_ne_zero`: dimensions of labels occurring on an
  actual physical subsystem.

## Main results

* `TensorPower.labelCutoff_subsystemPerm_mul_of_nested`,
  `TensorPower.toEuclideanLin_labelCutoff_of_matched`: transferring the cutoff from one matched
  physical region.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 332–354,
  `comparator:rough-overlap`; copy actions are defined in `05-replicas.tex`,
  lines 14–27.
-/

section SubsystemLabelCoordinates

section SubsystemLabelCoordinates

open scoped BigOperators Matrix Kronecker
open Matrix PermutationRepresentation

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) (k : ℕ) (B : Finset F)

/-- Split each copy into its complementary and regional configurations, then
collect the copies of each factor. -/
def subsystemSplitEquiv : Config k ι ≃
    (Fin k → ManyBody.ComplConfig ι B) ×
      (Fin k → ManyBody.RegionConfig ι B) :=
  (Equiv.piCongrRight fun _ : Fin k ↦
    (ManyBody.cutEquiv ι B).trans (Equiv.prodComm _ _)).trans
      (Equiv.arrowProdEquivProdArrow (Fin k)
        (fun _ ↦ ManyBody.ComplConfig ι B)
        (fun _ ↦ ManyBody.RegionConfig ι B))

omit [Fintype F] in
/-- The actual subsystem permutation fixes the complementary coordinates and
permutes precisely the regional copies after the canonical split. -/
theorem subsystemSplitEquiv_subsystemPerm (σ : Equiv.Perm (Fin k))
    (x : Config k ι) :
    subsystemSplitEquiv ι k B (subsystemPerm k ι B σ x) =
      ((subsystemSplitEquiv ι k B x).1,
        copyPerm (ManyBody.RegionConfig ι B) k σ
          (subsystemSplitEquiv ι k B x).2) := by
  apply Prod.ext
  · funext j f
    change (if (f : F) ∈ B then x (σ⁻¹ j) f else x j f) = x j f
    exact ite_eq_right f.property
  · funext j f
    change (if (f : F) ∈ B then x (σ⁻¹ j) f else x j f) = x (σ⁻¹ j) f
    exact ite_eq_left f.property

variable [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- Every central Schur projector on an actual subsystem is the regional
projector tensored with the identity, in the canonical split coordinates.
No invariance assumption on a state is involved. -/
theorem labelProj_subsystemPerm_submatrix (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (labelProj (subsystemPerm k ι B) l).submatrix
        (subsystemSplitEquiv ι k B).symm (subsystemSplitEquiv ι k B).symm =
      (1 : Matrix (Fin k → ManyBody.ComplConfig ι B)
        (Fin k → ManyBody.ComplConfig ι B) ℂ) ⊗ₖ
          labelProj (copyPerm (ManyBody.RegionConfig ι B) k) l := by
  exact groupAlgebraRep_submatrix_of_prod_action
    (subsystemPerm k ι B) (copyPerm (ManyBody.RegionConfig ι B) k)
    (subsystemSplitEquiv ι k B) (subsystemSplitEquiv_subsystemPerm ι k B)
    (IrrepLabel.centralIdem l)

/-- The closed Schur cutoff on a subsystem becomes the regional cutoff
tensored with the identity under the canonical coordinate split. -/
theorem labelCutoff_subsystemPerm_submatrix (a : ℝ) :
    (labelCutoff (subsystemPerm k ι B) a).submatrix
        (subsystemSplitEquiv ι k B).symm (subsystemSplitEquiv ι k B).symm =
      (1 : Matrix (Fin k → ManyBody.ComplConfig ι B)
        (Fin k → ManyBody.ComplConfig ι B) ℂ) ⊗ₖ
          labelCutoff (copyPerm (ManyBody.RegionConfig ι B) k) a := by
  classical
  ext x y
  simp only [labelCutoff, labelObservable, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have h := congrArg (fun M ↦ M x y) (labelProj_subsystemPerm_submatrix ι k B l)
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
  rw [h]
  ring

/-- The actual failure mass of a subsystem Schur cutoff on a pure tensor power
is its trace mass in the IID regional marginal. This is the regional
expectation identity in the retained-mass argument of the OpenAI area-law
manuscript, `07-comparators.tex`, lines 332–354.

The identity holds for zero copies, empty regions, singular marginals, and
unnormalized vectors. It does not assume regional permutation invariance of
the full pure state. -/
theorem norm_sq_one_sub_labelCutoff_subsystemPerm_prod
    (ψ : EuclideanSpace ℂ ((f : F) → ι f)) (a : ℝ) :
    ‖Matrix.toEuclideanLin (1 - labelCutoff (subsystemPerm k ι B) a)
      (WithLp.toLp 2 (fun x : Config k ι ↦ ∏ j, ψ (x j)))‖ ^ 2 =
        (Matrix.piKronecker (fun _ : Fin k ↦ ManyBody.regionState ψ B) *
          (1 - labelCutoff (copyPerm (ManyBody.RegionConfig ι B) k) a)).trace.re := by
  classical
  let C := ManyBody.ComplConfig ι B
  let R := ManyBody.RegionConfig ι B
  let e := subsystemSplitEquiv ι k B
  let τ : C × R → ℂ := fun x ↦ ψ ((ManyBody.cutEquiv ι B).symm (x.2, x.1))
  let v : Config k ι → ℂ := fun x ↦ ∏ j, ψ (x j)
  let v' : (Fin k → C) × (Fin k → R) → ℂ := fun x ↦ ∏ j, τ (x.1 j, x.2 j)
  let M := 1 - labelCutoff (subsystemPerm k ι B) a
  let P := 1 - labelCutoff (copyPerm R k) a
  have hP : IsStarProjection P := by
    apply IsStarProjection.one_sub
    rw [labelCutoff_eq_spectralProjectionGE]
    exact (isHermitian_labelObservable (copyPerm R k)
      (fun l ↦ Real.log l.dim)).neg.isStarProjection_spectralProjectionGE (-a)
  have hv : v ∘ e.symm = v' := rfl
  have hρ : Matrix.partialTraceLeft (Matrix.vecMulVec τ (star τ)) =
      ManyBody.regionState ψ B := rfl
  have hM : M.submatrix e.symm e.symm =
      (1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ P := by
    change (1 - labelCutoff (subsystemPerm k ι B) a).submatrix e.symm e.symm = _
    simp only [Matrix.submatrix_sub, Pi.sub_apply]
    rw [Matrix.submatrix_one_equiv, labelCutoff_subsystemPerm_submatrix]
    change (1 : Matrix ((Fin k → C) × (Fin k → R))
      ((Fin k → C) × (Fin k → R)) ℂ) -
        (1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ labelCutoff (copyPerm R k) a = _
    rw [← Matrix.one_kronecker_one]
    ext x y
    simp only [P, Matrix.sub_apply, Matrix.kroneckerMap_apply]
    ring
  have hmul : ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ P) *ᵥ v' =
      (M *ᵥ v) ∘ e.symm := by
    calc
      _ = M.submatrix e.symm e.symm *ᵥ (v ∘ e.symm) := by rw [hM, hv]
      _ = (M *ᵥ ((v ∘ e.symm) ∘ e)) ∘ e.symm :=
        Matrix.submatrix_mulVec_equiv M (v ∘ e.symm) e.symm e.symm
      _ = _ := by simp only [Function.comp_def, Equiv.symm_apply_apply]
  have hn : ‖WithLp.toLp 2 ((M *ᵥ v) ∘ e.symm)‖ =
      ‖WithLp.toLp 2 (M *ᵥ v)‖ :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map (WithLp.toLp 2 (M *ᵥ v))
  change ‖WithLp.toLp 2 (M *ᵥ v)‖ ^ 2 = _
  rw [← hn, ← hmul]
  simpa only [hρ] using Matrix.norm_sq_one_kronecker_mulVec_prod τ k P hP

end TensorPower

section SubsystemLabelExponential

/-!
# Regional label exponential moments of pure tensor powers

A regional exponential expectation of a literal product vector is the
trace of the same exponential against the tensor power of its actual
regional reduced density. The one-copy vector need not be normalized.
The identity includes zero copies, empty regions, and zero-dimensional
local spaces.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, proof of
`comparator:sharp-upper`, lines 405–412; the post-marginal identity used
there is `comparator:post-marginal`. Source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- A regional label exponential has the same expectation in the literal
pure tensor power and in the tensor power of the actual regional marginal.
No normalization or regional invariance is assumed.

Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:sharp-upper`, lines 405–412, using
`comparator:post-marginal`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem re_inner_exp_labelEntropy_subsystemPerm_prod
    (ψ : EuclideanSpace ℂ ((f : F) → ι f)) (k : ℕ) (Q : Finset F) (u : ℝ) :
    let Ψ := WithLp.toLp 2 (fun x : Config k ι ↦ ∏ j, ψ (x j))
    (⟪Ψ, Matrix.toEuclideanLin
      (NormedSpace.exp ((u : ℂ) • labelEntropy (subsystemPerm k ι Q))) Ψ⟫_ℂ).re =
      (Matrix.piKronecker (fun _ : Fin k ↦ ManyBody.regionState ψ Q) *
        NormedSpace.exp ((u : ℂ) •
          labelEntropy (copyPerm (ManyBody.RegionConfig ι Q) k))).trace.re := by
  classical
  have hexp {A : Type _} [Fintype A] [DecidableEq A]
      (φ : Equiv.Perm (Fin k) →* Equiv.Perm A) :
      NormedSpace.exp ((u : ℂ) • labelEntropy φ) =
        ∑ l, Complex.exp ((u : ℂ) * (Real.log l.dim : ℂ)) • labelProj φ l := by
    rw [labelEntropy, labelObservable_eq_hom, ← map_smul,
      Matrix.IsOrthogonalResolution.exp_hom, Matrix.IsOrthogonalResolution.hom_apply]
    rfl
  have hM :
      (NormedSpace.exp ((u : ℂ) • labelEntropy (subsystemPerm k ι Q))).submatrix
        (subsystemSplitEquiv ι k Q).symm (subsystemSplitEquiv ι k Q).symm =
      Matrix.kronecker
        (1 : Matrix (Fin k → ManyBody.ComplConfig ι Q)
          (Fin k → ManyBody.ComplConfig ι Q) ℂ)
        (NormedSpace.exp ((u : ℂ) •
          labelEntropy (copyPerm (ManyBody.RegionConfig ι Q) k))) := by
    rw [hexp, hexp]
    ext x y
    simpa only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.mul_sum, mul_left_comm] using
      (Finset.sum_congr rfl (fun (l : IrrepLabel (Equiv.Perm (Fin k)))
        (_ : l ∈ Finset.univ) ↦ congrArg
          (fun M ↦ Complex.exp ((u : ℂ) * (Real.log l.dim : ℂ)) * M x y)
          (labelProj_subsystemPerm_submatrix ι k Q l)))
  let τ : ManyBody.ComplConfig ι Q × ManyBody.RegionConfig ι Q → ℂ :=
    fun x ↦ ψ ((ManyBody.cutEquiv ι Q).symm (x.2, x.1))
  let v' : (Fin k → ManyBody.ComplConfig ι Q) ×
      (Fin k → ManyBody.RegionConfig ι Q) → ℂ :=
    fun x ↦ ∏ j, τ (x.1 j, x.2 j)
  have htrace (P : Matrix (Fin k → ManyBody.RegionConfig ι Q)
      (Fin k → ManyBody.RegionConfig ι Q) ℂ) :
      (Matrix.piKronecker (fun _ : Fin k ↦ ManyBody.regionState ψ Q) * P).trace =
        (Matrix.vecMulVec v' (star v') * Matrix.kronecker
          (1 : Matrix (Fin k → ManyBody.ComplConfig ι Q)
            (Fin k → ManyBody.ComplConfig ι Q) ℂ) P).trace := by
    simpa only [v', Matrix.partialTraceLeft_vecMulVec_prod,
      show Matrix.partialTraceLeft (Matrix.vecMulVec τ (star τ)) =
        ManyBody.regionState ψ Q from rfl, Matrix.kronecker] using
      Matrix.trace_partialTraceLeft_mul P (Matrix.vecMulVec v' (star v'))
  rw [htrace, ← hM, Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  have hv : v' = (fun x : Config k ι ↦ ∏ j, ψ (x j)) ∘
      (subsystemSplitEquiv ι k Q).symm := rfl
  simp only [hv, Matrix.submatrix_mulVec_equiv, Function.comp_assoc,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  simpa only [Equiv.symm_symm, Equiv.symm_comp_self, Function.comp_id,
    dotProduct, Function.comp_apply, Pi.star_apply] using
    congrArg Complex.re ((subsystemSplitEquiv ι k Q).symm.sum_comp
      (fun x : Config k ι ↦
        (NormedSpace.exp ((u : ℂ) • labelEntropy (subsystemPerm k ι Q)) *ᵥ
          (fun y : Config k ι ↦ ∏ j, ψ (y j))) x * star (∏ j, ψ (x j)))).symm

end TensorPower
end

end SubsystemLabelExponential

end SubsystemLabelCoordinates

section SupportedSubsystemLabelDimension

/-!
## Dimensions of labels occurring on an actual physical subsystem

A label whose projector is nonzero has dimension at most that of the
representation space. For an actual subsystem copy action, the canonical
regional coordinate split removes the complementary multiplicity before
this bound is applied. Thus an occurring label has dimension at most the
regional one-copy dimension raised to the copy number.

The argument includes empty coordinate sets and zero copies. A nonzero
projector supplies exactly the support needed by the dimension estimate;
no nonemptiness, normalization or full-rank premise is introduced.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, Lemma 6.1(3), lines 105–111,
  and `07-comparators.tex`, lines 356–365, `comparator:actual-cutoffs`,
  manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped Kronecker

noncomputable section

namespace PermutationRepresentation

variable {G Y : Type*} [Group G] [Fintype G] [Fintype Y] [DecidableEq Y]

/-- The dimension of a label occurring in an actual permutation
representation is bounded by its coordinate dimension. This is the
supported dimension step in the nested-label comparison of
`07-comparators.tex`, lines 356–365; it uses the invariant-subspace
dimension theorem of `05-replicas.tex`, lines 223–226. -/
theorem dim_le_card_of_labelProj_ne_zero (φ : G →* Equiv.Perm Y)
    (l : IrrepLabel G) (hl : labelProj φ l ≠ 0) : l.dim ≤ Fintype.card Y := by
  let W := LinearMap.range (Matrix.toLin' (labelProj φ l))
  have hW : ∀ g, ∀ w ∈ W, permOp φ g *ᵥ w ∈ W := by
    intro g w hw
    obtain ⟨v, rfl⟩ := hw
    refine ⟨permOp φ g *ᵥ v, ?_⟩
    simp only [Matrix.toLin'_apply, mulVec_mulVec]
    rw [(commute_labelProj_permOp φ l g).eq]
  have hfix : ∀ w ∈ W, labelProj φ l *ᵥ w = w := by
    intro w hw
    obtain ⟨v, rfl⟩ := hw
    simp only [Matrix.toLin'_apply, mulVec_mulVec, labelProj_mul_self]
  have hne : W ≠ ⊥ := by
    rw [Ne, LinearMap.range_eq_bot, ← map_zero Matrix.toLin', Matrix.toLin'.injective.eq_iff]
    exact hl
  calc
    l.dim ≤ Module.finrank ℂ W := dim_le_finrank_of_invariant φ l hW hfix hne
    _ ≤ Module.finrank ℂ (Y → ℂ) := W.finrank_le
    _ = Fintype.card Y := by simp

end PermutationRepresentation

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  (k : ℕ) (B : Finset F)

/-- An occurring label of the actual B-subsystem action has dimension at
most `(dim H_B)^k`, independently of all complementary coordinates.
Source: `07-comparators.tex`, lines 356–365, together with the merge
dimension inequalities in `05-replicas.tex`, lines 105–111. -/
theorem dim_le_pow_card_of_subsystem_labelProj_ne_zero
    (l : IrrepLabel (Equiv.Perm (Fin k)))
    (hl : labelProj (subsystemPerm k ι B) l ≠ 0) :
    l.dim ≤ Fintype.card (ManyBody.RegionConfig ι B) ^ k := by
  classical
  have hregional : labelProj (copyPerm (ManyBody.RegionConfig ι B) k) l ≠ 0 := by
    intro hz
    apply hl
    ext x y
    have h := congrArg
      (fun M ↦ M (subsystemSplitEquiv ι k B x) (subsystemSplitEquiv ι k B y))
      (labelProj_subsystemPerm_submatrix ι k B l)
    simpa only [Matrix.submatrix_apply, Equiv.symm_apply_apply, hz,
      Matrix.kronecker_zero, Matrix.zero_apply] using h
  calc
    l.dim ≤ Fintype.card (Fin k → ManyBody.RegionConfig ι B) :=
      dim_le_card_of_labelProj_ne_zero
        (copyPerm (ManyBody.RegionConfig ι B) k) l hregional
    _ = Fintype.card (ManyBody.RegionConfig ι B) ^ k := by simp

end TensorPower

end

end SupportedSubsystemLabelDimension

end SubsystemLabelCoordinates

section MatchedSchurCutoffs

/-!
## Transferring the cutoff from one matched physical region

For two regions comparable by inclusion, the compatible-label dimension
inequalities bound either logarithmic label by the other plus the copy
number times the logarithmic dimension of their difference. Consequently
the actual closed cutoff on the matched region is contained in the actual
cutoff on the target region at the enlarged threshold.

Only the two matched regions occur in this argument. In particular, the
target label is not assumed to commute with all the other cutoffs used to
construct a vector. An arbitrary spectator factor may be retained, so the
result applies to the same Bell-range common-cutoff vector without changing
that vector or its selected auxiliary label.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, Lemma 6.1(3), lines 105–111,
  and `07-comparators.tex`, lines 356–365, `comparator:actual-cutoffs`,
  manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix Kronecker symmDiff
open Matrix PermutationRepresentation

noncomputable section

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (k : ℕ)

/-- On every nonzero joint block of nested regions, either label is bounded
by the other and the actual difference-region dimension. The difference
label is obtained by the identity resolution, not supplied as a premise. -/
private theorem log_dim_bounds_of_subset {S U : Finset F} (hSU : S ⊆ U)
    {l ν : IrrepLabel (Equiv.Perm (Fin k))}
    (hp : labelProj (subsystemPerm k ι S) l *
      labelProj (subsystemPerm k ι U) ν ≠ 0) :
    Real.log ν.dim ≤ Real.log l.dim +
        (k : ℝ) * Real.log (Fintype.card (ManyBody.RegionConfig ι (U \ S))) ∧
      Real.log l.dim ≤ Real.log ν.dim +
        (k : ℝ) * Real.log (Fintype.card (ManyBody.RegionConfig ι (U \ S))) := by
  classical
  have hsum : (∑ μ : IrrepLabel (Equiv.Perm (Fin k)),
      labelProj (subsystemPerm k ι S) l * labelProj (subsystemPerm k ι (U \ S)) μ *
        labelProj (subsystemPerm k ι U) ν) =
      labelProj (subsystemPerm k ι S) l * labelProj (subsystemPerm k ι U) ν := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_labelProj, mul_one]
  obtain ⟨μ, hμ⟩ : ∃ μ : IrrepLabel (Equiv.Perm (Fin k)),
      labelProj (subsystemPerm k ι S) l * labelProj (subsystemPerm k ι (U \ S)) μ *
        labelProj (subsystemPerm k ι U) ν ≠ 0 := by
    by_contra! hzero
    apply hp
    rw [← hsum]
    exact Finset.sum_eq_zero fun μ _ ↦ hzero μ
  have hμproj : labelProj (subsystemPerm k ι (U \ S)) μ ≠ 0 := by
    intro hzero
    exact hμ (by rw [hzero, mul_zero, zero_mul])
  have hdim := merge_dim_le (ι := ι) (k := k)
    (Q := S) (E := U \ S) Finset.disjoint_sdiff
    (l := l) (μ := μ) (ν := ν)
    (by simpa only [Finset.union_sdiff_of_subset hSU] using hμ)
  have hl : (0 : ℝ) < l.dim := Nat.cast_pos.mpr l.dim_pos
  have hm : (0 : ℝ) < μ.dim := Nat.cast_pos.mpr μ.dim_pos
  have hn : (0 : ℝ) < ν.dim := Nat.cast_pos.mpr ν.dim_pos
  have hμlog : Real.log μ.dim ≤
      (k : ℝ) * Real.log (Fintype.card (ManyBody.RegionConfig ι (U \ S))) := by
    have hd : (μ.dim : ℝ) ≤
        (Fintype.card (ManyBody.RegionConfig ι (U \ S)) : ℝ) ^ k := by
      exact_mod_cast dim_le_pow_card_of_subsystem_labelProj_ne_zero ι k (U \ S) μ hμproj
    simpa only [Real.log_pow] using Real.log_le_log hm hd
  have hlarge := Real.log_le_log hn
    (show (ν.dim : ℝ) ≤ (l.dim : ℝ) * μ.dim by exact_mod_cast hdim.1)
  have hsmall := Real.log_le_log hl
    (show (l.dim : ℝ) ≤ (ν.dim : ℝ) * μ.dim by exact_mod_cast hdim.2)
  rw [Real.log_mul hl.ne' hm.ne'] at hlarge
  rw [Real.log_mul hn.ne' hm.ne'] at hsmall
  constructor <;> linarith

/-- For comparable physical regions, the actual cutoff of the matched
region is contained in the target cutoff after the explicit difference
dimension is added to its threshold. No commutation with other regions is
assumed. Source: `07-comparators.tex`, lines 356–365,
`comparator:actual-cutoffs`. -/
theorem labelCutoff_subsystemPerm_mul_of_nested {B Q : Finset F}
    (hnested : B ⊆ Q ∨ Q ⊆ B) {a t : ℝ}
    (ht : a + (k : ℝ) *
      Real.log (Fintype.card (ManyBody.RegionConfig ι (B ∆ Q))) ≤ t) :
    labelCutoff (subsystemPerm k ι Q) t * labelCutoff (subsystemPerm k ι B) a =
      labelCutoff (subsystemPerm k ι B) a := by
  classical
  have hc : ∀ l ν : IrrepLabel (Equiv.Perm (Fin k)),
      Commute (labelProj (subsystemPerm k ι B) l)
        (labelProj (subsystemPerm k ι Q) ν) := by
    intro l ν
    exact hnested.elim
      (fun h ↦ commute_labelProj_subsystemPerm_of_subset ι k h l ν)
      (fun h ↦ (commute_labelProj_subsystemPerm_of_subset ι k h ν l).symm)
  have hlog : ∀ l ν : IrrepLabel (Equiv.Perm (Fin k)),
      labelProj (subsystemPerm k ι B) l * labelProj (subsystemPerm k ι Q) ν ≠ 0 →
      Real.log ν.dim ≤ Real.log l.dim + (k : ℝ) *
        Real.log (Fintype.card (ManyBody.RegionConfig ι (B ∆ Q))) := by
    intro l ν hp
    rcases hnested with h | h
    · have hd : B ∆ Q = Q \ B := by
        rw [Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.empty_union]
      simpa only [hd] using (log_dim_bounds_of_subset ι k h hp).1
    · have hd : B ∆ Q = B \ Q := by
        rw [Finset.symmDiff_def, Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.union_empty]
      have hp' : labelProj (subsystemPerm k ι Q) ν *
          labelProj (subsystemPerm k ι B) l ≠ 0 := by
        rw [← (hc l ν).eq]
        exact hp
      simpa only [hd] using (log_dim_bounds_of_subset ι k h hp').2
  have hfix : ∀ l : IrrepLabel (Equiv.Perm (Fin k)), Real.log l.dim ≤ a →
      labelCutoff (subsystemPerm k ι Q) t * labelProj (subsystemPerm k ι B) l =
        labelProj (subsystemPerm k ι B) l := by
    intro l hl
    calc
      labelCutoff (subsystemPerm k ι Q) t * labelProj (subsystemPerm k ι B) l =
          ∑ ν : IrrepLabel (Equiv.Perm (Fin k)),
            labelProj (subsystemPerm k ι Q) ν * labelProj (subsystemPerm k ι B) l := by
        rw [labelCutoff, labelObservable, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ν _
        rw [smul_mul_assoc]
        by_cases hp : labelProj (subsystemPerm k ι Q) ν *
            labelProj (subsystemPerm k ι B) l = 0
        · simp only [hp, smul_zero]
        · have hp' : labelProj (subsystemPerm k ι B) l *
              labelProj (subsystemPerm k ι Q) ν ≠ 0 := by
            rw [(hc l ν).eq]
            exact hp
          have hν : Real.log ν.dim ≤ t :=
            (hlog l ν hp').trans ((add_le_add hl le_rfl).trans ht)
          simp only [ite_eq_left hν, Complex.ofReal_one, one_smul]
      _ = labelProj (subsystemPerm k ι B) l := by
        rw [← Finset.sum_mul, sum_labelProj, one_mul]
  rw [show labelCutoff (subsystemPerm k ι B) a =
    ∑ l : IrrepLabel (Equiv.Perm (Fin k)),
      ((if Real.log l.dim ≤ a then 1 else 0 : ℝ) : ℂ) •
        labelProj (subsystemPerm k ι B) l from rfl, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_smul_comm]
  by_cases hl : Real.log l.dim ≤ a
  · simpa only [ite_eq_left hl, Complex.ofReal_one, one_smul] using hfix l hl
  · simp only [ite_eq_right hl, Complex.ofReal_zero, zero_smul]

/-- The same vector fixed by a matched physical cutoff is fixed by the
actual enlarged target cutoff. An arbitrary unchanged spectator factor
includes the selected Bell system. The two scalar bounds are exactly
those used in `comparator:actual-cutoffs`, `07-comparators.tex`, lines
356–365. No relation with any other imposed cutoff is required. -/
theorem toEuclideanLin_labelCutoff_of_matched
    {D : Type*} [Fintype D] [DecidableEq D] {B Q : Finset F}
    (hnested : B ⊆ Q ∨ Q ⊆ B) {s z Bsh Bexc : ℝ}
    (hz : 0 < z) (hsh : s ≤ Bsh)
    (hexc : 1 + Real.log (Fintype.card (ManyBody.RegionConfig ι (B ∆ Q))) ≤ Bexc)
    (φ : EuclideanSpace ℂ (D × Config k ι))
    (hφ : toEuclideanLin
      ((1 : Matrix D D ℂ) ⊗ₖ labelCutoff (subsystemPerm k ι B) ((k : ℝ) * (s / z + 1)))
        φ = φ) :
    toEuclideanLin
      ((1 : Matrix D D ℂ) ⊗ₖ
        labelCutoff (subsystemPerm k ι Q) ((k : ℝ) * (Bsh / z + Bexc))) φ = φ := by
  have hthreshold : (k : ℝ) * (s / z + 1) + (k : ℝ) *
      Real.log (Fintype.card (ManyBody.RegionConfig ι (B ∆ Q))) ≤
        (k : ℝ) * (Bsh / z + Bexc) := by
    calc
      _ = (k : ℝ) * (s / z +
          (1 + Real.log (Fintype.card (ManyBody.RegionConfig ι (B ∆ Q))))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (div_le_div_of_nonneg_right hsh hz.le) hexc) (Nat.cast_nonneg k)
  have hmul := labelCutoff_subsystemPerm_mul_of_nested ι k hnested hthreshold
  have hmul' :
      ((1 : Matrix D D ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι Q) ((k : ℝ) * (Bsh / z + Bexc))) *
        ((1 : Matrix D D ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι B) ((k : ℝ) * (s / z + 1))) =
        (1 : Matrix D D ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι B) ((k : ℝ) * (s / z + 1)) := by
    rw [← mul_kronecker_mul, one_mul, hmul]
  calc
    _ = toEuclideanLin
        ((1 : Matrix D D ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι Q) ((k : ℝ) * (Bsh / z + Bexc)))
        (toEuclideanLin
          ((1 : Matrix D D ℂ) ⊗ₖ
            labelCutoff (subsystemPerm k ι B) ((k : ℝ) * (s / z + 1))) φ) := by rw [hφ]
    _ = φ := by rw [← Entropy.toEuclideanLin_mul_apply, hmul', hφ]

end TensorPower

end

end MatchedSchurCutoffs
