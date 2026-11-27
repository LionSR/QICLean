/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Spectral.Eigenvalue.MatrixReindexEuclidean
import QICLean.ManyBody.Replica.LowDefect.RegionalLowDefectProjection
import QICLean.ManyBody.Replica.LowDefect.RegionalRoughLowerNorm
import QICLean.ManyBody.Replica.LowDefect.RegionalSharpLowerNorm
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.Entropy.Typical.PureCompression
import QICLean.Entropy.Typical.Density
import QICLean.ManyBody.Replica.CompressedSite.CompressedTypicalLabelMass
import QICLean.ManyBody.Replica.Configuration.RegionalFiveFactorCoordinates
import QICLean.ManyBody.Replica.Bell.PrevectorRoughUpper
import QICLean.ManyBody.Replica.Bell.SelectedBellPostPin
import QICLean.ManyBody.Replica.Metric.SymmetricBandCommute
import QICLean.Channel.OperatorMean.TreeDerivative

/-!
# Data of the norm comparisons from an auxiliary pair

The objects and hypotheses of the upper and lower norm comparisons (area-law paper,
Proposition 8.1) for a finite product system: the vector `pre_k`, the leaf factors `A_{j,g}`,
the mean-tree root with leaves `A_j = ∏_g A_{j,g}` and its band factorization, the common
auxiliary labels, the typical Schmidt set, the status family, the prefix data and the marginal
moment data.

## Main definitions

* `ManyBody.NormComparison.IsTypicalSchmidtSet`: `comparator:typical-set`.
* `ManyBody.NormComparison.IsStatusFamily`: status partitions obeying `comparator:nesting`.
* `ManyBody.NormComparison.IsPrefixData`: `comparator:prefix-data`.
* `ManyBody.NormComparison.IsMarginalMomentData`: `comparator:mgf-data`.
* `ManyBody.NormComparison.prevector`: the vector `pre_k`.
* `ManyBody.NormComparison.leafFactor`: the leaf factor `A_{j,g}`.
* `ManyBody.NormComparison.meanRoot`: the mean-tree root `𝓜`.

## Main results

* `ManyBody.NormComparison.meanRoot_eq_listProd`: `𝓜 = ∏_g 𝓜_g`.
* `ManyBody.NormComparison.exists_prevector_labels`: the common labels.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
Proposition 8.1 (`prop:comparators`), `07-comparators.tex`, lines 13–214, revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The proofs are written from the
manuscript; no Lean declaration of the accompanying development is reused.
-/

noncomputable section

open Filter Topology Matrix TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
  symmDiff
namespace ManyBody.NormComparison

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (β : ι → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The one-copy sites `V = phys ⊗ C ⊗ R`: the label `some none` is the auxiliary system
`C`, the label `none` is `R`, and both have dimension `d`
(`07-comparators.tex`, lines 87–95). -/
abbrev siteSpace (d : ℕ) : Option (Option ι) → Type :=
  addedSiteSpace (addedSiteSpace β (Fin d)) (Fin d)

/-- The vector `pre_k = π_R^{λ_k}(Ω ⊗ Bell_{CR})^{⊗k}` of `comparator:prevector`, with
`Bell_{CR} = d^{-1/2} ∑_i |i⟩_C|i⟩_R` and the Schur-label projection on the `R` copies
(`07-comparators.tex`, lines 87–90 and 133–140), in the configuration coordinates of
`k` copies of `V`. -/
def prevector (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (d : ℕ)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) (k : ℕ) :
    EuclideanSpace ℂ (TensorPower.Config k (siteSpace β d)) :=
  WithLp.toLp 2 (replicaPrevector Ω d k (ell k) ∘ globalReplicaCopiesEquiv β (Fin d) (Fin d) k)

/-- The leaf factor `A_{j,g} = (W_P⁻¹ W_F⁻¹ W_Y)²` of `comparator:metrics` for one
partition `X, U, Y, V`, with `P = CXU` and `F = RV`, and the common-dimension Schur metrics
`W = W_{·,k}` at parameter `t` (`07-comparators.tex`, lines 91–106). -/
def leafFactor (d k : ℕ) (t : ℝ) (X U Y V : Finset ι) :
    Matrix (TensorPower.Config k (siteSpace β d)) (TensorPower.Config k (siteSpace β d)) ℂ :=
  let W := replicaMetric (siteSpace β d) t k
  ((W (insert (some none) ((X ∪ U).image fun x ↦ some (some x))))⁻¹ *
    (W (insert none (V.image fun x ↦ some (some x))))⁻¹ *
      W (Y.image fun x ↦ some (some x))) ^ 2

/-- The mean-tree root `𝓜` with leaves `A_j = ∏_g A_{j,g}` (`07-comparators.tex`,
lines 101–117). The operators act on the symmetric space `𝒮_k = Sym^k 𝒱` through the
isometric coordinates `Z`, whose range is the symmetric subspace. -/
def meanRoot {St : Type} {K : ℕ} (d k : ℕ) (t : ℝ) (X : Finset ι)
    (U Y V : St → Fin K → Finset ι) {n : ℕ}
    (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ) (T : MeanTree St) :
    Matrix (Fin n) (Fin n) ℂ :=
  T.eval fun j ↦ Zᴴ * (List.ofFn fun g ↦ leafFactor β d k t X (U j g) (Y j g) (V j g)).prod * Z

open Classical in
/-- The band factorization of the mean-tree root: on the symmetric space the leaves
`A_j = ∏_g A_{j,g}` factor into commuting bands, so `𝓜 = ∏_g 𝓜_g`, where `𝓜_g` is the
root of the same tree with leaves `A_{j,g}` (`07-comparators.tex`, lines 114–117). The
far region and the middle region may be given in any spelling equal to `RV` and `Y`. -/
theorem meanRoot_eq_listProd [∀ v, Nonempty (β v)] {St : Type} {K : ℕ}
    {d k n : ℕ} [NeZero d] {t : ℝ} (ht : 0 ≤ t) (X : Finset ι)
    (U Y V : St → Fin K → Finset ι)
    (hdisj : ∀ j l, Disjoint (X ∪ U j l) (Y j l))
    (hV : ∀ j l, V j l = (X ∪ U j l ∪ Y j l)ᶜ)
    (hnest : ∀ j j' l l', l < l' → X ∪ U j l ∪ Y j l ⊆ X ∪ U j' l')
    (Z : Matrix (TensorPower.Config k (siteSpace β d)) (Fin n) ℂ) (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm ((o : Option (Option ι)) → siteSpace β d o) k))
    (T : MeanTree St) (F Ymid : St → Fin K → Finset (Option (Option ι)))
    (hF : ∀ j l, F j l = insert none ((V j l).image fun x ↦ some (some x)))
    (hY : ∀ j l, Ymid j l = (Y j l).image fun x ↦ some (some x)) :
    let W := replicaMetric (siteSpace β d) t k
    let P := fun j l ↦ insert (some none) ((X ∪ U j l).image fun x ↦ some (some x))
    meanRoot β d k t X U Y V Z T =
      (List.ofFn fun l ↦ T.eval fun j ↦
        Zᴴ * ((W (P j l))⁻¹ * (W (F j l))⁻¹ * W (Ymid j l)) ^ 2 * Z).prod := by
  intro W P
  obtain ⟨hPE, hfar, hnestP⟩ :=
    replicaMetric_lifted_region_geometry K (fun j l ↦ X ∪ U j l) Y hdisj hnest
  have hFeq : ∀ j l, F j l = (P j l ∪ Ymid j l)ᶜ := fun j l ↦ by
    rw [hF, hV, hY]
    exact hfar j l
  have : ∀ o, Nonempty (siteSpace β d o) := fun
    | none => ⟨(0 : Fin d)⟩
    | some none => ⟨(0 : Fin d)⟩
    | some (some x) => ‹∀ v, Nonempty (β v)› x
  have hprod := (replicaMetric_symProj_meanTree_eq_product (siteSpace β d) k n Z hZ hZZ ht K
    P Ymid (fun j l ↦ by simpa only [hY] using hPE j l)
    (fun j j' l l' hll' ↦ by simpa only [hY] using hnestP j j' l l' hll')).2 T
  have hleaf : ∀ j l, leafFactor β d k t X (U j l) (Y j l) (V j l) =
      ((W (P j l))⁻¹ * (W (P j l ∪ Ymid j l)ᶜ)⁻¹ * W (Ymid j l)) ^ 2 := fun j l ↦ by
    rw [← hFeq j l, hF j l, hY j l]
    rfl
  simp only [meanRoot, hleaf, hFeq]
  exact hprod

open Classical in
/-- The common auxiliary labels of `comparator:prevector` (`07-comparators.tex`,
lines 130–142 and 240–281) for a finite product system: one label sequence, selected by
the normalized typical Schmidt vector, for which every `pre_k` with `k > 0` is nonzero,
symmetric and of norm at most one, has physical mean energy exactly `E₀`, and carries the
label `λ_k` on both auxiliary systems. The selected labels retain an inverse-polynomial
mass and the logarithmic dimension `k S' + o(k)`. -/
theorem exists_prevector_labels
    (H : Matrix ((v : ι) → β v) ((v : ι) → β v) ℂ)
    (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (E₀ : ℝ)
    (hΩ : ‖Ω‖ = 1) (hE : H *ᵥ Ω.ofLp = (E₀ : ℂ) • Ω.ofLp)
    (X : Finset ι) (E : Finset (ManyBody.RegionConfig β X))
    (hz : 0 < (ManyBody.regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass
      E) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (ManyBody.cutEquiv β X) Ω
    let ψ : ManyBody.ComplConfig β X × Fin E.card → ℂ := fun x ↦
      compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    ∃ ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let ξ := prevector β Ω E.card ell k
        ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 ∧
          symProj (copyPerm ((o : Option (Option ι)) → siteSpace β E.card o) k) *ᵥ ξ = ξ ∧
          globalReplicaMeanHamiltonian β (Fin E.card) (Fin E.card) H k *ᵥ ξ =
            (E₀ : ℂ) • ξ.ofLp ∧
          labelProj (subsystemPerm k (siteSpace β E.card) {some none}) (ell k) *ᵥ ξ = ξ ∧
          labelProj (subsystemPerm k (siteSpace β E.card) {none}) (ell k) *ᵥ ξ = ξ) ∧
      (∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → ManyBody.ComplConfig β X)
              (Fin k → ManyBody.ComplConfig β X) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
              (fun x : (Fin k → ManyBody.ComplConfig β X) ×
                (Fin k → Fin E.card) ↦ ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ ↦ Real.log (ell k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ ↦ (k : ℝ)) := by
  intro ΩX ψ
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((Equiv.prodComm E (ManyBody.ComplConfig β X)).trans
        ((Equiv.refl (ManyBody.ComplConfig β X)).prodCongr
          (Finset.equivFin E)))).norm_map
      (compressedTypicalPureState ΩX E)).trans
      (norm_compressedTypicalPureState ΩX E hz)
  obtain ⟨ell, hpre, hmass, hdim⟩ :=
    exists_label_sequence_replicaPrevector Ω hΩ ψ hψ H E₀ hE
  refine ⟨ell, fun k hk ↦ ?_, hmass, hdim⟩
  intro ξ
  let d := E.card
  let eₖ := globalReplicaCopiesEquiv β (Fin d) (Fin d) k
  let u := replicaPrevector Ω d k (ell k)
  obtain ⟨hne, hnorm, henergy, hC, hR, hsym⟩ := hpre k hk
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ eₖ.symm
  have hξ : ξ = U (WithLp.toLp 2 u) := rfl
  have hξne : ξ ≠ 0 := fun h ↦ hne
    (U.injective (((hξ.symm.trans h).trans U.map_zero.symm)))
  have hξnorm : ‖ξ‖ ≤ 1 :=
    (congrArg norm hξ).trans_le ((U.norm_map (WithLp.toLp 2 u)).trans_le hnorm)
  have htransport
      (K : Matrix ((Fin k → (v : ι) → β v) × ((Fin k → Fin d) × (Fin k → Fin d)))
        ((Fin k → (v : ι) → β v) × ((Fin k → Fin d) × (Fin k → Fin d))) ℂ)
      (c : ℂ) (hu : K *ᵥ u = c • u) :
      K.submatrix eₖ eₖ *ᵥ ξ = c • ξ.ofLp := by
    exact congrArg
      (fun v : EuclideanSpace ℂ (TensorPower.Config k (siteSpace β d)) ↦ v.ofLp)
      ((toEuclideanLin_reindex_piLpCongrLeft eₖ.symm K
        (WithLp.toLp 2 u)).trans
        ((congrArg U (show toEuclideanLin K (WithLp.toLp 2 u) =
            c • WithLp.toLp 2 u from WithLp.ofLp_injective 2 hu)).trans
          (U.map_smul c (WithLp.toLp 2 u))))
  have hjoint : symProj (replicaJointCopyPerm ((v : ι) → β v) (Fin d) (Fin d) k) *ᵥ u = u :=
    symProj_mulVec_of_mem _ fun σ ↦ by
      rw [permOp_replicaJointCopyPerm]
      exact hsym σ
  obtain ⟨hbridgeC, hbridgeR⟩ :=
    labelProj_globalReplicaCopiesEquiv_auxiliary β (Fin d) (Fin d) k (ell k) (ell k)
  refine ⟨hξne, hξnorm, ?_, htransport _ (E₀ : ℂ) henergy, ?_, ?_⟩
  · rw [← symProj_replicaJointCopyPerm_submatrix_globalReplicaCopiesEquiv
      β (Fin d) (Fin d) k]
    simpa only [one_smul] using
      htransport (symProj (replicaJointCopyPerm ((v : ι) → β v) (Fin d) (Fin d) k)) 1
        (by simpa only [one_smul] using hjoint)
  · rw [← hbridgeC]
    simpa only [one_smul] using htransport _ 1 (by simpa only [one_smul] using hC)
  · rw [← hbridgeR]
    simpa only [one_smul] using htransport _ 1 (by simpa only [one_smul] using hR)

/-- **A typical Schmidt set** of `X` for `Ω`, `comparator:typical-set`
(`07-comparators.tex`, lines 37–45). The `p_i` are the eigenvalues of the reduced density
of `X`, that is, the squared Schmidt coefficients across `X`. -/
structure IsTypicalSchmidtSet (Ω : EuclideanSpace ℂ ((v : ι) → β v)) (X : Finset ι)
    (E : Finset (ManyBody.RegionConfig β X)) (w : ℝ) : Prop where
  /-- `E` is a nonempty set of Schmidt indices of `X` (line 38). -/
  nonempty : E.Nonempty
  /-- Its indices are positive Schmidt indices, `p_i > 0` (line 38). -/
  pos : ∀ i ∈ E, 0 < (ManyBody.regionState_posSemidef X Ω).isHermitian.eigenvalues i
  /-- The width satisfies `w ≥ 0` (line 39). -/
  width_nonneg : 0 ≤ w
  /-- `e^{-S_X-w} ≤ p_i ≤ e^{-S_X+w}` for `i ∈ E`, with `S_X = S(X)` (lines 38–41). -/
  window : ∀ i ∈ E,
    Real.exp (-ManyBody.regionEntropy Ω X - w) ≤
        (ManyBody.regionState_posSemidef X Ω).isHermitian.eigenvalues i ∧
      (ManyBody.regionState_posSemidef X Ω).isHermitian.eigenvalues i ≤
        Real.exp (-ManyBody.regionEntropy Ω X + w)
  /-- The mass `z = ∑_{i ∈ E} p_i` is positive (line 42). -/
  mass_pos : 0 < ∑ i ∈ E, (ManyBody.regionState_posSemidef X Ω).isHermitian.eigenvalues i

/-- **A finite collection of status partitions** with target `X`
(`07-comparators.tex`, lines 19–31). A status `j` consists of `K` partitions
`H_phys = H_X ⊗ H_{U_{j,g}} ⊗ H_{Y_{j,g}} ⊗ H_{V_{j,g}}`. -/
structure IsStatusFamily {St : Type} {K : ℕ} (X : Finset ι)
    (U Y V : St → Fin K → Finset ι) : Prop where
  /-- The four factors are disjoint: `X` and `U_{j,g}` (lines 22–23). -/
  disjoint_XU : ∀ j g, Disjoint X (U j g)
  /-- `X` and `Y_{j,g}` are disjoint (lines 22–23). -/
  disjoint_XY : ∀ j g, Disjoint X (Y j g)
  /-- `X` and `V_{j,g}` are disjoint (lines 22–23). -/
  disjoint_XV : ∀ j g, Disjoint X (V j g)
  /-- `U_{j,g}` and `Y_{j,g}` are disjoint (lines 22–23). -/
  disjoint_UY : ∀ j g, Disjoint (U j g) (Y j g)
  /-- `U_{j,g}` and `V_{j,g}` are disjoint (lines 22–23). -/
  disjoint_UV : ∀ j g, Disjoint (U j g) (V j g)
  /-- `Y_{j,g}` and `V_{j,g}` are disjoint (lines 22–23). -/
  disjoint_YV : ∀ j g, Disjoint (Y j g) (V j g)
  /-- The four factors cover all physical sites (lines 22–23). -/
  cover : ∀ j g, X ∪ U j g ∪ Y j g ∪ V j g = Finset.univ
  /-- `comparator:nesting`: for every two allowed statuses and every `g < g'`,
  `XU_gY_g ⊆ XU_{g'}` as sets of physical sites (lines 26–31). -/
  nesting : ∀ j j' g g', g < g' → X ∪ U j g ∪ Y j g ⊆ X ∪ U j' g'

/-- **The prefix data** of the rough upper bound, `comparator:prefix-data`
(`07-comparators.tex`, lines 56–68). -/
structure IsPrefixData (Ω : EuclideanSpace ℂ ((v : ι) → β v)) {St : Type} {K : ℕ}
    (X : Finset ι) (U Y : St → Fin K → Finset ι) (R : Finset (Finset ι))
    (Bsh Bexc : ℝ) : Prop where
  /-- `𝓡` is a nested collection: any two members are comparable (lines 56–57). -/
  nested : ∀ B ∈ R, ∀ B' ∈ R, B ⊆ B' ∨ B' ⊆ B
  /-- Every member of `𝓡` is disjoint from `X` (line 57). -/
  disjoint : ∀ B ∈ R, Disjoint X B
  /-- `S(B) ≤ B_sh` for `B ∈ 𝓡` (line 61). -/
  entropy_le : ∀ B ∈ R, ManyBody.regionEntropy Ω B ≤ Bsh
  /-- For every status and band, each of `Q = U_g` and `Q = U_gY_g` has a matched member
  `B` of `𝓡` containing it or contained in it, with
  `1 + log dim H_{B △ Q} ≤ B_exc` (lines 57–65). -/
  matched : ∀ j g (Q : Finset ι), Q = U j g ∨ Q = U j g ∪ Y j g →
    ∃ B ∈ R, (B ⊆ Q ∨ Q ⊆ B) ∧
      1 + Real.log (Fintype.card (ManyBody.RegionConfig β (B ∆ Q))) ≤ Bexc

/-- **The marginal moment assumption** of the sharp bounds, `comparator:mgf-data`
(`07-comparators.tex`, lines 70–85): for every `Q ∈ {XU_g, V_g, Y_g, U_g, U_gY_g}` the
marginal `ρ_Q` of `Ω` satisfies `log Tr ρ_Q^{1-u} ≤ u S(Q) + C₀ 𝓑 u²` for
`|u| ≤ c₀ / √𝓑`, with only positive eigenvalues in the trace. -/
structure IsMarginalMomentData (Ω : EuclideanSpace ℂ ((v : ι) → β v)) {St : Type} {K : ℕ}
    (X : Finset ι) (U Y V : St → Fin K → Finset ι) (C₀ c₀ B : ℝ) : Prop where
  /-- `𝓑 ≥ 1` (line 76). -/
  one_le : 1 ≤ B
  /-- The moment bound for the five marginals of every status and band (lines 71–83). -/
  moment : ∀ j g (Q : Finset ι),
    Q = X ∪ U j g ∨ Q = V j g ∨ Q = Y j g ∨ Q = U j g ∨ Q = U j g ∪ Y j g →
    ∀ u : ℝ, |u| ≤ c₀ / Real.sqrt B →
      Real.log (∑ i, if 0 < (ManyBody.regionState_posSemidef Q Ω).isHermitian.eigenvalues i
          then (ManyBody.regionState_posSemidef Q Ω).isHermitian.eigenvalues i ^ (1 - u)
          else 0) ≤
        u * ManyBody.regionEntropy Ω Q + C₀ * B * u ^ 2

namespace IsStatusFamily

variable {β} {St : Type} {K : ℕ} {X : Finset ι} {U Y V : St → Fin K → Finset ι}

/-- The far part of a status partition is the complement of the other three:
`V = (X ∪ U ∪ Y)ᶜ`. -/
theorem far_eq_compl (h : IsStatusFamily X U Y V) (j : St) (l : Fin K) :
    V j l = (X ∪ U j l ∪ Y j l)ᶜ := by
  ext x
  simp only [Finset.mem_compl, Finset.mem_union]
  constructor
  · rintro hx ((hX | hU) | hY)
    · exact Finset.disjoint_left.mp (h.disjoint_XV j l) hX hx
    · exact Finset.disjoint_left.mp (h.disjoint_UV j l) hU hx
    · exact Finset.disjoint_left.mp (h.disjoint_YV j l) hY hx
  · intro hx
    have hmem : x ∈ X ∪ U j l ∪ Y j l ∪ V j l := (h.cover j l).symm ▸ Finset.mem_univ x
    simp only [Finset.mem_union] at hmem
    tauto

/-- The inner region `X ∪ U` of a status partition is disjoint from the middle part `Y`. -/
theorem disjoint_inner_middle (h : IsStatusFamily X U Y V) (j : St) (l : Fin K) :
    Disjoint (X ∪ U j l) (Y j l) :=
  Finset.disjoint_union_left.mpr ⟨h.disjoint_XY j l, h.disjoint_UY j l⟩

/-- The nesting of a status family without the target: `U_g ∪ Y_g ⊆ U_{g'}` for `g < g'`
and every two statuses. -/
theorem union_subset_later (h : IsStatusFamily X U Y V) (j j' : St) (l l' : Fin K) (hll : l < l') :
    U j l ∪ Y j l ⊆ U j' l' := by
  intro x hx
  have hxX : x ∉ X := fun hX ↦ by
    rcases Finset.mem_union.mp hx with hU | hY
    · exact Finset.disjoint_left.mp (h.disjoint_XU j l) hX hU
    · exact Finset.disjoint_left.mp (h.disjoint_XY j l) hX hY
  have := h.nesting j j' l l' hll (by
    rw [Finset.union_assoc]; exact Finset.mem_union_right _ hx)
  rcases Finset.mem_union.mp this with hX | hU
  · exact absurd hX hxX
  · exact hU

end IsStatusFamily

/-- The marginal moment assumption in terms of the surprisal moment of the eigenvalues of
the marginal: `log E e^{uK} ≤ u S(Q) + C₀ 𝓑 u²` for `|u| ≤ c₀ / √𝓑`. -/
theorem IsMarginalMomentData.surprisalMoment_le {Ω : EuclideanSpace ℂ ((v : ι) → β v)}
    {St : Type} {K : ℕ} {X : Finset ι} {U Y V : St → Fin K → Finset ι} {C₀ c₀ B : ℝ}
    (h : IsMarginalMomentData β Ω X U Y V C₀ c₀ B) (j : St) (l : Fin K) (Q : Finset ι)
    (hQ : Q = X ∪ U j l ∨ Q = V j l ∨ Q = Y j l ∨ Q = U j l ∨ Q = U j l ∪ Y j l)
    (u : ℝ) (hu : |u| ≤ c₀ / Real.sqrt B) :
    Real.log (Entropy.surprisalMoment
      (ManyBody.regionState_posSemidef Q Ω).isHermitian.eigenvalues u) ≤
        u * ManyBody.regionEntropy Ω Q + C₀ * B * u ^ 2 := by
  rw [Entropy.surprisalMoment_eq_sum_rpow _
    (ManyBody.regionState_posSemidef Q Ω).eigenvalues_nonneg]
  exact h.moment j l Q hQ u hu

end ManyBody.NormComparison
