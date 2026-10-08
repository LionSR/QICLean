/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RegionSplit
import QICLean.Entropy.ConditionalSkewPhase
import QICLean.Representation.MarkedSimilaritySymbol
import QICLean.Analysis.EntropyContinuity

/-!
# The skew bound of Lemma 6.4

Lemma 6.4 of the area-law paper (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, lines 640–660 and 838–843) finishes by applying the conditional skew estimate
(Lemma 5.3) pointwise to the symbol `f_θ`. Lemma 5.3 is stated on tensor factors
`(P₀ P₁)((x U) F)`; this file reads it on regions of `V`, for a partition `P = P₀ P₁`,
`Y = x U`, `F` and an operator `0 ≤ h ≤ 1` supported on `P₀ x`.

## Main declarations

* `TensorPower.SkewPartition`, `TensorPower.SkewPartition.equiv` — the coordinates.
* `TensorPower.SkewPartition.skewFun_eq_markedScalarSymbol` — `f_θ` is the function of
  Lemma 5.3 in these coordinates.
* `TensorPower.SkewPartition.markedScalarSymbol_skew_le` — Lemma 5.3 for `f_θ`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 5.3 (`lem:skew`), `04-conditional.tex`, lines 487–507, and Lemma 6.4 (`lem:symbol`),
  `05-replicas.tex`, lines 640–660 and 838–843.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix Entropy Entropy.ConditionalSkew PermutationRepresentation MeasureTheory
open scoped Kronecker ComplexOrder MatrixOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- A partition `V = (P₀ ∪ P₁) ∪ (x ∪ U) ∪ F` into the regions of Lemmas 5.3 and 6.4. -/
structure SkewPartition (P₀ P₁ x U F : Finset V) : Prop where
  P₀P₁ : Disjoint P₀ P₁
  xU : Disjoint x U
  PY : Disjoint (P₀ ∪ P₁) (x ∪ U)
  PF : Disjoint (P₀ ∪ P₁) F
  YF : Disjoint (x ∪ U) F
  cover : ∀ v, v ∈ P₀ ∪ P₁ ∨ v ∈ x ∪ U ∨ v ∈ F

section CoherentIntegral

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

theorem continuous_comp_unitary_mulVec_single {φ : (Ω → ℂ) → ℂ}
    (hφ : ContinuousOn φ unitSphere) (a : Ω) :
    Continuous fun U : unitaryGroup Ω ℂ => φ ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) :=
  hφ.comp_continuous (continuous_unitary_mulVec_single a) fun U =>
    unitary_mulVec_single_mem_unitSphere U a

/-- **Monotonicity of the coherent measure**: for continuous real-part bounds on unit vectors,
`Re ∫ φ dμ_σ ≤ Re ∫ ψ dμ_σ`. -/
theorem re_coherentIntegral_le {σ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hσp : σ.PosSemidef)
    (a : Ω) {φ ψ : (Ω → ℂ) → ℂ} (hφ : ContinuousOn φ unitSphere)
    (hψ : ContinuousOn ψ unitSphere) (hle : ∀ θ ∈ unitSphere, (φ θ).re ≤ (ψ θ).re) :
    (coherentIntegral a σ φ).re ≤ (coherentIntegral a σ ψ).re := by
  set θ : unitaryGroup Ω ℂ → Ω → ℂ := fun U => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1
  set F : unitaryGroup Ω ℂ → ℂ := fun U => (σ * coherentProj k (θ U)).trace
  have hF0 : ∀ U, 0 ≤ F U := fun U => by
    change 0 ≤ (σ * coherentProj k (θ U)).trace
    rw [coherentProj, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
    exact hσp.dotProduct_mulVec_nonneg _
  have hFim : ∀ U, (F U).im = 0 := fun U => ((Complex.nonneg_iff.mp (hF0 U)).2).symm
  have hFre : ∀ U, 0 ≤ (F U).re := fun U => (Complex.nonneg_iff.mp (hF0 U)).1
  have hT : 0 ≤ (symProj (copyPerm Ω k)).trace := by
    have h : (symProj (copyPerm Ω k)).PosSemidef := by
      have e : symProj (copyPerm Ω k) =
          (symProj (copyPerm Ω k))ᴴ * symProj (copyPerm Ω k) := by
        rw [isHermitian_symProj.eq, symProj_mul_symProj]
      rw [e]; exact posSemidef_conjTranspose_mul_self _
    exact h.trace_nonneg
  have hTim : (symProj (copyPerm Ω k)).trace.im = 0 := ((Complex.nonneg_iff.mp hT).2).symm
  have hTre : 0 ≤ (symProj (copyPerm Ω k)).trace.re := (Complex.nonneg_iff.mp hT).1
  have hcφ := continuous_comp_unitary_mulVec_single hφ a
  have hcψ := continuous_comp_unitary_mulVec_single hψ a
  have hiφ := integrable_coherentIntegrand a σ hcφ
  have hiψ := integrable_coherentIntegrand a σ hcψ
  simp only [coherentIntegral, Complex.mul_re, hTim, zero_mul, sub_zero]
  refine mul_le_mul_of_nonneg_left ?_ hTre
  rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, ← integral_re hiφ, ← integral_re hiψ]
  refine MeasureTheory.integral_mono hiφ.re hiψ.re fun U => ?_
  simp only [RCLike.re_to_complex, Complex.mul_re]
  change (F U).re * (φ (θ U)).re - (F U).im * (φ (θ U)).im ≤
    (F U).re * (ψ (θ U)).re - (F U).im * (ψ (θ U)).im
  rw [hFim, zero_mul, zero_mul, sub_zero, sub_zero]
  exact mul_le_mul_of_nonneg_left (hle _ (unitary_mulVec_single_mem_unitSphere U a)) (hFre U)

theorem coherentIntegral_const_mul (a : Ω) (σ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ)
    (c : ℂ) (φ : (Ω → ℂ) → ℂ) :
    coherentIntegral a σ (fun θ => c * φ θ) = c * coherentIntegral a σ φ := by
  simp only [coherentIntegral]
  simp_rw [mul_left_comm _ c]
  rw [integral_const_mul]
  ring

end CoherentIntegral

section Continuity

variable {α β : Type*}

theorem continuous_partialTraceRight [Fintype β] :
    Continuous (partialTraceRight : Matrix (α × β) (α × β) ℂ → Matrix α α ℂ) :=
  continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun k _ =>
    (continuous_apply (j, k)).comp (continuous_apply (i, k))

theorem continuous_partialTraceLeft [Fintype α] :
    Continuous (partialTraceLeft : Matrix (α × β) (α × β) ℂ → Matrix β β ℂ) :=
  continuous_pi fun i => continuous_pi fun j => continuous_finsetSum _ fun k _ =>
    (continuous_apply (k, j)).comp (continuous_apply (k, i))

theorem continuous_submatrix {γ : Type*} (e f : γ → α) :
    Continuous fun M : Matrix α α ℂ => M.submatrix e f :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply (f j)).comp (continuous_apply (e i))

theorem continuous_vecMulVec_self : Continuous fun w : α → ℂ => vecMulVec w (star w) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply i).mul (continuous_apply j).star

theorem eigenvalues_mem_Icc_of_trace_eq_one {m : Type*} [Fintype m] [DecidableEq m]
    {M : Matrix m m ℂ} (hM : M.PosSemidef) (htr : M.trace = 1) (hH : M.IsHermitian) (i : m) :
    hH.eigenvalues i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hM.eigenvalues_nonneg i, posSemidef_trace_one_eigenvalues_le_one hM htr i⟩

open Entropy.MarginalPhase in
/-- Continuity of the conditional mutual information along continuous families of states. -/
theorem continuousOn_condMutualInfo {X U F Z : Type*} [Fintype X] [DecidableEq X] [Fintype U]
    [DecidableEq U] [Fintype F] [DecidableEq F] [TopologicalSpace Z]
    {ρ : Z → Matrix (X × (U × F)) (X × (U × F)) ℂ} (hρ : ∀ z, (ρ z).PosSemidef) {T : Set Z}
    (hc : ContinuousOn ρ T) (htr : ∀ z ∈ T, (ρ z).trace = 1) :
    ContinuousOn (fun z => condMutualInfo (ρ z) (hρ z)) T := by
  have hXU : ∀ z, (marginalXU (ρ z)).PosSemidef := fun z =>
    ((hρ z).submatrix assocE).partialTraceRight
  have htrXU : ∀ z ∈ T, (marginalXU (ρ z)).trace = 1 := fun z hz => by
    rw [marginalXU, trace_partialTraceRight, trace_submatrix_equiv, htr z hz]
  have cXU : ContinuousOn (fun z => marginalXU (ρ z)) T :=
    (continuous_partialTraceRight.comp (continuous_submatrix _ _)).comp_continuousOn hc
  have cUF : ContinuousOn (fun z => marginalUF (ρ z)) T :=
    continuous_partialTraceLeft.comp_continuousOn hc
  have cU : ContinuousOn (fun z => marginalU (ρ z)) T :=
    continuous_partialTraceLeft.comp_continuousOn cXU
  unfold condMutualInfo
  refine ((ContinuousOn.add ?_ ?_).sub ?_).sub ?_
  · exact continuousOn_vonNeumannEntropy _ cXU fun z hz i =>
      eigenvalues_mem_Icc_of_trace_eq_one (hXU z) (htrXU z hz) _ i
  · exact continuousOn_vonNeumannEntropy _ cUF fun z hz i =>
      eigenvalues_mem_Icc_of_trace_eq_one (hρ z).partialTraceLeft
        (by rw [trace_partialTraceLeft, htr z hz]) _ i
  · exact continuousOn_vonNeumannEntropy _ cU fun z hz i =>
      eigenvalues_mem_Icc_of_trace_eq_one (hXU z).partialTraceLeft
        (by rw [trace_partialTraceLeft, htrXU z hz]) _ i
  · exact continuousOn_vonNeumannEntropy _ hc fun z hz i =>
      eigenvalues_mem_Icc_of_trace_eq_one (hρ z) (htr z hz) _ i

end Continuity

/-- Real powers through the complex functional calculus agree with real powers on positive
matrices. -/
theorem cfcC_suppPowFun_ofReal {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ}
    (hA : A.PosSemidef) (s : ℝ) : cfcC A (suppPowFun (s : ℂ)) = cfc (suppRpow s) A := by
  rw [cfcC_congr_of_nonneg hA (g₂ := fun t => ((suppRpow s t : ℝ) : ℂ)) fun t ht => ?_]
  · simp only [cfcC, Complex.ofReal_re, Complex.ofReal_im, cfc_const_zero, smul_zero, add_zero]
  · rcases ht.eq_or_lt with h0 | h0
    · simp [suppPowFun, suppRpow, ← h0]
    · simp only [suppPowFun, suppRpow, h0.ne', ↓reduceIte]
      exact (Complex.ofReal_cpow ht s).symm

namespace SkewPartition

variable {P₀ P₁ x U F : Finset V} (hp : SkewPartition P₀ P₁ x U F)
include hp

omit [Fintype V] in
theorem P_W : Disjoint (P₀ ∪ P₁) ((x ∪ U) ∪ F) := Finset.disjoint_union_right.mpr ⟨hp.PY, hp.PF⟩

omit [Fintype V] in
theorem cover_P (v : V) : v ∈ P₀ ∪ P₁ ∨ v ∈ (x ∪ U) ∪ F := by
  rcases hp.cover v with h | h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_union_left _ h)
  · exact Or.inr (Finset.mem_union_right _ h)

omit [Fintype V] in
theorem P₀x : Disjoint P₀ x :=
  Finset.disjoint_of_subset_left Finset.subset_union_left
    (Finset.disjoint_of_subset_right Finset.subset_union_left hp.PY)

/-- The coordinates `V ≅ (P₀ P₁)((x U) F)`. -/
def equiv : SiteConfig n ≃ (RegionConfig n P₀ × RegionConfig n P₁) ×
    ((RegionConfig n x × RegionConfig n U) × RegionConfig n F) :=
  (regionSplitEquiv hp.P_W hp.cover_P).trans (Equiv.prodCongr (regionUnionEquiv hp.P₀P₁)
    ((regionUnionEquiv hp.YF).trans (Equiv.prodCongr (regionUnionEquiv hp.xU) (Equiv.refl _))))

omit [Fintype V] in
theorem isRegionSplit_P :
    IsRegionSplit (P₀ ∪ P₁) (regionUnionEquiv hp.P₀P₁) (SkewPartition.equiv (n := n) hp) := by
  have h := (isRegionSplit_regionSplitEquiv (n := n) hp.P_W hp.cover_P).trans_prodCongr
    (regionUnionEquiv hp.P₀P₁)
    ((regionUnionEquiv hp.YF).trans (Equiv.prodCongr (regionUnionEquiv hp.xU) (Equiv.refl _)))
  rwa [Equiv.refl_trans] at h

omit [Fintype V] in
theorem equiv_apply (σ : SiteConfig n) :
    SkewPartition.equiv hp σ = (((fun v : {v // v ∈ P₀} => σ v), (fun v : {v // v ∈ P₁} => σ v)),
      (((fun v : {v // v ∈ x} => σ v), (fun v : {v // v ∈ U} => σ v)),
        (fun v : {v // v ∈ F} => σ v))) := rfl

omit [Fintype V] [DecidableEq V] hp in
theorem restrict_eq_iff {D : Finset V} {σ τ : SiteConfig n} :
    ((fun v : {v // v ∈ D} => σ v) = fun v : {v // v ∈ D} => τ v) ↔ ∀ v ∈ D, σ v = τ v :=
  ⟨fun h v hv => congrFun h ⟨v, hv⟩, fun h => funext fun v => h v.1 v.2⟩

omit [Fintype V] in
theorem mem_cases (v : V) : v ∈ P₀ ∨ v ∈ P₁ ∨ v ∈ x ∨ v ∈ U ∨ v ∈ F := by
  rcases hp.cover v with h | h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases Finset.mem_union.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

omit [Fintype V] in
theorem not_mem_of_mem {v : V} :
    (v ∈ P₀ → v ∉ P₁ ∧ v ∉ x ∧ v ∉ U ∧ v ∉ F) ∧ (v ∈ P₁ → v ∉ P₀ ∧ v ∉ x ∧ v ∉ U ∧ v ∉ F) ∧
    (v ∈ x → v ∉ P₀ ∧ v ∉ P₁ ∧ v ∉ U ∧ v ∉ F) ∧ (v ∈ U → v ∉ P₀ ∧ v ∉ P₁ ∧ v ∉ x ∧ v ∉ F) ∧
    (v ∈ F → v ∉ P₀ ∧ v ∉ P₁ ∧ v ∉ x ∧ v ∉ U) := by
  have d01 : v ∈ P₀ → v ∉ P₁ := fun h => Finset.disjoint_left.mp hp.P₀P₁ h
  have dxU : v ∈ x → v ∉ U := fun h => Finset.disjoint_left.mp hp.xU h
  have dPY : v ∈ P₀ ∪ P₁ → v ∉ x ∪ U := fun h => Finset.disjoint_left.mp hp.PY h
  have dPF : v ∈ P₀ ∪ P₁ → v ∉ F := fun h => Finset.disjoint_left.mp hp.PF h
  have dYF : v ∈ x ∪ U → v ∉ F := fun h => Finset.disjoint_left.mp hp.YF h
  simp only [Finset.mem_union] at dPY dPF dYF
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h' <;> tauto

/-- `(P₀ P₁)((x U) F) ≃ (x U)((P₀ P₁) F)`. -/
def regroupY {A₀ A₁ X' U' F' : Type*} :
    (A₀ × A₁) × ((X' × U') × F') ≃ (X' × U') × ((A₀ × A₁) × F') where
  toFun q := (q.2.1, (q.1, q.2.2))
  invFun r := (r.2.1, (r.1, r.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- `(P₀ P₁)((x U) F) ≃ (P₀ x)(P₁ (U F))`, the regrouping of Lemma 5.3. -/
def regroupH {A₀ A₁ X' U' F' : Type*} :
    (A₀ × A₁) × ((X' × U') × F') ≃ (A₀ × X') × (A₁ × (U' × F')) where
  toFun := regroup
  invFun r := ((r.1.1, r.2.1), ((r.1.2, r.2.2.1), r.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
theorem isRegionSplit_Y : IsRegionSplit (x ∪ U) (regionUnionEquiv hp.xU)
    ((SkewPartition.equiv (n := n) hp).trans regroupY) where
  fst σ := rfl
  snd σ τ := by
    simp only [Equiv.trans_apply, equiv_apply, regroupY, Equiv.coe_fn_mk, Prod.mk.injEq,
      restrict_eq_iff]
    constructor
    · rintro ⟨⟨h0, h1⟩, hF⟩ v hv
      rcases hp.mem_cases v with h | h | h | h | h
      · exact h0 v h
      · exact h1 v h
      · exact absurd (Finset.mem_union_left _ h) hv
      · exact absurd (Finset.mem_union_right _ h) hv
      · exact hF v h
    · intro h
      have nm := fun v => hp.not_mem_of_mem (v := v)
      refine ⟨⟨fun v hv => h v ?_, fun v hv => h v ?_⟩, fun v hv => h v ?_⟩ <;>
        simp only [Finset.mem_union, not_or] <;> have := nm v <;> tauto

omit [Fintype V] in
theorem isRegionSplit_H : IsRegionSplit (P₀ ∪ x) (regionUnionEquiv hp.P₀x)
    ((SkewPartition.equiv (n := n) hp).trans regroupH) where
  fst σ := rfl
  snd σ τ := by
    change ((fun v : {v // v ∈ P₁} => σ v), ((fun v : {v // v ∈ U} => σ v),
        (fun v : {v // v ∈ F} => σ v))) = ((fun v : {v // v ∈ P₁} => τ v),
        ((fun v : {v // v ∈ U} => τ v), (fun v : {v // v ∈ F} => τ v))) ↔ _
    simp only [Prod.mk.injEq, restrict_eq_iff]
    constructor
    · rintro ⟨h1, hU, hF⟩ v hv
      rcases hp.mem_cases v with h | h | h | h | h
      · exact absurd (Finset.mem_union_left _ h) hv
      · exact h1 v h
      · exact absurd (Finset.mem_union_right _ h) hv
      · exact hU v h
      · exact hF v h
    · intro h
      have nm := fun v => hp.not_mem_of_mem (v := v)
      refine ⟨fun v hv => h v ?_, fun v hv => h v ?_, fun v hv => h v ?_⟩ <;>
        simp only [Finset.mem_union, not_or] <;> have := nm v <;> tauto

omit hp in
theorem margY_eq {A₀ A₁ X' U' F' : Type*} [Fintype A₀] [Fintype A₁] [Fintype F']
    (w : (A₀ × A₁) × ((X' × U') × F') → ℂ) :
    margY w = partialTraceRight (vecMulVec (w ∘ regroupY.symm) (star (w ∘ regroupY.symm))) := by
  ext a b
  simp only [margY, margW, partialTraceRight_apply, partialTraceLeft, vecMulVec_apply,
    Function.comp_apply, Pi.star_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]
  rfl

omit hp in
theorem liftY_eq {A₀ A₁ X' U' F' : Type*} [DecidableEq A₀] [DecidableEq A₁] [DecidableEq F']
    (B : Matrix (X' × U') (X' × U') ℂ) :
    liftY (P₀ := A₀) (P₁ := A₁) (F := F') B =
      (B ⊗ₖ (1 : Matrix ((A₀ × A₁) × F') ((A₀ × A₁) × F') ℂ)).submatrix regroupY regroupY := by
  ext q q'
  simp only [liftY, regroupY, Equiv.coe_fn_mk, submatrix_apply, kroneckerMap_apply, one_apply,
    Prod.ext_iff]
  split_ifs <;> simp_all

variable (n) in
/-- The vector `θ` in the coordinates `(P₀ P₁)((x U) F)`. -/
def transport (θ : SiteConfig n → ℂ) :
    (RegionConfig n P₀ × RegionConfig n P₁) × ((RegionConfig n x × RegionConfig n U) ×
      RegionConfig n F) → ℂ :=
  θ ∘ (SkewPartition.equiv (n := n) hp).symm

theorem margP_transport (θ : SiteConfig n → ℂ) :
    margP (hp.transport n θ) =
      (regionState (P₀ ∪ P₁) (WithLp.toLp 2 θ)).submatrix (regionUnionEquiv hp.P₀P₁).symm
        (regionUnionEquiv hp.P₀P₁).symm :=
  hp.isRegionSplit_P.partialTraceRight_vecMulVec θ

theorem margY_transport (θ : SiteConfig n → ℂ) :
    margY (hp.transport n θ) =
      (regionState (x ∪ U) (WithLp.toLp 2 θ)).submatrix (regionUnionEquiv hp.xU).symm
        (regionUnionEquiv hp.xU).symm := by
  rw [margY_eq]
  exact hp.isRegionSplit_Y.partialTraceRight_vecMulVec θ

theorem liftP_eq (K : Matrix (RegionConfig n (P₀ ∪ P₁)) (RegionConfig n (P₀ ∪ P₁)) ℂ) :
    liftP (X := RegionConfig n x) (U := RegionConfig n U) (F := RegionConfig n F)
      (K.submatrix (regionUnionEquiv hp.P₀P₁).symm (regionUnionEquiv hp.P₀P₁).symm) =
      (localLift (P₀ ∪ P₁) K).submatrix (SkewPartition.equiv hp).symm
        (SkewPartition.equiv hp).symm :=
  (hp.isRegionSplit_P.localLift_submatrix K).symm

theorem liftY_eq' (K : Matrix (RegionConfig n (x ∪ U)) (RegionConfig n (x ∪ U)) ℂ) :
    liftY (P₀ := RegionConfig n P₀) (P₁ := RegionConfig n P₁) (F := RegionConfig n F)
      (K.submatrix (regionUnionEquiv hp.xU).symm (regionUnionEquiv hp.xU).symm) =
      (localLift (x ∪ U) K).submatrix (SkewPartition.equiv hp).symm
        (SkewPartition.equiv hp).symm := by
  rw [liftY_eq, ← hp.isRegionSplit_Y.localLift_submatrix K, submatrix_submatrix]
  rfl

theorem liftH_eq (K : Matrix (RegionConfig n (P₀ ∪ x)) (RegionConfig n (P₀ ∪ x)) ℂ) :
    liftH (P₁ := RegionConfig n P₁) (U := RegionConfig n U) (F := RegionConfig n F)
      (K.submatrix (regionUnionEquiv hp.P₀x).symm (regionUnionEquiv hp.P₀x).symm) =
      (localLift (P₀ ∪ x) K).submatrix (SkewPartition.equiv hp).symm
        (SkewPartition.equiv hp).symm := by
  rw [liftH, ← hp.isRegionSplit_H.localLift_submatrix K, submatrix_submatrix]
  rfl

/-- **`f_θ` in the coordinates of Lemma 5.3**: for `h = lift_{P₀ x} K`, the symbol of
Lemma 6.4 is the function `f(s)` of Lemma 5.3 for the transported vector. -/
theorem skewFun_transport (K : Matrix (RegionConfig n (P₀ ∪ x)) (RegionConfig n (P₀ ∪ x)) ℂ)
    (θ : SiteConfig n → ℂ) (s : ℝ) :
    skewFun (hp.transport n θ)
        (K.submatrix (regionUnionEquiv hp.P₀x).symm (regionUnionEquiv hp.P₀x).symm) (s : ℂ) =
      markedScalarSymbol s (P₀ ∪ P₁) (x ∪ U) (localLift (P₀ ∪ x) K) θ := by
  have hP := regionState_posSemidef (P₀ ∪ P₁) (WithLp.toLp 2 θ)
  have hY := regionState_posSemidef (x ∪ U) (WithLp.toLp 2 θ)
  have hneg : -(s : ℂ) = ((-s : ℝ) : ℂ) := by push_cast; ring
  rw [skewFun, margP_transport, margY_transport, hneg,
    cfcC_submatrix_equiv hP.isHermitian, cfcC_submatrix_equiv hP.isHermitian,
    cfcC_submatrix_equiv hY.isHermitian, cfcC_submatrix_equiv hY.isHermitian,
    hp.liftP_eq, hp.liftP_eq, hp.liftY_eq', hp.liftY_eq', hp.liftH_eq]
  simp only [submatrix_mul_equiv]
  rw [transport, star_dotProduct_submatrix_mulVec, markedScalarSymbol, regionPow, regionPow,
    regionPow, regionPow, cfcC_suppPowFun_ofReal hP, cfcC_suppPowFun_ofReal hP,
    cfcC_suppPowFun_ofReal hY, cfcC_suppPowFun_ofReal hY]

theorem star_transport_dotProduct (θ : SiteConfig n → ℂ) :
    star (hp.transport n θ) ⬝ᵥ hp.transport n θ = star θ ⬝ᵥ θ :=
  Fintype.sum_equiv (SkewPartition.equiv hp).symm _ _ fun _ => rfl

/-- **Lemma 5.3 for the symbol of Lemma 6.4** (`05-replicas.tex`, lines 838–843): for
`h = lift_{P₀ x} K` with `0 ≤ K ≤ 1`, `d_h = (dim P₀)(dim x)`, `0 < a` and
`a log (e d_h) ≤ 1/8`, the symbol `f_θ` at `t = a/2` satisfies
`|f_θ| - Re f_θ ≤ C a² log⁴(e d_h) η_θ^{1/8}` on unit vectors, where
`η_θ = I(x:F|U)_θ`. -/
theorem markedScalarSymbol_skew_le
    {K : Matrix (RegionConfig n (P₀ ∪ x)) (RegionConfig n (P₀ ∪ x)) ℂ} (hK0 : 0 ≤ K)
    (hK1 : K ≤ 1) {a : ℝ} (ha : 0 < a)
    (hac : a * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
      Fintype.card (RegionConfig n x))) ≤ 1 / 8) {θ : SiteConfig n → ℂ} (hθ : θ ∈ unitSphere) :
    ‖markedScalarSymbol (a / 2) (P₀ ∪ P₁) (x ∪ U) (localLift (P₀ ∪ x) K) θ‖ -
        (markedScalarSymbol (a / 2) (P₀ ∪ P₁) (x ∪ U) (localLift (P₀ ∪ x) K) θ).re ≤
      skewConst * a ^ 2 * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
        Fintype.card (RegionConfig n x))) ^ 4 * skewEta (hp.transport n θ) ^ (1 / 8 : ℝ) := by
  set φ := regionUnionEquiv (n := n) hp.P₀x
  have hθ' : star (hp.transport n θ) ⬝ᵥ hp.transport n θ = 1 := by
    rw [star_transport_dotProduct, dotProduct_comm]; exact hθ
  have hh0 : 0 ≤ K.submatrix φ.symm φ.symm :=
    nonneg_iff_posSemidef.mpr ((nonneg_iff_posSemidef.mp hK0).submatrix _)
  have hh1 : K.submatrix φ.symm φ.symm ≤ 1 := by
    rw [Matrix.le_iff] at hK1 ⊢
    have : (1 : Matrix (RegionConfig n P₀ × RegionConfig n x) (RegionConfig n P₀ ×
        RegionConfig n x) ℂ) - K.submatrix φ.symm φ.symm = (1 - K).submatrix φ.symm φ.symm := by
      ext i j
      simp [one_apply]
    rw [this]
    exact hK1.submatrix _
  have hcard : (Fintype.card (RegionConfig n P₀ × RegionConfig n x) : ℝ) =
      Fintype.card (RegionConfig n P₀) * Fintype.card (RegionConfig n x) := by
    rw [Fintype.card_prod, Nat.cast_mul]
  have h := conditionalSkew_le hθ' hh0 hh1 ha (by rwa [hcard])
  rw [hcard, hp.skewFun_transport K θ (a / 2)] at h
  exact h

omit [Fintype V] in
theorem continuous_transport :
    Continuous fun θ : SiteConfig n → ℂ => hp.transport n θ :=
  continuous_pi fun _ => continuous_apply _

/-- `θ ↦ η_θ = I(x:F|U)_θ` is continuous on unit vectors. -/
theorem continuousOn_skewEta_transport :
    ContinuousOn (fun θ : SiteConfig n → ℂ => skewEta (hp.transport n θ)) unitSphere := by
  have hc : Continuous fun θ : SiteConfig n → ℂ => rhoW (hp.transport n θ) :=
    (continuous_submatrix _ _).comp (continuous_partialTraceLeft.comp
      (continuous_vecMulVec_self.comp hp.continuous_transport))
  refine continuousOn_condMutualInfo (fun θ => posSemidef_rhoW _) hc.continuousOn
    fun θ hθ => ?_
  rw [trace_rhoW, star_transport_dotProduct, dotProduct_comm]
  exact hθ

/-- **Lemma 6.4, equation `replicas:skew-bound`** (`05-replicas.tex`, lines 640–660 and
838–843): for `h = lift_{P₀ x} K` with `0 ≤ K ≤ 1`, `d_h = (dim P₀)(dim x)`, `0 < a` with
`a log (e d_h) ≤ 1/8` and `t = a/2`, uniformly over symmetric density matrices `σ`,
`Tr σ 𝒟_k ≤ 2 C a² log⁴(e d_h) ∫ η_θ^{1/8} dμ_σ(θ) + o_k(1)`, where
`η_θ = I(x:F|U)_θ` and `C = skewConst`. -/
theorem eventually_re_trace_skewOperator_le [∀ v, NeZero (n v)]
    {K : Matrix (RegionConfig n (P₀ ∪ x)) (RegionConfig n (P₀ ∪ x)) ℂ} (hK0 : 0 ≤ K)
    (hK1 : K ≤ 1) {a : ℝ} (ha : 0 < a)
    (hac : a * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
      Fintype.card (RegionConfig n x))) ≤ 1 / 8) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ∀ (b : SiteConfig n)
      (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
      σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
        ((σ * skewOperator k (markedSimilarity n (a / 2) k (P₀ ∪ P₁) (x ∪ U) F
            (localLift (P₀ ∪ x) K))).trace).re ≤
          2 * skewConst * a ^ 2 * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
            Fintype.card (RegionConfig n x))) ^ 4 *
            (coherentIntegral b σ fun θ =>
              ((skewEta (hp.transport n θ) ^ (1 / 8 : ℝ) : ℝ) : ℂ)).re + ε := by
  set ℓ := Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
    Fintype.card (RegionConfig n x)))
  have hd1 : (1 : ℝ) ≤ Fintype.card (RegionConfig n P₀) * Fintype.card (RegionConfig n x) := by
    have h0 : 1 ≤ Fintype.card (RegionConfig n P₀) := Fintype.card_pos
    have h1 : 1 ≤ Fintype.card (RegionConfig n x) := Fintype.card_pos
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hℓ : 1 ≤ ℓ := one_le_log_exp_mul hd1
  have ha1 : a < 1 := by nlinarith
  have hh : IsSupportedOn (localLift (P₀ ∪ x) K) ((P₀ ∪ P₁) ∪ (x ∪ U)) :=
    (isSupportedOn_localLift K).mono (Finset.union_subset_union Finset.subset_union_left
      Finset.subset_union_left)
  have hsym := hasCoherentSymbol_markedSimilarity (half_pos ha) (by linarith) hp.PY hp.PF hp.YF hh
  set f := markedScalarSymbol (a / 2) (P₀ ∪ P₁) (x ∪ U) (localLift (P₀ ∪ x) K)
  have hfc : ContinuousOn f unitSphere := hsym.continuousOn
  set g : (SiteConfig n → ℂ) → ℂ := fun θ => ((2 * (‖f θ‖ - (f θ).re) : ℝ) : ℂ)
  set η : (SiteConfig n → ℂ) → ℝ := fun θ => skewEta (hp.transport n θ) ^ (1 / 8 : ℝ)
  have hηc : ContinuousOn η unitSphere :=
    hp.continuousOn_skewEta_transport.rpow_const fun _ _ => Or.inr (by norm_num)
  have hgc : ContinuousOn g unitSphere :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.mul
      (hfc.norm.sub (Complex.continuous_re.comp_continuousOn hfc)))
  have hGc : ContinuousOn (fun θ => ((2 * skewConst * a ^ 2 * ℓ ^ 4 : ℝ) : ℂ) * (η θ : ℂ))
      unitSphere :=
    continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hηc)
  filter_upwards [eventually_norm_trace_skewOperator_markedSimilarity_sub_le (half_pos ha)
    (by linarith) hp.PY hp.PF hp.YF hh hε] with k hk b σ hσp hσt hσ
  have h1 := hk b σ hσp hσt hσ
  have h2 : (coherentIntegral b σ g).re ≤ (coherentIntegral b σ
      (fun θ => ((2 * skewConst * a ^ 2 * ℓ ^ 4 : ℝ) : ℂ) * (η θ : ℂ))).re := by
    refine re_coherentIntegral_le hσp b hgc hGc fun θ hθ => ?_
    simp only [g, Complex.ofReal_re, ← Complex.ofReal_mul, η]
    have := hp.markedScalarSymbol_skew_le hK0 hK1 ha hac hθ
    nlinarith
  rw [coherentIntegral_const_mul, Complex.re_ofReal_mul] at h2
  have h3 : ((σ * skewOperator k (markedSimilarity n (a / 2) k (P₀ ∪ P₁) (x ∪ U) F
      (localLift (P₀ ∪ x) K))).trace).re ≤ (coherentIntegral b σ g).re + ε := by
    have := (Complex.re_le_norm _).trans h1
    rw [Complex.sub_re] at this
    linarith
  linarith

end SkewPartition

end TensorPower
