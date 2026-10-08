/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RelativePin
import QICLean.Representation.SkewSymbolBound
import QICLean.Entropy.MovementEtaRegional

/-!
# Lemmas 6.3 and 6.4 with the entropy in region form

Lemma 6.3 (`lem:relative-pin`, `05-replicas.tex`, lines 486–505) and the skew bound of
Lemma 6.4 (`lem:symbol`, display `replicas:skew-bound`, lines 640–660) of the area-law paper
(*A two-dimensional area law from a global spectral gap*) state their exponent as
`η_θ = S_θ(x|P) + S_θ(x|Y₀) = I_θ(x:F|P) = I_θ(x:F|Y₀)`. The formal statements
`TensorPower.relativePin` and `TensorPower.SkewPartition.eventually_re_trace_skewOperator_le` write
it in coordinates: as the exponent `Entropy.movementEta` of Lemma 5.1, and as
`I(x:F|U)` of the transported vector. This file restates both with
`η_θ = Entropy.regionalMovementEta P x Y₀ θ`, and proves the variants with the two outer parts
exchanged, which both lemmas assert (`05-replicas.tex`, lines 502–503 and 657).

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.leafMetric_comm`, `TensorPower.markedSimilarity_comm` — the partition metric is
  symmetric in the outer parts.
* `TensorPower.relativePin_regionalMovementEta` — Lemma 6.3 with `η_θ = S_θ(x|P) + S_θ(x|Y₀)`.
* `TensorPower.relativePin_toF` — Lemma 6.3 for a move to `F`.
* `TensorPower.SkewPartition.skewEta_transport` — `I(x:F|U)` of the transported vector is
  `S_θ(x|P) + S_θ(x|U)`.
* `TensorPower.SkewPartition.eventually_re_trace_skewOperator_le_regionalMovementEta` — the skew
  bound with `η_θ` in region form, and `..._swap` with the outer parts exchanged.
-/

open Matrix Entropy Entropy.ConditionalSkew Entropy.MarginalPhase PermutationRepresentation
open scoped Kronecker ComplexOrder MatrixOrder

namespace TensorPower

universe u

/-! ### Symmetry in the outer parts -/

section Symmetry

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

/-- `A_k^{1/2}(F, Y, P) = A_k^{1/2}(P, Y, F)`: the factors `W_P^{-1}` and `W_F^{-1}` commute
(`05-replicas.tex`, line 461). -/
theorem leafRoot_comm {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V} (hPF : Disjoint P F) :
    leafRoot n t k F Y P = leafRoot n t k P Y F := by
  have hPF' : Commute (replicaMetric (fun v => Fin (n v)) t k P)⁻¹
      (replicaMetric (fun v => Fin (n v)) t k F)⁻¹ := by
    rw [replicaMetric_inv_eq ht, replicaMetric_inv_eq ht]
    exact commute_replicaMetric_of_disjoint' k hPF _ _
  rw [leafRoot, leafRoot, hPF'.eq]

/-- The partition metric is symmetric in the two outer parts: `A_k(F, Y, P) = A_k(P, Y, F)`. -/
theorem leafMetric_comm {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V} (hPF : Disjoint P F) :
    leafMetric n t k F Y P = leafMetric n t k P Y F := by
  rw [leafMetric, leafMetric, leafRoot_comm ht k hPF]

theorem markedSimilarity_comm {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P Y F : Finset V}
    (hPF : Disjoint P F) (h : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    markedSimilarity n t k F Y P h = markedSimilarity n t k P Y F h := by
  rw [markedSimilarity, markedSimilarity, leafMetric_comm ht k hPF]

end Symmetry

/-! ### The relative coherent pin -/

/-- **Lemma 6.3, the relative coherent pin, with `η_θ` in region form** (`05-replicas.tex`,
equation `replicas:relative-pin`, lines 486–505). Let `P, x, Y₀, F` partition the sites,
`0 < t ≤ 1`, `a = 2t` with `a log(e dim x) ≤ c`. There is a polynomial `K (k + 2)^N`, uniform in
`θ`, such that
`C_{x,k} ≥ (K (k + 2)^N)^{-1} exp{k a [η_θ - C a^{1/4} log²(e dim x)]} P_{θ,k}` with
`η_θ = S_θ(x|P) + S_θ(x|Y₀)`. By `Entropy.regionalMovementEta_eq_cmi_left` and
`Entropy.regionalMovementEta_eq_cmi_right` this is also `I_θ(x:F|P) = I_θ(x:F|Y₀)`. The
hypothesis `t ≤ 1` replaces the paper's standing `t < 1/4`; see `TensorPower.relativePin`. -/
theorem relativePin_regionalMovementEta :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
        {P x Y F : Finset V} (_ : FourPartition P x Y F) {t : ℝ}, 0 < t → t ≤ 1 →
        2 * t * Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ≤ c →
        ∃ K N : ℝ, 0 < K ∧ ∀ (k : ℕ) (θ : EuclideanSpace ℂ (SiteConfig n)), ‖θ‖ = 1 →
          ∀ w : Config k (fun v => Fin (n v)) → ℂ,
            ‖star (tensorVec k θ.ofLp) ⬝ᵥ w‖ ^ 2 *
              Real.exp (k * (2 * t) * (regionalMovementEta P x Y θ -
                C * (2 * t) ^ (1 / 4 : ℝ) *
                  Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ^ 2)) ≤
            K * ((k : ℝ) + 2) ^ N * (star w ⬝ᵥ (relativeMetric n t k P x Y F *ᵥ w)).re := by
  obtain ⟨C, c, hC, hc, H⟩ := relativePin.{u}
  refine ⟨C, c, hC, hc, fun h t ht0 ht1 hsmall => ?_⟩
  obtain ⟨K, N, hK, H'⟩ := H h ht0 ht1 hsmall
  refine ⟨K, N, hK, fun k θ hθ w => ?_⟩
  rw [← h.movementEta_frameVector θ]
  exact H' k θ hθ w

/-- **Lemma 6.3 for a move to `F`** (`05-replicas.tex`, lines 502–503: "the same statement
holds for a move to `F` after exchanging the outer parts"). With `A_k = A_k(P, xY₀, F)`,
`B_k = A_k(P, Y₀, Fx)` and `η_θ = S_θ(x|F) + S_θ(x|Y₀)`,
`A_k^{-1/2} B_k A_k^{-1/2} ≥ (K (k + 2)^N)^{-1} exp{k a [η_θ - C a^{1/4} log²(e dim x)]} P_{θ,k}`.
-/
theorem relativePin_toF :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
        {P x Y F : Finset V} (_ : FourPartition P x Y F) {t : ℝ}, 0 < t → t ≤ 1 →
        2 * t * Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ≤ c →
        ∃ K N : ℝ, 0 < K ∧ ∀ (k : ℕ) (θ : EuclideanSpace ℂ (SiteConfig n)), ‖θ‖ = 1 →
          ∀ w : Config k (fun v => Fin (n v)) → ℂ,
            ‖star (tensorVec k θ.ofLp) ⬝ᵥ w‖ ^ 2 *
              Real.exp (k * (2 * t) * (regionalMovementEta F x Y θ -
                C * (2 * t) ^ (1 / 4 : ℝ) *
                  Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ^ 2)) ≤
            K * ((k : ℝ) + 2) ^ N * (star w ⬝ᵥ
              (((CFC.sqrt (leafMetric n t k P (x ∪ Y) F))⁻¹ * leafMetric n t k P Y (F ∪ x) *
                (CFC.sqrt (leafMetric n t k P (x ∪ Y) F))⁻¹) *ᵥ w)).re := by
  obtain ⟨C, c, hC, hc, H⟩ := relativePin_regionalMovementEta.{u}
  refine ⟨C, c, hC, hc, ?_⟩
  intro V _ _ n _ P x Y F h t ht0 ht1 hsmall
  obtain ⟨K, N, hK, H'⟩ := H h.swap ht0 ht1 hsmall
  refine ⟨K, N, hK, fun k θ hθ w => ?_⟩
  have e : relativeMetric n t k F x Y P =
      (CFC.sqrt (leafMetric n t k P (x ∪ Y) F))⁻¹ * leafMetric n t k P Y (F ∪ x) *
        (CFC.sqrt (leafMetric n t k P (x ∪ Y) F))⁻¹ := by
    rw [relativeMetric, leafMetric_comm ht0.le k h.PF,
      leafMetric_comm ht0.le k (Finset.disjoint_union_right.mpr ⟨h.PF, h.Px⟩)]
  rw [← e]
  exact H' k θ hθ w

/-! ### The skew bound -/

namespace SkewPartition

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
variable {P₀ P₁ x U F : Finset V} (hp : SkewPartition P₀ P₁ x U F)
include hp

omit [Fintype V] in
theorem Px : Disjoint (P₀ ∪ P₁) x :=
  Finset.disjoint_of_subset_right Finset.subset_union_left hp.PY

omit [Fintype V] [DecidableEq V] hp in
/-- `((P₀ P₁) x)(U F) ≃ (P₀ P₁)((x U) F)`. -/
def regroupUF {A₀ A₁ X' U' F' : Type*} :
    ((A₀ × A₁) × X') × (U' × F') ≃ (A₀ × A₁) × ((X' × U') × F') where
  toFun r := (r.1.1, ((r.1.2, r.2.1), r.2.2))
  invFun q := ((q.1, q.2.1.1), (q.2.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
theorem isRegionSplit_Px : IsRegionSplit ((P₀ ∪ P₁) ∪ x)
    ((regionUnionEquiv hp.Px).trans (Equiv.prodCongr (regionUnionEquiv hp.P₀P₁) (Equiv.refl _)))
    ((SkewPartition.equiv (n := n) hp).trans regroupUF.symm) where
  fst _ := rfl
  snd σ τ := by
    change ((fun v : {v // v ∈ U} => σ v), (fun v : {v // v ∈ F} => σ v)) =
      ((fun v : {v // v ∈ U} => τ v), (fun v : {v // v ∈ F} => τ v)) ↔ _
    simp only [Prod.mk.injEq, restrict_eq_iff]
    constructor
    · rintro ⟨hU, hF⟩ v hv
      simp only [Finset.mem_union, not_or] at hv
      rcases hp.mem_cases v with h | h | h | h | h
      · exact absurd h hv.1.1
      · exact absurd h hv.1.2
      · exact absurd h hv.2
      · exact hU v h
      · exact hF v h
    · intro h
      have nm := fun v => hp.not_mem_of_mem (v := v)
      refine ⟨fun v hv => h v ?_, fun v hv => h v ?_⟩ <;>
        simp only [Finset.mem_union, not_or] <;> have := nm v <;> tauto

omit [Fintype V] in
theorem marginalUF_rhoW_transport (θ : SiteConfig n → ℂ) :
    marginalUF (rhoW (hp.transport n θ)) =
      partialTraceLeft
        (vecMulVec (θ ∘ ((SkewPartition.equiv (n := n) hp).trans regroupUF.symm).symm)
          (star (θ ∘ ((SkewPartition.equiv (n := n) hp).trans regroupUF.symm).symm))) := by
  ext ⟨u, f⟩ ⟨u', f'⟩
  simp only [marginalUF, rhoW, margW, partialTraceLeft_apply, submatrix_apply, vecMulVec_apply,
    Pi.star_apply, Function.comp_apply, Fintype.sum_prod_type, transport, Equiv.symm_trans_apply,
    Equiv.symm_symm, assocE, Equiv.prodAssoc_symm_apply, regroupUF, Equiv.coe_fn_mk]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [Finset.sum_comm]

/-- **`η_θ` of the skew bound in region form**: `I(x:F|U)` of the transported vector is
`S_θ(x|P) + S_θ(x|U)` with `P = P₀ ∪ P₁` (`05-replicas.tex`, lines 645–647; the two forms
agree by purity, `04-conditional.tex`, lines 122–124 and 138–139). -/
theorem skewEta_transport (θ : SiteConfig n → ℂ) :
    skewEta (hp.transport n θ) = regionalMovementEta (P₀ ∪ P₁) x U (WithLp.toLp 2 θ) := by
  set θt := hp.transport n θ
  set w := θ ∘ ((SkewPartition.equiv (n := n) hp).trans regroupUF.symm).symm
  have eXU : ∀ hh, _root_.vonNeumannEntropy (marginalXU (rhoW θt)) hh =
      regionEntropy (x ∪ U) (WithLp.toLp 2 θ) := by
    intro hh
    rw [_root_.vonNeumannEntropy_congr (by rw [marginalXU_rhoW, hp.margY_transport]) hh
      ((regionState_isHermitian _ _).submatrix _)]
    exact vonNeumannEntropy_submatrix_equiv _ _ _
  have eU : ∀ hh, _root_.vonNeumannEntropy (marginalU (rhoW θt)) hh =
      regionEntropy U (WithLp.toLp 2 θ) := fun hh =>
    _root_.vonNeumannEntropy_congr (by
      rw [marginalU, marginalXU_rhoW, hp.margY_transport, partialTraceLeft_regionState_union]) hh _
  have eW : ∀ hh, _root_.vonNeumannEntropy (rhoW θt) hh =
      regionEntropy (P₀ ∪ P₁) (WithLp.toLp 2 θ) := by
    intro hh
    have h1 : _root_.vonNeumannEntropy (rhoW θt) hh =
        _root_.vonNeumannEntropy (partialTraceLeft (vecMulVec θt (star θt)))
          (posSemidef_vecMulVec_self_star θt).partialTraceLeft.isHermitian :=
      vonNeumannEntropy_submatrix_equiv assocE.symm _ _
    rw [h1, ← pure_marginal_entropy_eq, _root_.vonNeumannEntropy_congr
      (show partialTraceRight (vecMulVec θt (star θt)) = _ from hp.margP_transport θ) _
      ((regionState_isHermitian _ _).submatrix _)]
    exact vonNeumannEntropy_submatrix_equiv _ _ _
  have eUF : ∀ hh, _root_.vonNeumannEntropy (marginalUF (rhoW θt)) hh =
      regionEntropy ((P₀ ∪ P₁) ∪ x) (WithLp.toLp 2 θ) := by
    intro hh
    rw [_root_.vonNeumannEntropy_congr (hp.marginalUF_rhoW_transport θ) hh
      (posSemidef_vecMulVec_self_star w).partialTraceLeft.isHermitian,
      ← pure_marginal_entropy_eq, _root_.vonNeumannEntropy_congr
        (hp.isRegionSplit_Px.partialTraceRight_vecMulVec θ) _
        ((regionState_isHermitian _ _).submatrix _)]
    exact vonNeumannEntropy_submatrix_equiv _ _ _
  have hρ := posSemidef_rhoW θt
  have a1 := eXU (hρ.submatrix assocE).partialTraceRight.isHermitian
  have a2 := eUF hρ.partialTraceLeft.isHermitian
  have a3 := eU (hρ.submatrix assocE).partialTraceRight.partialTraceLeft.isHermitian
  have a4 := eW hρ.isHermitian
  rw [skewEta, condMutualInfo, regionalMovementEta]
  linarith

/-- **Lemma 6.4, equation `replicas:skew-bound`, with `η_θ` in region form**
(`05-replicas.tex`, lines 640–660): for `h = lift_{P₀ x} K` with `0 ≤ K ≤ 1`,
`d_h = (dim P₀)(dim x)`, `0 < a` with `a log (e d_h) ≤ 1/8` and `t = a/2`, uniformly over
symmetric density matrices `σ`,
`Tr σ 𝒟_k ≤ 2 C a² log⁴(e d_h) ∫ η_θ^{1/8} dμ_σ(θ) + o_k(1)` with
`η_θ = S_θ(x|P) + S_θ(x|U)`, `P = P₀ ∪ P₁` and `C = skewConst`. -/
theorem eventually_re_trace_skewOperator_le_regionalMovementEta [∀ v, NeZero (n v)]
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
              ((regionalMovementEta (P₀ ∪ P₁) x U (WithLp.toLp 2 θ) ^ (1 / 8 : ℝ) : ℝ) :
                ℂ)).re + ε := by
  simpa only [hp.skewEta_transport] using
    hp.eventually_re_trace_skewOperator_le hK0 hK1 ha hac hε

/-- **Lemma 6.4, the skew bound with the outer parts exchanged** (`05-replicas.tex`, line 657,
and lines 842–843). For the partition metric `A_k(F, x ∪ U, P₀ ∪ P₁)`, whose second outer part
`P₀ ∪ P₁` contains the support `P₀` of `h` outside the middle part, the bound holds with
`η_θ = S_θ(x|P₀ ∪ P₁) + S_θ(x|U)`. -/
theorem eventually_re_trace_skewOperator_le_swap [∀ v, NeZero (n v)]
    {K : Matrix (RegionConfig n (P₀ ∪ x)) (RegionConfig n (P₀ ∪ x)) ℂ} (hK0 : 0 ≤ K)
    (hK1 : K ≤ 1) {a : ℝ} (ha : 0 < a)
    (hac : a * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
      Fintype.card (RegionConfig n x))) ≤ 1 / 8) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, ∀ (b : SiteConfig n)
      (σ : Matrix (Fin k → SiteConfig n) (Fin k → SiteConfig n) ℂ), σ.PosSemidef →
      σ.trace = 1 → (∀ π, permOp (copyPerm (SiteConfig n) k) π * σ = σ) →
        ((σ * skewOperator k (markedSimilarity n (a / 2) k F (x ∪ U) (P₀ ∪ P₁)
            (localLift (P₀ ∪ x) K))).trace).re ≤
          2 * skewConst * a ^ 2 * Real.log (Real.exp 1 * (Fintype.card (RegionConfig n P₀) *
            Fintype.card (RegionConfig n x))) ^ 4 *
            (coherentIntegral b σ fun θ =>
              ((regionalMovementEta (P₀ ∪ P₁) x U (WithLp.toLp 2 θ) ^ (1 / 8 : ℝ) : ℝ) :
                ℂ)).re + ε := by
  have hc : ∀ (k : ℕ) (h : Matrix (SiteConfig n) (SiteConfig n) ℂ),
      markedSimilarity n (a / 2) k F (x ∪ U) (P₀ ∪ P₁) h =
        markedSimilarity n (a / 2) k (P₀ ∪ P₁) (x ∪ U) F h := fun k h =>
    markedSimilarity_comm (by positivity) k hp.PF h
  simp only [hc]
  exact hp.eventually_re_trace_skewOperator_le_regionalMovementEta hK0 hK1 ha hac hε

end SkewPartition

end TensorPower
