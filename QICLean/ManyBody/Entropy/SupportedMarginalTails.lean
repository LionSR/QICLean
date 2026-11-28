/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.Surprisal.MarginalTails
import QICLean.ManyBody.Sites.SupportedDecomposition
import QICLean.Analysis.Norm.L2OpNormReindex
import QICLean.ManyBody.Sites.Cut
import QICLean.ManyBody.Sites.Support
import QICLean.ManyBody.Sites.RegionState
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.ManyBody.Sites.Lattice.ChainCut

/-!
# Marginal tails for interactions with designated supports

Let `𝓗 = ⊗_{v ∈ V} ℂ^{n_v}` be a finite tensor product with arbitrary local dimensions.
An operator is supported on `D ⊆ V` when it acts as the identity on the sites outside
`D`: its matrix elements vanish between configurations that differ outside `D` and do not
depend on the common values there. For a bipartition `B ⊔ Bᶜ = V`, an operator supported
on `D` is one-sided when `D ⊆ B` or `D ⊆ Bᶜ`. Otherwise, the matrix units on `D ∩ B` write
it as a sum of at most `d²` products `c ⊗ d'` with `‖c‖ ≤ 1` and `‖d'‖` at most its norm,
where `d = ∏_{v ∈ D} n_v`.

With these decompositions, `QICLean.Entropy.Surprisal.MarginalTails` gives Lemma 3.1 of the
area-law manuscript in its stated form: designated supports, `d_i = ∏_{v ∈ D_i} dim 𝓗_v`,
and `ℬ = 1 + ∑_{i ∈ I×} log² (e d_i)` over the terms whose support meets both sides.

The budget `ManyBody.cutLogBudget` of the crossing terms and the support dimension
`Entropy.supportDim` are defined in `QICLean.ManyBody.Sites.Cut`.

## Main results

* `ManyBody.IsSupportedOn.isOneSided_of_subset`, `ManyBody.IsSupportedOn.isOneSided_of_disjoint`.
* `ManyBody.IsSupportedOn.hasProductDecomposition`: the matrix-unit decomposition.
* `Entropy.log_surprisalMoment_cut_le`, `Entropy.surprisalTail_cut_le`: Lemma 3.1.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Lemma 3.1 (`lem:tail`),
  `02-initial.tex`, lines 34–69 and 126–133.

Independently written from the manuscript; no upstream Lean proof text is reused.

Moved from TNLean, `TNLean/MPS/AreaLaw/Entropy/RenyiEntropy.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

section Main

variable {ι : Type*} [Fintype ι]

variable {h : ι → Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v))
    ℂ} {D : ι → Finset V} {c₀ E₀ g₀ : ℝ}
  {Ψ : EuclideanSpace ℂ (∀ v, Fin (n v))} {B : Finset V}
  {ρ : Matrix ((v : {v // v ∈ B}) → Fin (n v)) ((v : {v // v ∈ B}) → Fin (n v)) ℂ}

theorem norm_cutVector (B : Finset V) (Ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ‖ManyBody.cutVector B Ψ‖ = ‖Ψ‖ :=
  ManyBody.norm_cutVector (X := fun v ↦ Fin (n v)) B Ψ

/-- Transport of all hypotheses of Lemma 3.1 to cut coordinates. -/
private theorem cut_transport (hsupp : ∀ i, ManyBody.IsSupportedOn (h i) (D i))
    (hherm : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ c₀) (hΨ : ‖Ψ‖ = 1)
    (heig : toEuclideanLin (∑ i, h i) Ψ = (E₀ : ℂ) • Ψ)
    (hgap : ((∑ i, h i) - (E₀ : ℂ) • 1 -
      (g₀ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ψ) (star (WithLp.ofLp Ψ)))).PosSemidef) :
    (∀ i, (ManyBody.cutOperator B (h i)).IsHermitian) ∧ (∀ i, ‖ManyBody.cutOperator B (h i)‖ ≤ c₀) ∧
      (∀ i ∉ ManyBody.crossingTerms D B, Matrix.IsOneSided (ManyBody.cutOperator B (h i))) ∧
      (∀ i ∈ ManyBody.crossingTerms D B, 1 ≤ supportDim n (D i)) ∧
      (∀ i ∈ ManyBody.crossingTerms D B,
        Matrix.HasProductDecomposition (ManyBody.cutOperator B (h i)) c₀ (supportDim n (D i) ^ 2)) ∧
      ‖ManyBody.cutVector B Ψ‖ = 1 ∧
      toEuclideanLin (∑ i, ManyBody.cutOperator B (h i)) (ManyBody.cutVector B Ψ) =
        (E₀ : ℂ) • ManyBody.cutVector B Ψ ∧
      ((∑ i, ManyBody.cutOperator B (h i)) - (E₀ : ℂ) • 1 - (g₀ : ℂ) • (1 -
        vecMulVec (WithLp.ofLp (ManyBody.cutVector B Ψ))
          (star (WithLp.ofLp (ManyBody.cutVector B Ψ))))).PosSemidef := by
  classical
  have hΨ0 : Ψ ≠ 0 := fun h0 ↦ by simp [h0] at hΨ
  obtain ⟨σ₀, -⟩ : ∃ σ, Ψ σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hΨ0 (by ext σ; simp [hcon σ])
  have hn : ∀ v, 1 ≤ n v := fun v ↦ Nat.one_le_iff_ne_zero.mpr fun h0 ↦ by
    have hv := σ₀ v
    rw [h0] at hv
    exact hv.elim0
  have hsum : ∑ i, ManyBody.cutOperator B (h i)
      = reindex (ManyBody.cutEquiv (fun v ↦ Fin (n v)) B) (ManyBody.cutEquiv (fun v ↦ Fin (n v))
      B) (∑ i, h i) := by
    ext a b
    simp [Matrix.sum_apply]
  refine ⟨fun i ↦ (hherm i).submatrix _, fun i ↦ by
    rw [Matrix.l2_opNorm_reindex_equiv]; exact hnorm i, fun i hi ↦ ?_, fun i _ ↦ ?_,
    fun i _ ↦ (hsupp i).hasProductDecomposition σ₀ (fun v _ ↦ hn v) (hnorm i),
    by rw [norm_cutVector, hΨ], ?_, ?_⟩
  · simp only [ManyBody.crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
      not_exists, not_not] at hi
    by_cases hDB : ∃ v ∈ D i, v ∈ B
    · exact (hsupp i).isOneSided_of_subset (fun v hv ↦ hi hDB v hv) (ManyBody.cutEquiv
        (fun v ↦ Fin (n v)) B σ₀).2
    · push Not at hDB
      exact (hsupp i).isOneSided_of_disjoint (Finset.disjoint_left.mpr hDB) (ManyBody.cutEquiv
          (fun v ↦ Fin (n v)) B σ₀).1
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ ↦
      Nat.one_le_iff_ne_zero.mp (hn v))
  · rw [hsum]
    ext x
    have h1 := congrArg (fun φ : EuclideanSpace ℂ (∀ v, Fin (n v)) ↦ φ
        ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) B).symm x)) heig
    simp only [toLpLin_apply, PiLp.smul_apply, smul_eq_mul] at h1 ⊢
    rw [reindex_apply, submatrix_mulVec_equiv]
    have hcomp : (WithLp.ofLp (ManyBody.cutVector B Ψ)) ∘ (ManyBody.cutEquiv (fun v ↦ Fin (n v))
        B).symm.symm = WithLp.ofLp Ψ := by
      funext σ
      simp only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    rw [hcomp]
    simpa using h1
  · have h1 := (posSemidef_submatrix_equiv (ManyBody.cutEquiv (fun v ↦ Fin (n v)) B).symm).mpr hgap
    convert h1 using 1
    rw [hsum]
    ext a b
    simp [reindex_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply, vecMulVec_apply]

/-- **Lemma 3.1, moment bound.** Let `𝓗 = ⊗_{v ∈ V} ℂ^{n_v}` and `H = ∑_i h_i`, where
each `h_i` is Hermitian, supported on `D_i`, and `‖h_i‖ ≤ c₀` with `c₀ ≥ 0`. Let `Ψ` be a
unit vector with `H Ψ = E₀ Ψ` and `H - E₀ ≥ g₀ (1 - |Ψ⟩⟨Ψ|)`, `g₀ > 0`. For a bipartition
`B ⊔ Bᶜ = V`, let `ρ = Tr_{Bᶜ} |Ψ⟩⟨Ψ|`, `d_i = ∏_{v ∈ D_i} n_v`,
`ℬ = 1 + ∑_{i ∈ I×} log² (e d_i)` over the terms whose support meets both sides, and
`ϑ = c₀ / g₀`. Then the surprisal of the eigenvalues of `ρ` satisfies
`log E e^{uK} ≤ u S(ρ) + 512 e ϑ ℬ u²` for `|u| ≤ 1/(32 √((1 + ϑ) ℬ))`.

Area-law manuscript, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–63,
`eq:initial-tail-mgf`. The one-dimensional ground space, ground energy and gap of the
source are expressed by the eigenvector equation and the operator gap inequality. -/
theorem log_surprisalMoment_cut_le (hsupp : ∀ i, ManyBody.IsSupportedOn (h i) (D i))
    (hherm : ∀ i, (h i).IsHermitian) (hc₀ : 0 ≤ c₀) (hnorm : ∀ i, ‖h i‖ ≤ c₀) (hΨ : ‖Ψ‖ = 1)
    (hg₀ : 0 < g₀) (heig : toEuclideanLin (∑ i, h i) Ψ = (E₀ : ℂ) • Ψ)
    (hgap : ((∑ i, h i) - (E₀ : ℂ) • 1 -
      (g₀ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ψ) (star (WithLp.ofLp Ψ)))).PosSemidef)
    (hρdef : partialTraceRight (vecMulVec (WithLp.ofLp (ManyBody.cutVector B Ψ))
      (star (WithLp.ofLp (ManyBody.cutVector B Ψ)))) = ρ) (hρ : ρ.IsHermitian) {u : ℝ}
    (hu : |u| ≤ tailRadius (c₀ / g₀)
        (ManyBody.cutLogBudget D n B)) :
    Real.log (surprisalMoment hρ.eigenvalues u) ≤
      u * vonNeumannEntropy ρ hρ +
        512 * Real.exp 1 * (c₀ / g₀) * ManyBody.cutLogBudget D n B * u ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    cut_transport (B := B) hsupp hherm hnorm hΨ heig hgap
  exact log_surprisalMoment_eigenvalues_le h1 hc₀ h2 h3 h4 h5 h6 hg₀ h7 h8 hρdef hρ hu

/-- **Lemma 3.1, tail bound.** Under the hypotheses of `log_surprisalMoment_cut_le`, for
every real `w` (the manuscript states `w ≥ 0`),
`Pr {|K - S(ρ)| > w} ≤ min {1, 2 e^{e/2} exp (-w / (32 √((1 + ϑ) ℬ)))}`.

Area-law manuscript, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 64–69,
`eq:initial-tail-probability`. -/
theorem surprisalTail_cut_le (hsupp : ∀ i, ManyBody.IsSupportedOn (h i) (D i))
    (hherm : ∀ i, (h i).IsHermitian) (hc₀ : 0 ≤ c₀) (hnorm : ∀ i, ‖h i‖ ≤ c₀) (hΨ : ‖Ψ‖ = 1)
    (hg₀ : 0 < g₀) (heig : toEuclideanLin (∑ i, h i) Ψ = (E₀ : ℂ) • Ψ)
    (hgap : ((∑ i, h i) - (E₀ : ℂ) • 1 -
      (g₀ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ψ) (star (WithLp.ofLp Ψ)))).PosSemidef)
    (hρdef : partialTraceRight (vecMulVec (WithLp.ofLp (ManyBody.cutVector B Ψ))
      (star (WithLp.ofLp (ManyBody.cutVector B Ψ)))) = ρ) (hρ : ρ.IsHermitian) (w : ℝ) :
    surprisalTail hρ.eigenvalues (vonNeumannEntropy ρ hρ) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) * Real.exp (-(w / (32 * Real.sqrt
        ((1 + c₀ / g₀) * ManyBody.cutLogBudget D n B))))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    cut_transport (B := B) hsupp hherm hnorm hΨ heig hgap
  exact surprisalTail_eigenvalues_le h1 hc₀ h2 h3 h4 h5 h6 hg₀ h7 h8 hρdef hρ w

end Main

end Entropy

section

open ManyBody (interval ChainInteraction ChainSupport)

noncomputable section

section

/-- Jensen's inequality for the exponential gives the lower log-moment bound.
Source: the one-dimensional note, `part1_arealaw.tex`, `rem:renyi`, lines 280–286. -/
private theorem mul_entropy_le_log_surprisalMoment {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) (u : ℝ) :
    u * (∑ i, Real.negMulLog (p i)) ≤ Real.log (Entropy.surprisalMoment p u) := by
  have h := (convexOn_exp).map_sum_le (fun i (_ : i ∈ Finset.univ) ↦ hp i) hs
    (fun i _ ↦ Set.mem_univ (u * -Real.log (p i)))
  have h' : Real.exp (u * ∑ i, Real.negMulLog (p i)) ≤ Entropy.surprisalMoment p u := by
    simpa [smul_eq_mul, Entropy.surprisalMoment, Real.negMulLog, Finset.mul_sum,
      mul_neg, mul_assoc, mul_left_comm] using h
  exact (Real.le_log_iff_exp_le (Entropy.surprisalMoment_pos hp hs u)).mpr h'

open Matrix

open ManyBody (IsGapped groundSpace)

open scoped ComplexOrder Matrix.Norms.L2Operator

/-- The physical log-moment bound applied to the regional state.
Source: the one-dimensional note, `part1_arealaw.tex`, `eq:mgf`, lines 157–166. -/
private theorem ManyBody.ChainInteraction.log_surprisalMoment_region_le
    {L q R : ℕ} {J Δ : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (X : Finset (Fin L)) {u : ℝ}
    (hu : |u| ≤ Entropy.tailRadius (J / Δ)
      (ManyBody.cutLogBudget (fun Y : ChainSupport L R ↦ Y.1) (fun _ ↦ q) X)) :
    Real.log (Entropy.surprisalMoment
      (ManyBody.regionState_isHermitian (X := fun _ ↦ Fin q) X Ω).eigenvalues u) ≤
    u * ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω X +
      512 * Real.exp 1 * (J / Δ) *
        ManyBody.cutLogBudget (fun Y : ChainSupport L R ↦ Y.1) (fun _ ↦ q) X * u ^ 2 := by
  have heig : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω :=
    ManyBody.mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  have hgap := hgap.posSemidef_sub_smul_one
      (ManyBody.Interaction.isHermitian_hamiltonian hh) hΩ hspan
  exact Entropy.log_surprisalMoment_cut_le (n := fun _ : Fin L ↦ q) (B := X)
    h.mem hh hJ hhJ hΩ hΔ heig hgap (ManyBody.regionState_eq_partialTraceRight_cutVector X Ω).symm
    (ManyBody.regionState_isHermitian X Ω) hu

/-- Increasing the cut budget decreases the admissible moment radius.
Source: the one-dimensional note, `part1_arealaw.tex`, `eq:theta`, lines 152–155. -/
private theorem tailRadius_anti_budget {θ B B' : ℝ} (hθ : 0 ≤ θ) (hB : 1 ≤ B) (hBB' : B ≤ B') :
    Entropy.tailRadius θ B' ≤ Entropy.tailRadius θ B := by
  unfold Entropy.tailRadius
  gcongr

/-- Near-one Rényi entropies of an interval in the original gapped chain.
The entropy at order one is the existing regional von Neumann entropy.
The local function `H` is defined by the existing surprisal moment; at every
positive order other than one it is exactly the logarithm of the sum of the
eigenvalues to that order, divided by one minus the order. Zero eigenvalues
contribute zero. The final equality identifies the spectral power formula throughout
the stated interval, with the von Neumann convention at order one.
No invertibility or rank assumption is imposed.

Source: the one-dimensional note, `part1_arealaw.tex`, `rem:renyi`,
lines 280–286, with `eq:theta` and `eq:mgf`, lines 152–166.
The source explicitly restricts to the contiguous chain at lines 91–93. -/
theorem ManyBody.ChainInteraction.near_one_renyi_entropy_interval_bounds
    {L q R : ℕ} {J Δ : ℝ}
    (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hq : 1 ≤ q) (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (l r : ℕ) :
    let X := interval L l r
    let p := (ManyBody.regionState_isHermitian
      (X := fun _ ↦ Fin q) X Ω).eigenvalues
    let S := ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω X
    let u₀ := Entropy.tailRadius (J / Δ) (ManyBody.chainBudgetConst q R)
    let H : ℝ → ℝ := fun α ↦
      if α = 1 then S
      else Real.log (Entropy.surprisalMoment p (1 - α)) / (1 - α)
    H 1 = S ∧
      ∀ α : ℝ, 1 - u₀ ≤ α → α ≤ 1 →
        S ≤ H α ∧
        H α ≤ S + 512 * Real.exp 1 * (J / Δ) *
          ManyBody.chainBudgetConst q R * (1 - α) ∧
        |H α - S| ≤ 16 * Real.exp 1 *
          Real.sqrt ((1 + J / Δ) * ManyBody.chainBudgetConst q R) ∧
        H α = if α = 1 then S else Real.log (∑ i, p i ^ α) / (1 - α) := by
  dsimp only
  refine ⟨ite_eq_left rfl, ?_⟩
  intro α hαlo hαhi
  have hθ : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
  have hB := ManyBody.one_le_chainBudgetConst q R
  have hs : 1 ≤ Real.sqrt ((1 + J / Δ) * ManyBody.chainBudgetConst q R) :=
    Real.one_le_sqrt.mpr (by nlinarith [mul_nonneg hθ (zero_le_one.trans hB)])
  have hrad : Entropy.tailRadius (J / Δ) (ManyBody.chainBudgetConst q R) ≤ 1 / 32 := by
    simpa only [Entropy.tailRadius, mul_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 32 * 1)
        (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 32))
  rcases eq_or_lt_of_le hαhi with rfl | hαlt
  · simp only [ite_true, sub_self, mul_zero, add_zero, le_refl, abs_zero, true_and, and_true]
    positivity
  · simp only [ite_eq_right hαlt.ne]
    set p := (ManyBody.regionState_isHermitian
      (X := fun _ ↦ Fin q) (interval L l r) Ω).eigenvalues
    set S := ManyBody.regionEntropy (X := fun _ ↦ Fin q) Ω (interval L l r)
    set u := 1 - α
    have hu0 : 0 < u := sub_pos.mpr hαlt
    have hu : u ≤ Entropy.tailRadius (J / Δ) (ManyBody.chainBudgetConst q R) := by
      linarith only [hαlo]
    have hp : ∀ i, 0 ≤ p i :=
      (ManyBody.regionState_posSemidef (X := fun _ ↦ Fin q)
        (interval L l r) Ω).eigenvalues_nonneg
    have hpSum : ∑ i, p i = 1 :=
      Entropy.sum_eigenvalues_partialTraceRight_eq_one
        (Ψ := ManyBody.cutVector (interval L l r) Ω)
        (by rw [Entropy.norm_cutVector, hΩ])
        (ManyBody.regionState_eq_partialTraceRight_cutVector (interval L l r) Ω).symm
        (ManyBody.regionState_isHermitian (interval L l r) Ω)
    have hlo : S ≤ Real.log (Entropy.surprisalMoment p u) / u :=
      (le_div_iff₀ hu0).mpr (by
        simpa only [S, ManyBody.regionEntropy, ManyBody.regionEntropy, vonNeumannEntropy, p,
          mul_comm] using
          mul_entropy_le_log_surprisalMoment hp hpSum u)
    have hcut := ManyBody.cutLogBudget_interval_le (L := L) (R := R) hq l r
    have hmoment := h.log_surprisalMoment_region_le hh hhJ hJ hΔ hΩ hgap hspan (interval L l r)
      ((abs_of_pos hu0).le.trans (hu.trans
        (tailRadius_anti_budget hθ (Entropy.one_le_cutLogBudget _ _) hcut)))
    have hlog : Real.log (Entropy.surprisalMoment p u) ≤ u * S +
        512 * Real.exp 1 * (J / Δ) * ManyBody.chainBudgetConst q R * u ^ 2 :=
      hmoment.trans (by gcongr)
    have hupper : Real.log (Entropy.surprisalMoment p u) / u ≤ S +
        512 * Real.exp 1 * (J / Δ) * ManyBody.chainBudgetConst q R * u :=
      (div_le_iff₀ hu0).mpr (by nlinarith only [hlog])
    set s := Real.sqrt ((1 + J / Δ) * ManyBody.chainBudgetConst q R)
    have hu' : u * (32 * s) ≤ 1 :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * s)).mp hu
    have hs_sq : s ^ 2 = (1 + J / Δ) * ManyBody.chainBudgetConst q R :=
      Real.sq_sqrt (by positivity)
    have hθB : (J / Δ) * ManyBody.chainBudgetConst q R ≤ s ^ 2 := by
      nlinarith only [hs_sq, hB]
    have hc1 : 512 * Real.exp 1 * (J / Δ) * ManyBody.chainBudgetConst q R * u * s ≤
        16 * Real.exp 1 * (J / Δ) * ManyBody.chainBudgetConst q R := by
      nlinarith only [mul_le_mul_of_nonneg_left hu'
        (by positivity : 0 ≤ 16 * Real.exp 1 * (J / Δ) * ManyBody.chainBudgetConst q R)]
    have hc : 512 * Real.exp 1 * (J / Δ) * ManyBody.chainBudgetConst q R * u ≤
        16 * Real.exp 1 * s :=
      (mul_le_mul_iff_right₀ (zero_lt_one.trans_le hs)).mp (by
        nlinarith only [hc1, mul_le_mul_of_nonneg_left hθB
          (by positivity : 0 ≤ 16 * Real.exp 1)])
    have hu1 : u ≠ 1 := ne_of_lt ((hu.trans hrad).trans_lt (by norm_num))
    refine ⟨hlo, hupper, ?_, ?_⟩
    · rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
      linarith only [hupper, hc]
    · simpa only [u, sub_sub_cancel] using
        congrArg (fun t : ℝ ↦ Real.log t / u) (Entropy.surprisalMoment_eq_sum_rpow_of_ne_one hp hu1)

end

end

end
