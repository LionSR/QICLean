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

## Main definitions

* `ManyBody.cutLogBudget`: the log budget of the terms of a family of supports crossing a cut.

## Main results

* `ManyBody.cutLogBudget_le`, `ManyBody.cutLogBudget_const_le`: the budget is at most
  `1 + |I×| log² (e d)` for crossing supports of dimension at most `d`, and so at most
  `1 + |I×| log² (e q^k)` for one local dimension `q` and supports of at most `k` sites.
* `ManyBody.IsSupportedOn.isOneSided_of_subset`, `ManyBody.IsSupportedOn.isOneSided_of_disjoint`.
* `ManyBody.IsSupportedOn.hasProductDecomposition`: the matrix-unit decomposition.
* `Entropy.log_surprisalMoment_cut_le`, `Entropy.surprisalTail_cut_le`: Lemma 3.1.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Lemma 3.1 (`lem:tail`),
  `02-initial.tex`, lines 34–69 and 126–133.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder Kronecker Matrix.Norms.L2Operator

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

section Main

variable {ι : Type*} [Fintype ι]

/-- The dimension `d_i = ∏_{v ∈ D_i} dim 𝓗_v` of a designated support.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, line 51. -/
def supportDim (n : V → ℕ) (D : Finset V) : ℕ := ∏ v ∈ D, n v

omit [Fintype V] [DecidableEq V] in
/-- A support of `k` sites with local dimension `q` at every site has dimension `q ^ k`. -/
theorem supportDim_const (q : ℕ) (D : Finset V) : supportDim (fun _ ↦ q) D = q ^ D.card :=
  Finset.prod_const q

omit [Fintype V] [DecidableEq V] in
/-- The **cut budget** `ℬ_B = 1 + ∑_{i ∈ I×} log² (e d_i)` of a family of supports `D` at the
region `B`. The sum runs over the supports crossing `B`, and `d_i = ∏_{v ∈ D_i} n_v` is the
dimension of the `i`th support for the local dimensions `n`. It is the parameter
`Entropy.cutLogBudget` of the marginal tail bound at the crossing terms; a chain, a lattice
domain or any family of designated supports gives its budget by choosing `D`.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, lines 47–55. -/
noncomputable abbrev _root_.ManyBody.cutLogBudget (D : ι → Finset V) (n : V → ℕ)
    (B : Finset V) : ℝ :=
  Entropy.cutLogBudget (ManyBody.crossingTerms D B) (supportDim n ∘ D)

/-- Exchanging a region and its complement preserves the cut budget. -/
@[simp] theorem _root_.ManyBody.cutLogBudget_compl (D : ι → Finset V) (n : V → ℕ)
    (B : Finset V) : ManyBody.cutLogBudget D n Bᶜ = ManyBody.cutLogBudget D n B := by
  rw [ManyBody.cutLogBudget, ManyBody.crossingTerms_compl]

omit [Fintype V] [DecidableEq V] in
/-- No support crosses the empty region, so its cut budget is one. -/
@[simp] theorem _root_.ManyBody.cutLogBudget_empty (D : ι → Finset V) (n : V → ℕ) :
    ManyBody.cutLogBudget D n ∅ = 1 := by
  simp [ManyBody.cutLogBudget, Entropy.cutLogBudget]

omit [DecidableEq V] in
/-- No support crosses the region of all sites, so its cut budget is one. -/
@[simp] theorem _root_.ManyBody.cutLogBudget_univ (D : ι → Finset V) (n : V → ℕ) :
    ManyBody.cutLogBudget D n Finset.univ = 1 := by
  simp [ManyBody.cutLogBudget, Entropy.cutLogBudget]

omit [Fintype V] [DecidableEq V] in
/-- **The cut budget grows linearly with the number of crossing supports.** If every crossing
support has dimension at most `d`, then `ℬ_B ≤ 1 + |I×| log² (e d)`. -/
theorem _root_.ManyBody.cutLogBudget_le {D : ι → Finset V} {n : V → ℕ} {B : Finset V}
    {d : ℝ} (hdim : ∀ i ∈ ManyBody.crossingTerms D B, (supportDim n (D i) : ℝ) ≤ d) :
    ManyBody.cutLogBudget D n B ≤
      1 + (ManyBody.crossingTerms D B).card * Real.log (Real.exp 1 * d) ^ 2 := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hterm : ∀ i ∈ ManyBody.crossingTerms D B,
      Real.log (Real.exp 1 * ((supportDim n ∘ D) i : ℝ)) ^ 2 ≤
        Real.log (Real.exp 1 * d) ^ 2 := by
    intro i hi
    rcases Nat.eq_zero_or_pos (supportDim n (D i)) with h0 | hpos
    · have h0' : ((supportDim n ∘ D) i : ℝ) = 0 := by simp [h0]
      rw [h0', mul_zero, Real.log_zero, zero_pow two_ne_zero]
      exact sq_nonneg _
    · have h1 : (1 : ℝ) ≤ supportDim n (D i) := by exact_mod_cast hpos
      have hl : 0 ≤ Real.log (Real.exp 1 * supportDim n (D i)) :=
        Real.log_nonneg (one_le_mul_of_one_le_of_one_le he h1)
      exact pow_le_pow_left₀ hl (Real.log_le_log (by positivity)
        (mul_le_mul_of_nonneg_left (hdim i hi) (Real.exp_pos 1).le)) 2
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hsum
  change 1 + _ ≤ _
  linarith

omit [Fintype V] [DecidableEq V] in
/-- **The cut budget for one local dimension.** With local dimension `q ≥ 1` at every site and
crossing supports of at most `k` sites, `ℬ_B ≤ 1 + |I×| log² (e q^k)`. -/
theorem _root_.ManyBody.cutLogBudget_const_le {D : ι → Finset V} {q k : ℕ} {B : Finset V}
    (hq : 1 ≤ q) (hcard : ∀ i ∈ ManyBody.crossingTerms D B, (D i).card ≤ k) :
    ManyBody.cutLogBudget D (fun _ ↦ q) B ≤
      1 + (ManyBody.crossingTerms D B).card * Real.log (Real.exp 1 * (q : ℝ) ^ k) ^ 2 := by
  refine ManyBody.cutLogBudget_le fun i hi ↦ ?_
  rw [supportDim_const, Nat.cast_pow]
  exact pow_le_pow_right₀ (by exact_mod_cast hq) (hcard i hi)

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
