/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MarginalTails
import QICLean.Channel.Peripheral.SchurAsymptoticConvergence

/-!
# Marginal tails for interactions with designated supports

Let `𝓗 = ⊗_{v ∈ V} ℂ^{n_v}` be a finite tensor product with arbitrary local dimensions.
An operator is supported on `D ⊆ V` when it acts as the identity on the sites outside
`D`: its matrix elements vanish between configurations that differ outside `D` and do not
depend on the common values there. For a bipartition `B ⊔ Bᶜ = V`, an operator supported
on `D` is one-sided when `D ⊆ B` or `D ⊆ Bᶜ`. Otherwise, the matrix units on `D ∩ B` write
it as a sum of at most `d²` products `c ⊗ d'` with `‖c‖ ≤ 1` and `‖d'‖` at most its norm,
where `d = ∏_{v ∈ D} n_v`.

With these decompositions, `QICLean.Entropy.MarginalTails` gives Lemma 3.1 of the
area-law manuscript in its stated form: designated supports, `d_i = ∏_{v ∈ D_i} dim 𝓗_v`,
and `ℬ = 1 + ∑_{i ∈ I×} log² (e d_i)` over the terms whose support meets both sides.

## Main results

* `Entropy.IsSupportedOn.isOneSided_of_subset`, `Entropy.IsSupportedOn.isOneSided_of_disjoint`.
* `Entropy.IsSupportedOn.hasProductDecomposition`: the matrix-unit decomposition.
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

/-- Configurations of a finite tensor product `⊗_v ℂ^{n_v}`. -/
abbrev SiteConfig (n : V → ℕ) := (v : V) → Fin (n v)

/-- An operator is supported on `D` when it acts as the identity outside `D`: its matrix
elements vanish between configurations that differ outside `D`, and otherwise do not
depend on the common values outside `D`.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, line 39: designated supports. -/
def IsSupportedOn (X : Matrix (SiteConfig n) (SiteConfig n) ℂ) (D : Finset V) : Prop :=
  (∀ σ τ : SiteConfig n, (∃ v ∉ D, σ v ≠ τ v) → X σ τ = 0) ∧
    ∀ σ τ σ' τ' : SiteConfig n, (∀ v ∈ D, σ v = σ' v) → (∀ v ∈ D, τ v = τ' v) →
      (∀ v ∉ D, σ v = τ v) → (∀ v ∉ D, σ' v = τ' v) → X σ τ = X σ' τ'

omit [Fintype V] [DecidableEq V] in
/-- Matrix elements of a supported operator agree whenever the configurations agree on
the support and have the same coincidence pattern outside it. -/
theorem IsSupportedOn.apply_eq {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} {D : Finset V}
    (hX : IsSupportedOn X D) {σ τ σ' τ' : SiteConfig n} (h1 : ∀ v ∈ D, σ v = σ' v)
    (h2 : ∀ v ∈ D, τ v = τ' v) (h3 : ∀ v ∉ D, (σ v = τ v ↔ σ' v = τ' v)) :
    X σ τ = X σ' τ' := by
  by_cases h : ∃ v ∉ D, σ v ≠ τ v
  · obtain ⟨v, hv, hne⟩ := h
    rw [hX.1 σ τ ⟨v, hv, hne⟩, hX.1 σ' τ' ⟨v, hv, fun h' ↦ hne ((h3 v hv).mpr h')⟩]
  · push_neg at h
    exact hX.2 σ τ σ' τ' h1 h2 h (fun v hv ↦ (h3 v hv).mp (h v hv))

/-- The cut decomposition of a configuration into its parts on `B` and on `Bᶜ`. -/
abbrev cutEquiv (n : V → ℕ) (B : Finset V) :
    SiteConfig n ≃ ((v : {v // v ∈ B}) → Fin (n v)) × ((v : {v // v ∉ B}) → Fin (n v)) :=
  Equiv.piEquivPiSubtypeProd (· ∈ B) fun v ↦ Fin (n v)

/-- An operator in cut coordinates. -/
noncomputable abbrev cutOperator (B : Finset V) (X : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Matrix (((v : {v // v ∈ B}) → Fin (n v)) × ((v : {v // v ∉ B}) → Fin (n v)))
      (((v : {v // v ∈ B}) → Fin (n v)) × ((v : {v // v ∉ B}) → Fin (n v))) ℂ :=
  reindex (cutEquiv n B) (cutEquiv n B) X

/-- A vector in cut coordinates. -/
noncomputable abbrev cutVector (B : Finset V) (Ψ : EuclideanSpace ℂ (SiteConfig n)) :
    EuclideanSpace ℂ (((v : {v // v ∈ B}) → Fin (n v)) × ((v : {v // v ∉ B}) → Fin (n v))) :=
  WithLp.toLp 2 fun x ↦ Ψ ((cutEquiv n B).symm x)

section OneSided

variable {B : Finset V}

omit [Fintype V] in
theorem cutEquiv_symm_apply_mem (x : (v : {v // v ∈ B}) → Fin (n v))
    (y : (v : {v // v ∉ B}) → Fin (n v)) {v : V} (hv : v ∈ B) :
    (cutEquiv n B).symm (x, y) v = x ⟨v, hv⟩ := by
  simp [Equiv.piEquivPiSubtypeProd, hv]

omit [Fintype V] in
theorem cutEquiv_symm_apply_not_mem (x : (v : {v // v ∈ B}) → Fin (n v))
    (y : (v : {v // v ∉ B}) → Fin (n v)) {v : V} (hv : v ∉ B) :
    (cutEquiv n B).symm (x, y) v = y ⟨v, hv⟩ := by
  simp [Equiv.piEquivPiSubtypeProd, hv]

/-- A term supported inside `B` acts on the first cut factor only. -/
theorem IsSupportedOn.isOneSided_of_subset {X : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    {D : Finset V} (hX : IsSupportedOn X D) (hDB : D ⊆ B)
    (y₀ : (v : {v // v ∉ B}) → Fin (n v)) : IsOneSided (cutOperator B X) := by
  classical
  refine Or.inl ⟨fun x x' ↦ cutOperator B X (x, y₀) (x', y₀), ?_⟩
  ext ⟨x, y⟩ ⟨x', y'⟩
  change cutOperator B X (x, y) (x', y') =
    cutOperator B X (x, y₀) (x', y₀) * (1 : Matrix _ _ ℂ) y y'
  simp only [reindex_apply, submatrix_apply, one_apply, mul_ite, mul_one, mul_zero]
  split_ifs with hy
  · subst hy
    refine hX.apply_eq (fun v hv ↦ ?_) (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    · rw [cutEquiv_symm_apply_mem _ _ (hDB hv), cutEquiv_symm_apply_mem _ _ (hDB hv)]
    · rw [cutEquiv_symm_apply_mem _ _ (hDB hv), cutEquiv_symm_apply_mem _ _ (hDB hv)]
    · by_cases hvB : v ∈ B
      · simp only [cutEquiv_symm_apply_mem _ _ hvB]
      · simp only [cutEquiv_symm_apply_not_mem _ _ hvB]
  · obtain ⟨w, hw⟩ := Function.ne_iff.mp hy
    refine hX.1 _ _ ⟨w.1, fun h ↦ w.2 (hDB h), ?_⟩
    rwa [cutEquiv_symm_apply_not_mem _ _ w.2, cutEquiv_symm_apply_not_mem _ _ w.2]

/-- A term supported outside `B` acts on the second cut factor only. -/
theorem IsSupportedOn.isOneSided_of_disjoint {X : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    {D : Finset V} (hX : IsSupportedOn X D) (hDB : Disjoint D B)
    (x₀ : (v : {v // v ∈ B}) → Fin (n v)) : IsOneSided (cutOperator B X) := by
  classical
  refine Or.inr ⟨fun y y' ↦ cutOperator B X (x₀, y) (x₀, y'), ?_⟩
  ext ⟨x, y⟩ ⟨x', y'⟩
  have hnot : ∀ v ∈ D, v ∉ B := fun v hv hvB ↦ Finset.disjoint_left.mp hDB hv hvB
  change cutOperator B X (x, y) (x', y') =
    (1 : Matrix _ _ ℂ) x x' * cutOperator B X (x₀, y) (x₀, y')
  simp only [reindex_apply, submatrix_apply, one_apply, ite_mul, one_mul, zero_mul]
  split_ifs with hx
  · subst hx
    refine hX.apply_eq (fun v hv ↦ ?_) (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    · rw [cutEquiv_symm_apply_not_mem _ _ (hnot v hv), cutEquiv_symm_apply_not_mem _ _ (hnot v hv)]
    · rw [cutEquiv_symm_apply_not_mem _ _ (hnot v hv), cutEquiv_symm_apply_not_mem _ _ (hnot v hv)]
    · by_cases hvB : v ∈ B
      · simp only [cutEquiv_symm_apply_mem _ _ hvB]
      · simp only [cutEquiv_symm_apply_not_mem _ _ hvB]
  · obtain ⟨w, hw⟩ := Function.ne_iff.mp hx
    refine hX.1 _ _ ⟨w.1, fun h ↦ hnot _ h w.2, ?_⟩
    rwa [cutEquiv_symm_apply_mem _ _ w.2, cutEquiv_symm_apply_mem _ _ w.2]

end OneSided

end Entropy
