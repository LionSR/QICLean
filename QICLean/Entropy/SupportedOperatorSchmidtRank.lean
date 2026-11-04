/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidtRealignment
import QICLean.Algebra.OperatorSchmidtReindex
import QICLean.Entropy.SupportedMarginalTails

/-!
# Operator Schmidt rank from designated supports

For a finite tensor product with arbitrary local dimensions, an operator
supported on X has operator Schmidt rank across A bounded by the square of
the dimension of the configurations on either X ∩ A or X \ A. In uniform positive
local dimension q, the two-sided bound is at most q to the cardinality of X.
An operator supported entirely on either side of the cut has rank at most one.
The support-square and one-sided statements include
empty configuration spaces and empty sets of sites.

The sharp count follows from the matrix-unit decomposition in the
OpenAI area-law manuscript, 02-initial.tex, lines 126–133.
These support estimates are used for words of local operators in LVV,
arXiv:1307.5143v1, equation e:decomp, lines 584–588, and AKLV,
arXiv:1301.1162v1, Lemma l:agsp, lines 646–657. No assumption about a state,
a spectral gap, positivity, or normalization is required here.
-/

open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace Entropy

private theorem operatorSchmidtRank_zero
    {α β : Type*} [Fintype α] [Finite β] :
    Matrix.operatorSchmidtRank (0 : Matrix (α × β) (α × β) ℂ) = 0 := by
  exact Nat.eq_zero_of_le_zero
    (Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨Fin.elim0, Fin.elim0, by simp⟩)

/-- The designated-support matrix-unit count, expressed as operator Schmidt
rank. Supporting algebra for LVV, arXiv:1307.5143v1, equation e:decomp,
lines 584–588, and AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 646–657.
The existing decomposition is proved in the two-dimensional area-law
manuscript, 02-initial.tex, lines 126–133. -/
theorem IsSupportedOn.operatorSchmidtRank_cutOperator_le
    {V : Type*} [Finite V] [DecidableEq V] {n : V → ℕ}
    {A X : Finset V}
    {T : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hT : IsSupportedOn T X) :
    Matrix.operatorSchmidtRank (cutOperator A T) ≤
      (∏ v ∈ X ∩ A, n v) ^ 2 := by
  let := Fintype.ofFinite V
  by_cases hconfig : Nonempty (SiteConfig n)
  case neg =>
    have : IsEmpty (SiteConfig n) := ⟨fun σ => hconfig ⟨σ⟩⟩
    have hzero : T = 0 := Subsingleton.elim _ _
    simp [hzero, cutOperator, operatorSchmidtRank_zero]
  obtain ⟨σ₀⟩ := hconfig
  obtain ⟨M, U, W, hM, hdec, _⟩ :=
    hT.hasProductDecomposition_inner (B := A) σ₀ (le_rfl : ‖T‖ ≤ ‖T‖)
  exact (Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨U, W, hdec⟩).trans (by simpa only [card_innerConfig] using hM)

/-- A supported operator acting on only one side of a cut has operator
Schmidt rank at most one. LVV, arXiv:1307.5143v1, lines 584–588;
AKLV, arXiv:1301.1162v1, Lemma l:agsp, lines 646–653. -/
theorem IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
    {V : Type*} [Finite V] [DecidableEq V] {n : V → ℕ}
    {A X : Finset V}
    {T : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hT : IsSupportedOn T X) (hside : X ⊆ A ∨ Disjoint X A) :
    Matrix.operatorSchmidtRank (cutOperator A T) ≤ 1 := by
  let := Fintype.ofFinite V
  by_cases hconfig : Nonempty (SiteConfig n)
  case neg =>
    have : IsEmpty (SiteConfig n) := ⟨fun σ => hconfig ⟨σ⟩⟩
    have hzero : T = 0 := Subsingleton.elim _ _
    simp [hzero, cutOperator, operatorSchmidtRank_zero]
  obtain ⟨σ₀⟩ := hconfig
  have hone : IsOneSided (cutOperator A T) := hside.elim
    (fun hleft => hT.isOneSided_of_subset hleft ((cutEquiv n A) σ₀).2)
    (fun hright => hT.isOneSided_of_disjoint hright ((cutEquiv n A) σ₀).1)
  rcases hone with ⟨U, hU⟩ | ⟨W, hW⟩
  · exact Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨(fun _ : Fin 1 => U), (fun _ : Fin 1 => 1), by simpa using hU⟩
  · exact Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
      ⟨(fun _ : Fin 1 => 1), (fun _ : Fin 1 => W), by simpa using hW⟩

/-- Exchanging a finite region and its complement preserves the operator Schmidt rank in cut
coordinates. Supporting the two-sided local support bound for ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, lines 1971–2013. The local dimensions may vanish. -/
theorem operatorSchmidtRank_cutOperator_compl_eq
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (A : Finset V) (T : Matrix (SiteConfig n) (SiteConfig n) ℂ) :
    Matrix.operatorSchmidtRank (cutOperator Aᶜ T) =
      Matrix.operatorSchmidtRank (cutOperator A T) := by
  classical
  let eL : ((v : {v : V // v ∉ A}) → Fin (n v)) ≃
      ((v : {v : V // v ∈ Aᶜ}) → Fin (n v)) :=
    Equiv.piCongrLeft' (fun v : {v : V // v ∉ A} ↦ Fin (n v))
    (Equiv.subtypeEquivRight (fun v : V ↦
      (show v ∉ A ↔ v ∈ Aᶜ from Finset.mem_compl.symm)))
  let eR : ((v : {v : V // v ∈ A}) → Fin (n v)) ≃
      ((v : {v : V // v ∉ Aᶜ}) → Fin (n v)) :=
    Equiv.piCongrLeft' (fun v : {v : V // v ∈ A} ↦ Fin (n v))
    (Equiv.subtypeEquivRight (fun v : V ↦
      (show v ∈ A ↔ v ∉ Aᶜ by simp only [Finset.mem_compl, not_not])))
  have he : ((cutEquiv n A).trans (Equiv.prodComm _ _)).trans (eL.prodCongr eR) =
      cutEquiv n Aᶜ := by
    apply Equiv.ext
    intro σ
    exact Prod.ext (funext fun _ ↦ rfl) (funext fun _ ↦ rfl)
  have hm : cutOperator Aᶜ T =
      ((cutOperator A T).reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)).reindex
        (eL.prodCongr eR) (eL.prodCongr eR) := by
    change T.reindex (cutEquiv n Aᶜ) (cutEquiv n Aᶜ) =
      T.reindex (((cutEquiv n A).trans (Equiv.prodComm _ _)).trans (eL.prodCongr eR))
        (((cutEquiv n A).trans (Equiv.prodComm _ _)).trans (eL.prodCongr eR))
    rw [he]
  rw [hm, Matrix.operatorSchmidtRank_reindex_prodCongr,
    Matrix.operatorSchmidtRank_reindex_prodComm]

/-- A supported operator has operator Schmidt rank bounded by the square of the configuration
dimension on either part of its designated support. Supporting the crossing-interval estimate
for ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. Empty regions and zero local
dimensions are included, and no spectral, positivity or state premise is needed. -/
theorem IsSupportedOn.operatorSchmidtRank_cutOperator_le_min
    {V : Type*} [Finite V] [DecidableEq V] {n : V → ℕ} {A X : Finset V}
    {T : Matrix (SiteConfig n) (SiteConfig n) ℂ} (hT : IsSupportedOn T X) :
    Matrix.operatorSchmidtRank (cutOperator A T) ≤
      min ((∏ v ∈ X ∩ A, n v) ^ 2) ((∏ v ∈ X \ A, n v) ^ 2) := by
  let := Fintype.ofFinite V
  refine le_min hT.operatorSchmidtRank_cutOperator_le ?_
  have hc := hT.operatorSchmidtRank_cutOperator_le (A := Aᶜ)
  rw [operatorSchmidtRank_cutOperator_compl_eq] at hc
  simpa only [Finset.sdiff_eq_inter_compl] using hc

/-- On a uniform finite tensor product with positive local dimension, an operator supported on
`X` has operator Schmidt rank at most `q ^ X.card` at every cut. This combines the two actual
support-square bounds, including local dimension one. Supporting ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, lines 1971–2013. -/
theorem IsSupportedOn.operatorSchmidtRank_cutOperator_le_pow_card
    {V : Type*} [Finite V] [DecidableEq V] {q : ℕ} (hq : 1 ≤ q) {A X : Finset V}
    {T : Matrix (SiteConfig (fun _ : V ↦ q)) (SiteConfig (fun _ : V ↦ q)) ℂ}
    (hT : IsSupportedOn T X) :
    Matrix.operatorSchmidtRank (cutOperator A T) ≤ q ^ X.card := by
  have hm := hT.operatorSchmidtRank_cutOperator_le_min (A := A)
  simp only [Finset.prod_const, ← pow_mul] at hm
  have hc := Finset.card_inter_add_card_sdiff X A
  rcases le_total (X ∩ A).card (X \ A).card with hle | hle
  · exact hm.trans ((min_le_left _ _).trans (Nat.pow_le_pow_right hq (by omega)))
  · exact hm.trans ((min_le_right _ _).trans (Nat.pow_le_pow_right hq (by omega)))

end Entropy
