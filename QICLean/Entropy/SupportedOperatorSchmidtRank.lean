/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OperatorSchmidt
import QICLean.Entropy.SupportedMarginalTails

/-!
# Operator Schmidt rank from designated supports

For a finite tensor product with arbitrary local dimensions, an operator
supported on X has operator Schmidt rank across A bounded by the square of
the dimension of the configurations on X ∩ A. An operator supported entirely
on either side of the cut has rank at most one. Both statements include
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
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    {A X : Finset V}
    {T : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hT : IsSupportedOn T X) :
    Matrix.operatorSchmidtRank (cutOperator A T) ≤
      (∏ v ∈ X ∩ A, n v) ^ 2 := by
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
    {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    {A X : Finset V}
    {T : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    (hT : IsSupportedOn T X) (hside : X ⊆ A ∨ Disjoint X A) :
    Matrix.operatorSchmidtRank (cutOperator A T) ≤ 1 := by
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

end Entropy
