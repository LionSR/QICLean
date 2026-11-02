/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Normed.Ring.Int
import Mathlib.Data.Finset.Powerset

/-!
# A coefficient bound for unions of marked finite sets

If each member of a finite family has a distinct chosen element, the signed
sum over subfamilies with a prescribed union has absolute value at most two
to the cardinality of that union. This is a finite combinatorial ingredient
for an energy-normalized interaction-label cluster estimate, auxiliary to
ALVV, arXiv:1602.08828v2, `thm:cluster-approx`, lines 1270–1291 and 1935–1968.
The false printed spatial approximation estimate remains distinct; see
https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf.
-/

namespace Finset

/-- Signed inclusion–exclusion coefficients with a fixed union are bounded
by the number of subsets of that union, when each member of the original
family has a distinct chosen element belonging to it. This is an auxiliary
coefficient bound for a corrected interaction-label expansion in ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1935–1968. -/
theorem norm_sum_powerset_biUnion_sign_le_two_pow
    {κ : Type*} [DecidableEq κ] (W : Finset (Finset κ)) (marker : W → κ)
    (hmarker : ∀ I : W, marker I ∈ (I : Finset κ)) (hinj : Function.Injective marker)
    (U : Finset κ) :
    ‖∑ F ∈ W.powerset with F.Nonempty ∧ F.biUnion id = U,
      (-1 : ℤ) ^ (F.card + 1)‖ ≤ (2 : ℝ) ^ U.card := by
  let V := W.filter (fun I ↦ I ⊆ U)
  have hcardV : V.card ≤ U.card := by
    let f : V → U := fun I ↦
      ⟨marker ⟨I.1, (Finset.mem_filter.mp I.2).1⟩,
        (Finset.mem_filter.mp I.2).2 (hmarker ⟨I.1, (Finset.mem_filter.mp I.2).1⟩)⟩
    apply Finset.card_le_card_of_injective (f := f)
    exact fun I J hij ↦ Subtype.ext (congrArg (fun K : W ↦ (K : Finset κ))
      (hinj (congrArg (fun K : U ↦ (K : κ)) hij)))
  have hfamilies :
      {F ∈ W.powerset | F.Nonempty ∧ F.biUnion id = U} ⊆ V.powerset := by
    exact fun F hF ↦ Finset.mem_powerset.mpr fun I hIF ↦ Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1 hIF,
        fun x hx ↦ (Finset.mem_filter.mp hF).2.2 ▸
          Finset.mem_biUnion.mpr ⟨I, hIF, hx⟩⟩
  have hcard : {F ∈ W.powerset | F.Nonempty ∧ F.biUnion id = U}.card ≤ 2 ^ U.card :=
    (Finset.card_le_card hfamilies).trans
      ((Finset.card_powerset V).trans_le (Nat.pow_le_pow_right (by decide) hcardV))
  refine (norm_sum_le _ _).trans ?_
  have hcardR : ({F ∈ W.powerset | F.Nonempty ∧ F.biUnion id = U}.card : ℝ) ≤
      (2 : ℝ) ^ U.card := by exact_mod_cast hcard
  simpa using hcardR

end Finset
