/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcLogAdditive
import QICLean.Analysis.OperatorMean.FiniteTree

/-!
# The logarithm of an ordered commuting product

The logarithm of an ordered finite product of pairwise commuting positive
definite matrices is the sum of their logarithms. This includes the empty
product and repeated matrix values.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, 06-transport.tex, transport:relative-factorization,
Lemma 7.1, and the band decomposition in 07-comparators.tex,
comparator:sharp-jensen, revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The logarithm of an ordered product of pairwise commuting positive
definite matrices is the sum of the logarithms.
Source: 06-transport.tex, transport:relative-factorization, Lemma 7.1. -/
theorem cfc_log_listProd_ofFn {K : ℕ} {X : Fin K → Matrix m m ℂ}
    (hX : ∀ g, (X g).PosDef)
    (hXX : ∀ g g', g ≠ g' → Commute (X g) (X g')) :
    CFC.log (List.ofFn X).prod = ∑ g, CFC.log (X g) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons, Fin.sum_univ_succ,
      (hX 0).cfc_log_mul (Matrix.MeanTree.posDef_listProd_ofFn (fun g => hX _)
        (fun g g' h => hXX _ _ (fun h' => h (Fin.succ_injective _ h'))))
        (Commute.list_prod_right _ _ fun y hy => by
          obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
          exact hXX _ _ (Fin.succ_ne_zero g).symm),
      ih (fun g => hX _) (fun g g' h => hXX _ _ (fun h' => h (Fin.succ_injective _ h')))]

end Matrix
