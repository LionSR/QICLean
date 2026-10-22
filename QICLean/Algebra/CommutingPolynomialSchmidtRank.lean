/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.CommutingPolynomialGaps
import QICLean.Algebra.OperatorSchmidtBounds
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Operator Schmidt rank of a commuting-gap coefficient

For commuting bipartite operators `A` and `B` whose ranks are at most one,
and an operator `T` of rank at most `r`, the coefficient of degree `k` in
`(C (A + B) + C T * X)^(m + k)` has operator Schmidt rank at most
`choose (m + 2 * k + 1) (2 * k + 1) * r^k`.

The coefficient belongs to the span of the ordered commuting-gap forms.
Every form has `k` distinguished factors and hence rank at most `r^k`.
Subadditivity and the scalar rank inequality bound the whole coefficient by
this common rank bound times the size of the indexed family.

Supporting algebra for AKLV, arXiv:1301.1162v1, Lemma l:agsp,
lines 604–617 and 646–657. The Hamiltonian coefficient identification,
local supports, and geometric movement of the chain cut are separate steps.

**Local fix (count):** The count includes the additional `+1` omitted in the source.
See `docs/paper-gaps/aklv13_interpolation_and_word_count.tex`:
https://sirui-lu.com/QICLean/paper-gaps/aklv13_interpolation_and_word_count.pdf.
-/

open scoped BigOperators Kronecker

namespace Matrix

private theorem rank_one_le {l n : Type*} [Fintype l] [Fintype n]
    [DecidableEq (l × n)] : operatorSchmidtRank (1 : Matrix (l × n) (l × n) ℂ) ≤ 1 := by
  classical
  exact operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    ⟨fun _ : Fin 1 ↦ (1 : Matrix l l ℂ), fun _ : Fin 1 ↦ (1 : Matrix n n ℂ),
      by ext i j; simp [Matrix.one_apply]⟩

private theorem rank_pow_le_one {l n : Type*} [Fintype l] [Fintype n]
    [DecidableEq (l × n)] (A : Matrix (l × n) (l × n) ℂ)
    (hA : operatorSchmidtRank A ≤ 1) (a : ℕ) : operatorSchmidtRank (A ^ a) ≤ 1 := by
  induction a with
  | zero => simpa only [pow_zero] using (rank_one_le (l := l) (n := n))
  | succ a ih =>
    rw [pow_succ]
    exact (operatorSchmidtRank_mul_le _ _).trans (Nat.mul_le_mul ih hA)

private theorem rank_commuting_gap_form_le {l n : Type*} [Fintype l] [Fintype n]
    [DecidableEq (l × n)] (A B T : Matrix (l × n) (l × n) ℂ)
    (hA : operatorSchmidtRank A ≤ 1) (hB : operatorSchmidtRank B ≤ 1)
    {r : ℕ} (hT : operatorSchmidtRank T ≤ r)
    (k : ℕ) (d : Fin (k + 1) × Bool → ℕ) :
    operatorSchmidtRank
      ((List.ofFn (fun j : Fin k ↦
        A ^ d (j.castSucc, false) * B ^ d (j.castSucc, true) * T)).prod *
        (A ^ d (Fin.last k, false) * B ^ d (Fin.last k, true))) ≤ r ^ k := by
  induction k with
  | zero =>
    simpa only [List.ofFn_zero, List.prod_nil, one_mul, pow_zero, Nat.one_mul] using
      (operatorSchmidtRank_mul_le (A ^ d (Fin.last 0, false))
        (B ^ d (Fin.last 0, true))).trans
        (Nat.mul_le_mul (rank_pow_le_one A hA _) (rank_pow_le_one B hB _))
  | succ k ih =>
    rw [List.ofFn_succ, List.prod_cons, mul_assoc]
    have hfirst : operatorSchmidtRank
        (A ^ d (0, false) * B ^ d (0, true) * T) ≤ r := by
      simpa only [Nat.one_mul] using
        (operatorSchmidtRank_mul_le (A ^ d (0, false) * B ^ d (0, true)) T).trans
          (Nat.mul_le_mul
            ((operatorSchmidtRank_mul_le (A ^ d (0, false)) (B ^ d (0, true))).trans
              (Nat.mul_le_mul (rank_pow_le_one A hA _) (rank_pow_le_one B hB _))) hT)
    refine (operatorSchmidtRank_mul_le _ _).trans ?_
    simpa only [pow_succ', Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last] using
      Nat.mul_le_mul hfirst (ih (fun jb ↦ d (jb.1.succ, jb.2)))

/-- The operator Schmidt rank of a distinguished-letter coefficient with commuting
gap factors whose ranks are at most one. Supporting algebra for AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 604–617 and 646–657. The exponent-tuple count uses the
correction in docs/paper-gaps/aklv13_interpolation_and_word_count.tex. -/
theorem operatorSchmidtRank_coeff_pow_C_add_C_mul_X_le
    {l n : Type*} [Fintype l] [Fintype n] [DecidableEq (l × n)]
    (A B T : Matrix (l × n) (l × n) ℂ)
    (hAB : Commute A B)
    (hA : operatorSchmidtRank A ≤ 1)
    (hB : operatorSchmidtRank B ≤ 1)
    {r : ℕ} (hT : operatorSchmidtRank T ≤ r) (m k : ℕ) :
    operatorSchmidtRank
      (((Polynomial.C (A + B) + Polynomial.C T * Polynomial.X) ^ (m + k)).coeff k) ≤
        (m + 2 * k + 1).choose (2 * k + 1) * r ^ k := by
  let E := Finset.piAntidiag (Finset.univ : Finset (Fin (k + 1) × Bool)) m
  let G : E → Matrix (l × n) (l × n) ℂ := fun d ↦
    (List.ofFn (fun j : Fin k ↦
      A ^ d.val (j.castSucc, false) * B ^ d.val (j.castSucc, true) * T)).prod *
      (A ^ d.val (Fin.last k, false) * B ^ d.val (Fin.last k, true))
  have hspan :
      ((Polynomial.C (A + B) + Polynomial.C T * Polynomial.X) ^ (m + k)).coeff k ∈
        Submodule.span ℂ (Set.range G) :=
    Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps (𝕜 := ℂ) A B T hAB m k
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hspan
  rw [← hc]
  refine (operatorSchmidtRank_sum_le Finset.univ (fun d ↦ c d • G d)).trans ?_
  calc
    _ ≤ ∑ _ : E, r ^ k := Finset.sum_le_sum fun d _ ↦
      (operatorSchmidtRank_smul_le (c d) (G d)).trans
        (rank_commuting_gap_form_le A B T hA hB hT k d.val)
    _ = _ := by simp [E, Finset.card_piAntidiag_univ_fin_prod_bool]


end Matrix
