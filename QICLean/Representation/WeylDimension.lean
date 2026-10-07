/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.SchurLabelEstimates
import QICLean.Representation.WeylRecursion

/-!
# The Weyl dimension formula for the multiplicity spaces

The multiplicity `m_λ = dim V^{(q)}_λ` of the label `λ` in `(ℂ^q)^{⊗k}` is
`∏_{i<j} (l_i - l_j)/(j - i)` with `l_i = λ_i + q - 1 - i`, the Weyl dimension formula of
Lemma 6.1(1) of the area-law paper (*A two-dimensional area law from a global spectral
gap*, `05-replicas.tex`, equation `replicas:dimensions`).

## Method

Restricting `(ℂ^q)^{⊗(m+1)} = (ℂ^q)^{⊗m} ⊗ ℂ^q` to the first `m` copies, the trace of the
central idempotent of a label `ν` of `S_m` gives `∑_λ c(λ, ν) m_λ = q m_ν`; by the branching
rule this is `∑_i m_{ν + e_i} = q m_ν`. The Weyl formula satisfies the same recursion
(`Partition.sum_weylFormula_add`) and both vanish for partitions with more than `q` rows.
The recursion determines the values at level `m + 1` from those at level `m`: for a
counterexample `λ` with the most rows and, among those, lexicographically largest, removing
the last box of its last row gives a `ν` whose other branches are all larger.

## Main declarations

* `TensorPower.sum_branchMult_mul_multiplicity` — `∑_λ c(λ, ν) m_λ = q m_ν`.
* `TensorPower.multiplicity_eq_weylFormula` — **`dim V_λ = W_λ`**.
-/

open Finset Matrix PermutationRepresentation

namespace TensorPower

variable {q m : ℕ}

theorem firstCopies_groupAlgebraRep_apply_snoc (b : MonoidAlgebra ℂ (Equiv.Perm (Fin m)))
    (y : Fin m → Fin q) (c : Fin q) :
    groupAlgebraRep ((copyPerm (Fin q) (m + 1)).comp (firstCopies m)) b
        (Fin.snoc y c) (Fin.snoc y c) = groupAlgebraRep (copyPerm (Fin q) m) b y y := by
  have h := congrFun (slice_groupAlgebraRep b (Pi.single (Fin.snoc y c) 1) c) y
  have hs : slice (Pi.single (Fin.snoc y c : Fin (m + 1) → Fin q) (1 : ℂ)) c =
      Pi.single y 1 := by
    funext y'
    simp only [slice, Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro e; simpa using congrArg Fin.init e
    · rintro rfl; rfl
  rw [hs] at h
  simpa [slice, mulVec_single] using h

theorem trace_firstCopies_groupAlgebraRep (b : MonoidAlgebra ℂ (Equiv.Perm (Fin m))) :
    (groupAlgebraRep ((copyPerm (Fin q) (m + 1)).comp (firstCopies m)) b).trace =
      q * (groupAlgebraRep (copyPerm (Fin q) m) b).trace := by
  rw [Matrix.trace, ← (Fin.snocEquiv fun _ => Fin q).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, diag_apply]
  simp only [firstCopies_groupAlgebraRep_apply_snoc, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rfl

/-- **`∑_λ c(λ, ν) m_λ = q m_ν`**: restricting `(ℂ^q)^{⊗(m+1)}` to the first `m` copies
multiplies the multiplicity of `ν` by `q`. -/
theorem sum_branchMult_mul_multiplicity (n : IrrepLabel (Equiv.Perm (Fin m))) :
    ∑ l, IrrepLabel.branchMult (firstCopies m) l n * multiplicity (copyPerm (Fin q) (m + 1)) l =
      q * multiplicity (copyPerm (Fin q) m) n := by
  set φ' := copyPerm (Fin q) (m + 1)
  set a := IrrepLabel.restrictHom (firstCopies m) (IrrepLabel.centralIdem n)
  have hd : (n.dim : ℂ) ≠ 0 := by exact_mod_cast n.dim_pos.ne'
  have h1 : (groupAlgebraRep φ' a).trace = q * (n.dim * multiplicity (copyPerm (Fin q) m) n) := by
    rw [← groupAlgebraRep_comp, trace_firstCopies_groupAlgebraRep, ← labelProj,
      trace_labelProj]
    push_cast; ring
  have h2 : ∀ l, (groupAlgebraRep φ' a * labelProj φ' l).trace =
      n.dim * (IrrepLabel.branchMult (firstCopies m) l n * multiplicity φ' l) := by
    intro l
    have h := trace_mul_groupAlgebraRep_mul_labelProj φ' (M := 1) (fun g => Commute.one_right _)
      a l
    simp only [one_mul] at h
    rw [IrrepLabel.trace_block_centralIdem, trace_labelProj] at h
    have hl : (l.dim : ℂ) ≠ 0 := by exact_mod_cast l.dim_pos.ne'
    apply mul_left_cancel₀ hl
    rw [h]
    push_cast; ring
  have h3 : (groupAlgebraRep φ' a).trace = ∑ l, (groupAlgebraRep φ' a * labelProj φ' l).trace := by
    rw [← trace_sum, ← mul_sum, sum_labelProj, mul_one]
  rw [h1] at h3
  simp only [h2, ← mul_sum] at h3
  have h4 : (n.dim : ℂ) * ∑ l, (IrrepLabel.branchMult (firstCopies m) l n : ℂ) *
      multiplicity φ' l = n.dim * (q * multiplicity (copyPerm (Fin q) m) n) := by
    rw [← h3]; ring
  have h5 := mul_left_cancel₀ hd h4
  exact_mod_cast h5

end TensorPower
