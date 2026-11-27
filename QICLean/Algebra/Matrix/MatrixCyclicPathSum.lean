/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import QICLean.Algebra.Combinatorics.IndexInduction
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.BigOperators.Group.List.Defs
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul

/-!
# Path sums for ordered products of matrices

This file expands an ordered product of finitely many square matrices as a sum
over index paths: the matrix-vector product of the ordered product is the sum
over paths starting at the row index (`ofFn_prod_mulVec_apply`), an entry of the
ordered product is the sum over paths between its two indices (`ofFn_prod_apply`), and
the trace of the ordered product of a nonempty family is the sum over cyclic paths, in
which each factor connects a site to its cyclic successor
(`trace_ofFn_prod_eq_sum_cyclic`).  For a
ring of scaled matrix units only one path survives, so the trace is the product
of the scalars when consecutive units chain cyclically and zero otherwise
(`trace_ofFn_prod_smul_single`).

Moved from TNLean, `TNLean/Algebra/MatrixCyclicPathSum.lean` at commit `49b78ed821`
(Apache-2.0).

## Main results

* `Matrix.foldl_toEuclideanCLM_eq_reverse_prod`, `Matrix.listProd_ofFn_intertwine`: successive
  matrix actions.
-/

section MatrixCyclicPathSum

open scoped BigOperators

namespace Matrix

variable {ι R : Type*} [Fintype ι] [CommSemiring R]

/-- Summing over the tuples of length `L + 1` is summing over the first entry
and then over the remaining tuple. -/
lemma sum_fin_cons {L : ℕ} (F : (Fin (L + 1) → ι) → R) :
    ∑ t, F t = ∑ c, ∑ t : Fin L → ι, F (Fin.cons c t) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ => ι) (fun x => F (Fin.cons x.1 x.2)) F
    (fun _ => rfl), Fintype.sum_prod_type]

-- `Matrix`'s identity, and hence `List.prod` including the empty product,
-- requires decidable equality.
variable [DecidableEq ι]

/-- **Open path expansion.**  Applying the ordered product of the matrices
`M 0, …, M (L - 1)` to a vector `v` and reading the entry at `a` sums, over all
paths `t` of length `L` starting at `a`, the product of the matrix entries along
the path times `v` at the endpoint. -/
theorem ofFn_prod_mulVec_apply :
    ∀ (L : ℕ) (M : Fin L → Matrix ι ι R) (v : ι → R) (a : ι),
      (List.ofFn M).prod.mulVec v a =
        ∑ t : Fin L → ι,
          (∏ i : Fin L, M i ((Fin.cons a t : Fin (L + 1) → ι) i.castSucc)
            ((Fin.cons a t : Fin (L + 1) → ι) i.succ)) *
            v ((Fin.cons a t : Fin (L + 1) → ι) (Fin.last L))
  | 0, M, v, a => by
      simp [List.ofFn_zero]
  | L + 1, M, v, a => by
      rw [List.ofFn_succ, List.prod_cons, ← Matrix.mulVec_mulVec]
      change (∑ c, M 0 a c * (List.ofFn fun i => M i.succ).prod.mulVec v c) = _
      rw [sum_fin_cons]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ofFn_prod_mulVec_apply L, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Fin.prod_univ_succ, ← Fin.succ_last]
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]
      ring

/-- **Entry path expansion.**  The entry at `(a, b)` of the ordered product of the matrices
`M 0, …, M (L - 1)` is the sum, over all paths `t` of length `L + 1` from `a` to `b`, of the
product of the matrix entries along the path. -/
theorem ofFn_prod_apply (L : ℕ) (M : Fin L → Matrix ι ι R) (a b : ι) :
    (List.ofFn M).prod a b =
      ∑ t : Fin (L + 1) → ι,
        if t 0 = a ∧ t (Fin.last L) = b then ∏ i : Fin L, M i (t i.castSucc) (t i.succ)
        else 0 := by
  have h := ofFn_prod_mulVec_apply L M (Pi.single b 1) a
  rw [Matrix.mulVec_single_one, col_apply] at h
  rw [h, sum_fin_cons, Finset.sum_eq_single a
    (fun c _ hc => Finset.sum_eq_zero fun t _ => by simp [hc]) (by simp)]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [Pi.single_apply]

/-- **Cyclic path expansion.**  The trace of the ordered product of a nonempty
family of matrices is the sum, over all assignments of an index to each site of
the cycle, of the product of the entries connecting each site to its cyclic
successor. -/
theorem trace_ofFn_prod_eq_sum_cyclic (L : ℕ) (M : Fin (L + 1) → Matrix ι ι R) :
    (List.ofFn M).prod.trace =
      ∑ t : Fin (L + 1) → ι, ∏ n, M n (t n) (t (finRotate (L + 1) n)) := by
  rw [List.ofFn_succ', List.prod_concat, Matrix.trace, sum_fin_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := ofFn_prod_mulVec_apply L (fun i => M i.castSucc) (fun c => M (Fin.last L) c a) a
  change (∑ c, _ * _) = _ at h
  rw [Matrix.diag_apply, Matrix.mul_apply, h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.finRotate_succ_castSucc, finRotate_last, Fin.cons_zero]

/-- **Trace of a ring of scaled matrix units.**  The trace of the ordered
product of the scaled matrix units `c n • E_{l n, r n}` is the product of the
scalars when every column index `r n` equals the row index of the cyclic
successor, and zero otherwise. -/
theorem trace_ofFn_prod_smul_single (L : ℕ) (c : Fin (L + 1) → R)
    (l r : Fin (L + 1) → ι) :
    (List.ofFn fun n => c n • Matrix.single (l n) (r n) (1 : R)).prod.trace =
      if ∀ n, r n = l (finRotate (L + 1) n) then ∏ n, c n else 0 := by
  rw [trace_ofFn_prod_eq_sum_cyclic, Finset.sum_eq_single l]
  · simp only [smul_apply, single_apply, true_and, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · exact Finset.prod_congr rfl fun n _ => by simp [h n]
    · obtain ⟨n, hn⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ n) (by simp only [hn, ↓reduceIte])
  · intro t _ ht
    obtain ⟨n, hn⟩ := Function.ne_iff.mp ht
    refine Finset.prod_eq_zero (Finset.mem_univ n) ?_
    simp [Ne.symm hn]
  · simp

end Matrix

end MatrixCyclicPathSum

section OrderedMatrixAction

/-!
## Successive matrix actions

Applying the continuous linear maps of a matrix list from left to right gives
the product of the reversed list. The matrices need not commute or be invertible,
and both the list and the finite coordinate type may be empty.

The ascending application convention occurs in `output` in `openai/math`,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean`, lines 166–169.
This proof is independently written; no upstream Lean proof text is reused.
-/

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- Successive applications in list order equal the action of the reverse
matrix product, including the empty list and an empty coordinate type. -/
theorem foldl_toEuclideanCLM_eq_reverse_prod (l : List (Matrix ι ι 𝕜))
    (Ω : EuclideanSpace 𝕜 ι) :
    (l.map (fun A ↦ toEuclideanCLM (n := ι) (𝕜 := 𝕜) A)).foldl (fun ψ T ↦ T ψ) Ω =
      toEuclideanLin l.reverse.prod Ω := by
  rw [List.foldl_map]
  change l.foldl (fun ψ A ↦ toEuclideanLin A ψ) Ω = _
  induction l generalizing Ω with
  | nil => simp [toEuclideanLin]
  | cons A l ih =>
    simp [List.reverse_cons, List.prod_append, ih, toEuclideanLin, toLpLin_mul_same]

end Matrix

section MatrixProductIntertwine

/-!
# Ordered products through a rectangular intertwiner

A common rectangular intertwiner for two ordered families also intertwines
their products. The matrices need not be Hermitian or invertible, and the
intertwiner need not be an isometry. Empty products are included.

Auxiliary to the ordered band products in OpenAI's area-law manuscript,
`06-transport.tex`, lines 57--61 and 120--128, and `07-comparators.tex`,
lines 80--110 and 370--381, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace Matrix

/-- A common rectangular intertwiner preserves an ordered finite product.
Auxiliary to the ordered band-product identities in the area-law manuscript,
`06-transport.tex`, lines 57--61 and 120--128, and `07-comparators.tex`,
lines 80--110 and 370--381. -/
theorem listProd_ofFn_intertwine
    {α m n : Type*} [Semiring α]
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {K : ℕ} {A : Fin K → Matrix m m α} {B : Fin K → Matrix n n α}
    (Z : Matrix m n α) (h : ∀ g, A g * Z = Z * B g) :
    (List.ofFn A).prod * Z = Z * (List.ofFn B).prod := by
  have hprod := List.prod_hom_rel (List.ofFn (id : Fin K → Fin K))
    (r := fun L R ↦ L * Z = Z * R) (f := A) (g := B)
    (by simp only [Matrix.one_mul, Matrix.mul_one]) (by
      intro g L R hLR
      rw [Matrix.mul_assoc, hLR, ← Matrix.mul_assoc, h g, Matrix.mul_assoc])
  simpa only [List.map_ofFn, Function.comp_id] using hprod

end Matrix

end MatrixProductIntertwine

end OrderedMatrixAction
