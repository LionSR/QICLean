/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.WeightedGeometricMean
import Mathlib.Topology.UnitInterval

/-!
# Finite trees of weighted geometric means

A weighted binary tree is a finite rooted binary tree with a parameter
`p ∈ [0, 1]` at each internal vertex; its two outgoing edges have weights
`1 - p` and `p`. Its terminal weights are the products of edge weights along
root-to-leaf paths. Assigning positive definite matrices to the leaves and
evaluating each internal vertex by the weighted geometric mean `A #_p B`
defines the root matrix.

Leaves carry labels in a type `ι`, and the inputs are a family `A : ι → M_n(ℂ)`.
The terminal weight of a label is the sum of the path products over the leaves
carrying it, so a label may occur at several leaves. The tree is part of the
data: no associativity of matrix means is asserted or used.

## Main definitions

* `Matrix.MeanTree ι` — finite rooted binary trees with leaf labels in `ι` and
  a weight in the unit interval at each internal vertex.
* `Matrix.MeanTree.eval` — the root matrix of a tree with given leaf inputs.
* `Matrix.MeanTree.weight` — the terminal weights.

## Main results

Area-law paper, Lemma 7.1 (`transport:means`):

* `Matrix.MeanTree.sum_weight` — the terminal weights sum to one.
* `Matrix.MeanTree.eval_node_zero`, `Matrix.MeanTree.eval_node_one` — an edge of
  weight zero may be omitted and the vertex contracted.
* `Matrix.MeanTree.posDef_eval` — the root is positive definite.
* `Matrix.MeanTree.eval_star_conj` — the root commutes with invertible congruence.
* `Matrix.MeanTree.eval_mono` — the root is monotone in the inputs.
* `Matrix.MeanTree.eval_smul` — scalar homogeneity `𝒯(c_j A_j) = (∏ c_j ^ w_j) M`.
* `Matrix.MeanTree.re_dotProduct_eval_le` — the vector Jensen inequality
  `⟨z, M z⟩ ≤ ∏ ⟨z, A_j z⟩ ^ w_j`.
* `Matrix.MeanTree.smul_le_eval` — projection transfer: `A_j ≥ c_j P` for all `j`
  implies `M ≥ (∏ c_j ^ w_j) P`.
* `Matrix.MeanTree.eval_mul_of_commute`, `Matrix.MeanTree.eval_listProd_ofFn` —
  factorization of the root across commuting bands.

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, lines 28--62 (definition of weighted
  binary trees and the statement of Lemma 7.1) and lines 99--128 (its proof).
  The proofs here are written independently from the paper; no code is adapted
  from the accompanying Lean development.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Filter Topology

namespace Matrix

/-- A finite rooted binary tree with leaves labelled in `ι` and a parameter
`p ∈ [0, 1]` at each internal vertex. The two outgoing edges of `node p l r`
have weights `1 - p` (towards `l`) and `p` (towards `r`).

Area-law paper, `06-transport.tex`, lines 28--31. -/
inductive MeanTree (ι : Type*) where
  /-- A terminal leaf with label `j`. -/
  | leaf (j : ι) : MeanTree ι
  /-- An internal vertex with parameter `p`, first child `l`, second child `r`. -/
  | node (p : I) (l r : MeanTree ι) : MeanTree ι

namespace MeanTree

variable {ι : Type*} {n : Type*} [Fintype n] [DecidableEq n]

/-- The root matrix of a weighted binary tree with leaf inputs `A`: each internal
vertex with parameter `p` is evaluated by the weighted geometric mean `#_p` of
its children.

Area-law paper, `06-transport.tex`, lines 32--34. -/
noncomputable def eval (A : ι → Matrix n n ℂ) : MeanTree ι → Matrix n n ℂ
  | leaf j => A j
  | node p l r => geomMean p (l.eval A) (r.eval A)

@[simp] theorem eval_leaf (A : ι → Matrix n n ℂ) (j : ι) : (leaf j).eval A = A j := rfl

@[simp] theorem eval_node (A : ι → Matrix n n ℂ) (p : I) (l r : MeanTree ι) :
    (node p l r).eval A = geomMean p (l.eval A) (r.eval A) := rfl

/-- The terminal weights: the weight of a label is the sum, over the leaves
carrying it, of the products of edge weights along the root-to-leaf paths.

Area-law paper, `06-transport.tex`, lines 31--32. -/
noncomputable def weight [DecidableEq ι] : MeanTree ι → ι → ℝ
  | leaf j => Pi.single j 1
  | node p l r => (1 - (p : ℝ)) • l.weight + (p : ℝ) • r.weight

@[simp] theorem weight_leaf [DecidableEq ι] (j : ι) : (leaf j).weight = Pi.single j 1 := rfl

theorem weight_node [DecidableEq ι] (p : I) (l r : MeanTree ι) (i : ι) :
    (node p l r).weight i = (1 - (p : ℝ)) * l.weight i + p * r.weight i := rfl

/-- A label of some leaf of the tree. -/
def someLabel : MeanTree ι → ι
  | leaf j => j
  | node _ l _ => l.someLabel

/-- Terminal weights are nonnegative. -/
theorem weight_nonneg [DecidableEq ι] (T : MeanTree ι) (i : ι) : 0 ≤ T.weight i := by
  induction T with
  | leaf j => by_cases h : i = j <;> simp [h]
  | node p l r ihl ihr =>
    rw [weight_node]
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.2.2) ihl) (mul_nonneg p.2.1 ihr)

/-- **The terminal weights sum to one.**

Area-law paper, `06-transport.tex`, line 32. -/
theorem sum_weight [DecidableEq ι] [Fintype ι] (T : MeanTree ι) : ∑ i, T.weight i = 1 := by
  induction T with
  | leaf j => simp
  | node p l r ihl ihr =>
    simp only [weight_node, Finset.sum_add_distrib, ← Finset.mul_sum, ihl, ihr]
    ring

/-- The terminal weight of a label is zero unless the label occurs. Here we record the
contraction rule for a vertex whose second edge has weight zero. -/
theorem weight_node_zero [DecidableEq ι] (l r : MeanTree ι) :
    (node 0 l r).weight = l.weight := by
  ext i; simp [weight_node]

/-- Contraction rule for a vertex whose first edge has weight zero. -/
theorem weight_node_one [DecidableEq ι] (l r : MeanTree ι) :
    (node 1 l r).weight = r.weight := by
  ext i; simp [weight_node]

variable {A A' : ι → Matrix n n ℂ}

/-- **The root of a tree with positive definite inputs is positive definite.** -/
theorem posDef_eval (hA : ∀ j, (A j).PosDef) (T : MeanTree ι) : (T.eval A).PosDef := by
  induction T with
  | leaf j => exact hA j
  | node p l r ihl ihr => exact ihl.geomMean ihr p

/-- **Contraction of an edge of weight zero** at the second child: the vertex can be
replaced by its first child.

Area-law paper, `06-transport.tex`, lines 34--35. -/
theorem eval_node_zero (hA : ∀ j, (A j).PosDef) (l r : MeanTree ι) :
    (node 0 l r).eval A = l.eval A := by
  simpa using geomMean_zero (posDef_eval hA l) (posDef_eval hA r)

/-- **Contraction of an edge of weight zero** at the first child: the vertex can be
replaced by its second child.

Area-law paper, `06-transport.tex`, lines 34--35. -/
theorem eval_node_one (hA : ∀ j, (A j).PosDef) (l r : MeanTree ι) :
    (node 1 l r).eval A = r.eval A := by
  simpa using geomMean_one (posDef_eval hA l) (posDef_eval hA r)

/-- **The root commutes with invertible congruence.**

Area-law paper, Lemma 7.1 (`transport:means`), `06-transport.tex` lines 43 and
99--100. -/
theorem eval_star_conj (hA : ∀ j, (A j).PosDef) {S : Matrix n n ℂ} (hS : IsUnit S)
    (T : MeanTree ι) :
    T.eval (fun j ↦ star S * A j * S) = star S * T.eval A * S := by
  induction T with
  | leaf j => rfl
  | node p l r ihl ihr =>
    rw [eval_node, eval_node, ihl, ihr, geomMean_star_conj (posDef_eval hA l)
      (posDef_eval hA r) hS]

/-- **The root is monotone in the inputs.**

Area-law paper, Lemma 7.1 (`transport:means`), `06-transport.tex` lines 43 and
99--100. -/
theorem eval_mono (hA : ∀ j, (A j).PosDef) (hAA' : ∀ j, A j ≤ A' j) (T : MeanTree ι) :
    T.eval A ≤ T.eval A' := by
  have hA' : ∀ j, (A' j).PosDef := fun j ↦ by
    have hd : (A' j - A j).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hAA' j))
    simpa using (hA j).add_posSemidef hd
  induction T with
  | leaf j => exact hAA' j
  | node p l r ihl ihr =>
    calc geomMean p (l.eval A) (r.eval A)
        ≤ geomMean p (l.eval A) (r.eval A') :=
          geomMean_mono_right (posDef_eval hA l) p.2 ihr
      _ ≤ geomMean p (l.eval A') (r.eval A') :=
          geomMean_mono_left (posDef_eval hA l) (posDef_eval hA' r) p.2 ihl

/-- **Scalar homogeneity of the root**: `𝒯(c_j A_j : j) = (∏_j c_j ^ w_j) M` for
positive reals `c_j`.

Area-law paper, Lemma 7.1 (`transport:means`), display
`transport:scalar-homogeneity`, `06-transport.tex` lines 45--48 and 99--100. -/
theorem eval_smul [DecidableEq ι] [Fintype ι] (hA : ∀ j, (A j).PosDef) {c : ι → ℝ}
    (hc : ∀ j, 0 < c j) (T : MeanTree ι) :
    T.eval (fun j ↦ c j • A j) = (∏ j, c j ^ T.weight j) • T.eval A := by
  induction T with
  | leaf j =>
    simp only [eval_leaf, weight_leaf]
    rw [Finset.prod_eq_single j (fun i _ hij ↦ by simp [hij])
      (by simp)]
    simp
  | node p l r ihl ihr =>
    have hpos : ∀ T : MeanTree ι, 0 < ∏ j, c j ^ T.weight j := fun T ↦
      Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hc j) _
    rw [eval_node, eval_node, ihl, ihr, geomMean_smul (posDef_eval hA l) (posDef_eval hA r)
      (hpos l) (hpos r)]
    congr 1
    rw [← Real.finsetProd_rpow _ _ (fun j _ ↦ (Real.rpow_pos_of_pos (hc j) _).le),
      ← Real.finsetProd_rpow _ _ (fun j _ ↦ (Real.rpow_pos_of_pos (hc j) _).le),
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← Real.rpow_mul (hc j).le, ← Real.rpow_mul (hc j).le, ← Real.rpow_add (hc j),
      weight_node]
    ring_nf

/-- A product of nonnegative weighted powers, raised to a nonnegative power, combines
exponents. -/
private theorem prod_rpow_mul_prod_rpow [Fintype ι] {a u v : ι → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∏ j, a j ^ u j) ^ s * (∏ j, a j ^ v j) ^ t = ∏ j, a j ^ (s * u j + t * v j) := by
  rw [← Real.finsetProd_rpow _ _ (fun j _ ↦ Real.rpow_nonneg (ha j) _),
    ← Real.finsetProd_rpow _ _ (fun j _ ↦ Real.rpow_nonneg (ha j) _),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [← Real.rpow_mul (ha j), ← Real.rpow_mul (ha j),
    ← Real.rpow_add_of_nonneg (ha j) (mul_nonneg (hu j) hs) (mul_nonneg (hv j) ht)]
  ring_nf

/-- **The vector Jensen inequality for the root**: for every vector `z`,
`⟨z, M z⟩ ≤ ∏_j ⟨z, A_j z⟩ ^ w_j`.

Area-law paper, Lemma 7.1 (`transport:means`), display `transport:vector-jensen`,
`06-transport.tex` lines 49--51 and 99--100. The source states it for unit
vectors; it holds for every vector. -/
theorem re_dotProduct_eval_le [DecidableEq ι] [Fintype ι] (hA : ∀ j, (A j).PosDef)
    (T : MeanTree ι) (z : n → ℂ) :
    (star z ⬝ᵥ (T.eval A *ᵥ z)).re ≤ ∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ T.weight j := by
  have hq : ∀ X : Matrix n n ℂ, X.PosDef → 0 ≤ (star z ⬝ᵥ (X *ᵥ z)).re :=
    fun X hX ↦ hX.posSemidef.re_dotProduct_nonneg z
  induction T with
  | leaf j =>
    simp only [eval_leaf, weight_leaf]
    rw [Finset.prod_eq_single j (fun i _ hij ↦ by simp [hij]) (by simp)]
    simp
  | node p l r ihl ihr =>
    have hp0 : 0 ≤ 1 - (p : ℝ) := sub_nonneg.mpr p.2.2
    calc (star z ⬝ᵥ (geomMean p (l.eval A) (r.eval A) *ᵥ z)).re
        ≤ (star z ⬝ᵥ (l.eval A *ᵥ z)).re ^ (1 - (p : ℝ)) *
            (star z ⬝ᵥ (r.eval A *ᵥ z)).re ^ (p : ℝ) :=
          re_dotProduct_geomMean_le (posDef_eval hA l) (posDef_eval hA r) p.2 z
      _ ≤ (∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ l.weight j) ^ (1 - (p : ℝ)) *
            (∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ r.weight j) ^ (p : ℝ) := by
          gcongr <;> first
            | exact hq _ (posDef_eval hA l)
            | exact hq _ (posDef_eval hA r)
            | exact Real.rpow_nonneg (hq _ (posDef_eval hA r)) _
            | exact p.2.1
            | exact Real.rpow_nonneg (Finset.prod_nonneg fun j _ ↦
                Real.rpow_nonneg (hq _ (hA j)) _) _
      _ = ∏ j, (star z ⬝ᵥ (A j *ᵥ z)).re ^ (node p l r).weight j := by
          rw [prod_rpow_mul_prod_rpow (fun j ↦ hq _ (hA j)) l.weight_nonneg r.weight_nonneg
            hp0 p.2.1]
          simp only [weight_node]

/-- The geometric mean of a positive definite matrix with itself is that matrix. -/
private theorem geomMean_self {X : Matrix n n ℂ} (hX : X.PosDef) (p : ℝ) :
    geomMean p X X = X := by
  have h1 : X ^ (-(1 / 2) : ℝ) * X * X ^ (-(1 / 2) : ℝ) = 1 := by
    have hh := hX.rpow_half_mul_rpow_half
    calc X ^ (-(1 / 2) : ℝ) * X * X ^ (-(1 / 2) : ℝ)
        = X ^ (-(1 / 2) : ℝ) * (X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ)) * X ^ (-(1 / 2) : ℝ) := by
          rw [hh]
      _ = (X ^ (-(1 / 2) : ℝ) * X ^ (1 / 2 : ℝ)) * (X ^ (1 / 2 : ℝ) * X ^ (-(1 / 2) : ℝ)) := by
          noncomm_ring
      _ = 1 := by rw [hX.rpow_neg_mul_rpow, hX.rpow_mul_rpow_neg, one_mul]
  rw [geomMean, h1, CFC.one_rpow, mul_one, hX.rpow_half_mul_rpow_half]

/-- A tree with a constant positive definite input evaluates to that input. -/
theorem eval_const {X : Matrix n n ℂ} (hX : X.PosDef) (T : MeanTree ι) :
    T.eval (fun _ ↦ X) = X := by
  induction T with
  | leaf j => rfl
  | node p l r ihl ihr => rw [eval_node, ihl, ihr, geomMean_self hX]

/-- **Projection transfer.** If `P` is positive semidefinite and `A_j ≥ c_j P` with
`c_j > 0` for every label, then the root satisfies `M ≥ (∏_j c_j ^ w_j) P`.

Area-law paper, Lemma 7.1 (`transport:means`), display
`transport:projection-transfer`, `06-transport.tex` lines 53--56 and 102--118.
The source states this for an orthogonal projection `P`; the proof uses only
positive semidefiniteness of `P`, which every orthogonal projection has. As in
the source, the argument approximates the singular lower bounds by positive
definite inputs `(1 - ε) c_j (P + δ I)` and never evaluates the mean on singular
inputs. -/
theorem smul_le_eval [DecidableEq ι] [Fintype ι] (hA : ∀ j, (A j).PosDef)
    {P : Matrix n n ℂ} (hP : P.PosSemidef) {c : ι → ℝ} (hc : ∀ j, 0 < c j)
    (hAP : ∀ j, c j • P ≤ A j) (T : MeanTree ι) :
    (∏ j, c j ^ T.weight j) • P ≤ T.eval A := by
  cases isEmpty_or_nonempty n with
  | inl _ => exact le_of_eq (Subsingleton.elim _ _)
  | inr _ =>
  set K := ∏ j, c j ^ T.weight j
  have hK : 0 < K := Finset.prod_pos fun j _ ↦ Real.rpow_pos_of_pos (hc j) _
  -- Each input has a positive lower bound `λ_j I`.
  have hlow : ∀ j, ∃ r : ℝ, 0 < r ∧ r • (1 : Matrix n n ℂ) ≤ A j := fun j ↦ by
    obtain ⟨r, hr, hle⟩ := (CFC.exists_pos_algebraMap_le_iff (A j)
      (hA j).isHermitian.isSelfAdjoint).mpr fun x hx ↦ (hA j).isStrictlyPositive.spectrum_pos hx
    exact ⟨r, hr, by simpa [Algebra.algebraMap_eq_smul_one] using hle⟩
  choose lam hlam hlamA using hlow
  -- Step: for each `0 < ε < 1`, `(1 - ε) K P ≤ M`.
  have hstep : ∀ ε : ℝ, 0 < ε → ε < 1 → ((1 - ε) * K) • P ≤ T.eval A := by
    intro ε hε0 hε1
    have h1ε : 0 < 1 - ε := sub_pos.mpr hε1
    -- A common `δ > 0` with `(1 - ε) c_j δ ≤ ε λ_j` for all `j`.
    set δ : ℝ := Finset.univ.inf' ⟨T.someLabel, Finset.mem_univ _⟩
      (fun j ↦ ε * lam j / ((1 - ε) * c j))
    have hδ : 0 < δ := by
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' ⟨T.someLabel, Finset.mem_univ _⟩
        (fun j ↦ ε * lam j / ((1 - ε) * c j))
      rw [show δ = _ from hj]
      exact div_pos (mul_pos hε0 (hlam j)) (mul_pos h1ε (hc j))
    have hδle : ∀ j, (1 - ε) * c j * δ ≤ ε * lam j := fun j ↦ by
      have : δ ≤ ε * lam j / ((1 - ε) * c j) := Finset.inf'_le _ (Finset.mem_univ j)
      rwa [le_div_iff₀ (mul_pos h1ε (hc j)), mul_comm] at this
    set Q : Matrix n n ℂ := P + δ • 1
    have hQ : Q.PosDef := by simpa [Q, add_comm] using (PosDef.one.smul hδ).add_posSemidef hP
    -- The approximating inputs lie below the actual inputs.
    have hin : ∀ j, ((1 - ε) * c j) • Q ≤ A j := fun j ↦ by
      have hsplit : A j - ((1 - ε) * c j) • Q =
          (1 - ε) • (A j - c j • P) + (ε • A j - ((1 - ε) * c j * δ) • 1) := by
        simp only [Q, smul_add, smul_smul, smul_sub]
        module
      rw [← sub_nonneg, hsplit]
      refine add_nonneg (smul_nonneg h1ε.le (sub_nonneg.mpr (hAP j))) ?_
      rw [sub_nonneg]
      calc ((1 - ε) * c j * δ) • (1 : Matrix n n ℂ) ≤ (ε * lam j) • 1 :=
            smul_le_smul_of_nonneg_right (hδle j) zero_le_one
        _ = ε • (lam j • 1) := by rw [smul_smul]
        _ ≤ ε • A j := smul_le_smul_of_nonneg_left (hlamA j) hε0.le
    have hmono := eval_mono (A := fun j ↦ ((1 - ε) * c j) • Q)
      (fun j ↦ hQ.smul (mul_pos h1ε (hc j))) hin T
    rw [eval_smul (fun _ ↦ hQ) (fun j ↦ mul_pos h1ε (hc j)), eval_const hQ] at hmono
    have hprod : ∏ j, ((1 - ε) * c j) ^ T.weight j = (1 - ε) * K := by
      simp only [K]
      rw [Finset.prod_congr rfl (fun j _ ↦ Real.mul_rpow h1ε.le (hc j).le),
        Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos h1ε, T.sum_weight, Real.rpow_one]
    rw [hprod] at hmono
    refine le_trans ?_ hmono
    exact smul_le_smul_of_nonneg_left (le_add_of_nonneg_right
      (smul_nonneg hδ.le zero_le_one)) (mul_pos h1ε hK).le
  -- Let `ε → 0`.
  have htend : Tendsto (fun k : ℕ ↦ ((1 - 1 / ((k : ℝ) + 2)) * K) • P) atTop (𝓝 (K • P)) := by
    have h0 : Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun k ↦ ?_
      simp only [Function.comp, Nat.cast_add, Nat.cast_one]
      ring_nf
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub h0).mul_const K).smul_const P
    simpa using this
  refine le_of_tendsto' htend fun k ↦ hstep _ (by positivity) ?_
  rw [div_lt_one (by positivity)]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- A matrix commuting with every input commutes with the root. -/
theorem commute_eval_right (hA : ∀ j, (A j).PosDef) {X : Matrix n n ℂ}
    (hX : ∀ j, Commute X (A j)) (T : MeanTree ι) : Commute X (T.eval A) := by
  induction T with
  | leaf j => exact hX j
  | node p l r ihl ihr =>
    exact Commute.geomMean_right (posDef_eval hA l) (posDef_eval hA r) ihl ihr p

/-- Roots of trees whose inputs commute across two families commute. -/
theorem commute_eval_eval {ι' : Type*} {B : ι' → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef)
    (hB : ∀ j, (B j).PosDef) (hAB : ∀ j j', Commute (A j) (B j')) (T : MeanTree ι)
    (T' : MeanTree ι') : Commute (T.eval A) (T'.eval B) :=
  commute_eval_right hB (fun j' ↦ (commute_eval_right hA (fun j ↦ (hAB j j').symm) T).symm) T'

/-- **Factorization across two commuting bands.** If every input of the first family
commutes with every input of the second family, the root of the products is the
product of the roots.

Area-law paper, Lemma 7.1 (`transport:means`), `06-transport.tex` lines 57--61 and
120--128, for two bands. -/
theorem eval_mul_of_commute {B : ι → Matrix n n ℂ} (hA : ∀ j, (A j).PosDef)
    (hB : ∀ j, (B j).PosDef) (hAB : ∀ j j', Commute (A j) (B j')) (T : MeanTree ι) :
    T.eval (fun j ↦ A j * B j) = T.eval A * T.eval B := by
  induction T with
  | leaf j => rfl
  | node p l r ihl ihr =>
    rw [eval_node, eval_node, eval_node, ihl, ihr]
    exact geomMean_mul_of_commute (posDef_eval hA l) (posDef_eval hB l) (posDef_eval hA r)
      (posDef_eval hB r) (commute_eval_eval hA hB hAB l l) (commute_eval_eval hA hB hAB l r)
      (commute_eval_eval hA hB hAB r l) (commute_eval_eval hA hB hAB r r) p

/-- A product, in index order, of pairwise commuting positive definite matrices is
positive definite. -/
theorem posDef_listProd_ofFn {K : ℕ} {D : Fin K → Matrix n n ℂ} (hD : ∀ g, (D g).PosDef)
    (hcomm : ∀ g g', g ≠ g' → Commute (D g) (D g')) : (List.ofFn D).prod.PosDef := by
  induction K with
  | zero => simpa using PosDef.one
  | succ K ih =>
    rw [List.ofFn_succ, List.prod_cons]
    have hrest := ih (D := fun g ↦ D g.succ) (fun g ↦ hD _)
      (fun g g' h ↦ hcomm _ _ (fun h' ↦ h (Fin.succ_injective _ h')))
    refine (hD 0).mul_of_commute hrest (Commute.list_prod_right _ _ fun y hy ↦ ?_)
    obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
    exact hcomm _ _ (Fin.succ_ne_zero g).symm

/-- **Factorization across commuting bands.** Suppose every input is an ordered product
`A_j = ∏_g A_{j,g}` of positive definite factors, and every factor from band `g`
commutes with every factor from band `g'` whenever `g ≠ g'`. Then the root is the
product `∏_g M_g` of the roots `M_g` of the same weighted tree with inputs `A_{j,g}`.

Area-law paper, Lemma 7.1 (`transport:means`), `06-transport.tex` lines 57--61 and
120--128. -/
theorem eval_listProd_ofFn {K : ℕ} {D : ι → Fin K → Matrix n n ℂ}
    (hD : ∀ j g, (D j g).PosDef)
    (hcomm : ∀ j j' g g', g ≠ g' → Commute (D j g) (D j' g')) (T : MeanTree ι) :
    T.eval (fun j ↦ (List.ofFn (D j)).prod) = (List.ofFn fun g ↦ T.eval (D · g)).prod := by
  induction K with
  | zero => simpa using eval_const PosDef.one T
  | succ K ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    have hrest : ∀ j, (List.ofFn fun g : Fin K ↦ D j g.succ).prod.PosDef := fun j ↦
      posDef_listProd_ofFn (fun g ↦ hD j _)
        (fun g g' h ↦ hcomm j j _ _ (fun h' ↦ h (Fin.succ_injective _ h')))
    rw [eval_mul_of_commute (fun j ↦ hD j 0) hrest (fun j j' ↦
      Commute.list_prod_right _ _ fun y hy ↦ by
        obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
        exact hcomm _ _ _ _ (Fin.succ_ne_zero g).symm)]
    rw [ih (D := fun j g ↦ D j g.succ) (fun j g ↦ hD j _)
      (fun j j' g g' h ↦ hcomm _ _ _ _ (fun h' ↦ h (Fin.succ_injective _ h')))]

/-- **The band roots commute.** Under the hypotheses of `MeanTree.eval_listProd_ofFn`,
the roots `M_g` and `M_{g'}` commute whenever `g ≠ g'`.

Area-law paper, Lemma 7.1 (`transport:means`), `06-transport.tex` line 61. -/
theorem commute_eval_band {K : ℕ} {D : ι → Fin K → Matrix n n ℂ}
    (hD : ∀ j g, (D j g).PosDef)
    (hcomm : ∀ j j' g g', g ≠ g' → Commute (D j g) (D j' g')) (T : MeanTree ι) {g g' : Fin K}
    (hgg' : g ≠ g') : Commute (T.eval (D · g)) (T.eval (D · g')) :=
  commute_eval_eval (fun j ↦ hD j g) (fun j ↦ hD j g') (fun j j' ↦ hcomm j j' g g' hgg') T T

end MeanTree

end Matrix
