/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.FiniteTree
import QICLean.Analysis.OperatorMean.MeanDerivative

/-!
# Normalized derivative maps of a finite mean tree

For a weighted binary tree whose leaves carry distinct labels, the root `M` is
differentiable in each input `A_j` along Hermitian matrices. The derivative is the
composition, along the path from the leaf to the root, of the partial derivatives of
the means at the vertices on the path. The normalized leaf map
\[
  \Phi_j(Z) = w_j^{-1}\, M^{-1/2}\, \partial_{A_j} M\bigl[A_j^{1/2} Z A_j^{1/2}\bigr]\, M^{-1/2}
\]
is the composition of the normalized edge maps along the path, the square-root
normalizations cancelling at successive vertices; it is completely positive and,
for positive terminal weight, unital.

## Main definitions

* `Matrix.MeanTree.labels` — the labels of the leaves, in order.
* `Matrix.MeanTree.derivLabel A j` — the derivative of the root in the input `A_j`.
* `Matrix.MeanTree.leafMap A j` — the normalized leaf map `Φ_j`.

## Main results

Area-law paper, Lemma 7.2 (`transport:cp`):

* `Matrix.MeanTree.hasFDerivWithinAt_eval_update` — the derivative of the root in an
  input, within the Hermitian matrices.
* `Matrix.MeanTree.derivLabel_self` — `∂_{A_j} M[A_j] = w_j M`.
* `Matrix.MeanTree.sandwich_derivLabel_eq_smul_leafMap` — display `transport:leaf-map`.
* `Matrix.MeanTree.isNPositiveMap_leafMap`, `Matrix.MeanTree.leafMap_one` — `Φ_j` is
  completely positive and unital.
* `Matrix.MeanTree.leafMap_leaf`, `Matrix.MeanTree.leafMap_node_left`,
  `Matrix.MeanTree.leafMap_node_right` — `Φ_j` is the identity along an empty path and
  composes the normalized edge maps from the leaf to the root.

## References

* *A two-dimensional area law from a global spectral gap* (September 24, 2026),
  `build/sections/06-transport.tex`, Lemma 7.2 (`transport:cp`), statement lines
  144--150 and proof lines 169--172. The proofs are written independently from the
  paper.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Set Filter Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A real power of a matrix is Hermitian: the functional calculus always returns a
positive semidefinite matrix. -/
theorem isHermitian_rpow (X : Matrix n n ℂ) (r : ℝ) : (X ^ r).IsHermitian := by
  exact (Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := X) (y := r))).isHermitian

/-- The weighted geometric mean of any two matrices is Hermitian. -/
theorem isHermitian_geomMean (p : ℝ) (A B : Matrix n n ℂ) : (geomMean p A B).IsHermitian := by
  unfold geomMean IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, (isHermitian_rpow A _).eq,
    (isHermitian_rpow _ p).eq]
  simp only [Matrix.mul_assoc]

private theorem HasFDerivWithinAt.comp_of_eq' {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G]
    [NormedSpace ℂ G] {g : F → G} {g' : F →L[ℂ] G} {f : E → F} {f' : E →L[ℂ] F}
    {s : Set E} {t : Set F} {x : E} {y : F} (hg : HasFDerivWithinAt g g' t y)
    (hf : HasFDerivWithinAt f f' s x) (hst : MapsTo f s t) (hy : f x = y) :
    HasFDerivWithinAt (g ∘ f) (g'.comp f') s x := by
  subst hy; exact hg.comp x hf hst

namespace MeanTree

variable {ι : Type*} [DecidableEq ι]

/-- The labels of the leaves of a tree, from left to right. -/
def labels : MeanTree ι → List ι
  | leaf j => [j]
  | node _ l r => l.labels ++ r.labels

omit [DecidableEq ι] in
@[simp] theorem labels_leaf (j : ι) : (leaf j : MeanTree ι).labels = [j] := rfl

omit [DecidableEq ι] in
@[simp] theorem labels_node (p : I) (l r : MeanTree ι) :
    (node p l r).labels = l.labels ++ r.labels := rfl

/-- A label that occurs at no leaf has terminal weight zero. -/
theorem weight_eq_zero_of_not_mem {T : MeanTree ι} {j : ι} (hj : j ∉ T.labels) :
    T.weight j = 0 := by
  induction T with
  | leaf i =>
    simp only [labels_leaf, List.mem_singleton] at hj
    simp [hj]
  | node p l r ihl ihr =>
    simp only [labels_node, List.mem_append, not_or] at hj
    rw [weight_node, ihl hj.1, ihr hj.2]; ring

variable {A : ι → Matrix n n ℂ}

/-- The root does not depend on an input whose label occurs at no leaf. -/
theorem eval_update_of_not_mem {T : MeanTree ι} {j : ι} (hj : j ∉ T.labels)
    (X : Matrix n n ℂ) : T.eval (Function.update A j X) = T.eval A := by
  induction T with
  | leaf i =>
    simp only [labels_leaf, List.mem_singleton] at hj
    simp [Function.update_of_ne (Ne.symm hj)]
  | node p l r ihl ihr =>
    simp only [labels_node, List.mem_append, not_or] at hj
    rw [eval_node, eval_node, ihl hj.1, ihr hj.2]

omit [DecidableEq ι] in
/-- The root of a tree with Hermitian inputs is Hermitian. -/
theorem isHermitian_eval (hA : ∀ i, (A i).IsHermitian) (T : MeanTree ι) :
    (T.eval A).IsHermitian := by
  cases T with
  | leaf i => exact hA i
  | node p l r => exact isHermitian_geomMean _ _ _

/-- The derivative of the root in the input with label `j`: along each internal vertex,
the partial derivatives of the mean in its two arguments, composed with the
derivatives of the two subtrees. -/
noncomputable def derivLabel (A : ι → Matrix n n ℂ) (j : ι) :
    MeanTree ι → Matrix n n ℂ →L[ℂ] Matrix n n ℂ
  | leaf i => if i = j then ContinuousLinearMap.id ℂ _ else 0
  | node p l r =>
    geomMeanDerivLeft p (l.eval A) (r.eval A) ∘L l.derivLabel A j +
      geomMeanDerivRight p (l.eval A) (r.eval A) ∘L r.derivLabel A j

/-- The derivative in a label that occurs at no leaf is zero. -/
theorem derivLabel_of_not_mem {T : MeanTree ι} {j : ι} (hj : j ∉ T.labels) :
    T.derivLabel A j = 0 := by
  induction T with
  | leaf i =>
    simp only [labels_leaf, List.mem_singleton] at hj
    simp [derivLabel, Ne.symm hj]
  | node p l r ihl ihr =>
    simp only [labels_node, List.mem_append, not_or] at hj
    simp [derivLabel, ihl hj.1, ihr hj.2]

/-- **The derivative of the root in one input.** For a tree with distinct leaf labels
and positive definite inputs, the root is differentiable in the input `A_j` within the
Hermitian matrices, with derivative `derivLabel A j`.

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 144--150 and
169--171 (chain rule). -/
theorem hasFDerivWithinAt_eval_update (hA : ∀ i, (A i).PosDef) (T : MeanTree ι)
    (hT : T.labels.Nodup) (j : ι) :
    HasFDerivWithinAt (fun X ↦ T.eval (Function.update A j X)) (T.derivLabel A j)
      (hermitianSet n) (A j) := by
  induction T with
  | leaf i =>
    by_cases hij : i = j
    · subst hij
      simp only [derivLabel, ↓reduceIte, eval_leaf, Function.update_self]
      exact hasFDerivWithinAt_id (𝕜 := ℂ) (A i) (hermitianSet n)
    · simpa [derivLabel, hij, Function.update_of_ne hij] using
        hasFDerivWithinAt_const (𝕜 := ℂ) (A i) (A j) (hermitianSet n)
  | node p l r ihl ihr =>
    simp only [labels_node, List.nodup_append] at hT
    obtain ⟨hl, hr, hdisj⟩ := hT
    have hmaps : ∀ T' : MeanTree ι, MapsTo (fun X ↦ T'.eval (Function.update A j X))
        (hermitianSet n) (hermitianSet n) := fun T' X hX ↦ by
      refine isHermitian_eval (fun i ↦ ?_) T'
      by_cases hij : i = j
      · subst hij; simpa [hermitianSet] using hX
      · simpa [Function.update_of_ne hij] using (hA i).isHermitian
    have hpt : ∀ T' : MeanTree ι, T'.eval (Function.update A j (A j)) = T'.eval A := by
      intro T'; rw [Function.update_eq_self]
    by_cases hjl : j ∈ l.labels
    · have hjr : j ∉ r.labels := fun h ↦ hdisj j hjl j h rfl
      have hfun : (fun X ↦ (node p l r).eval (Function.update A j X)) =
          (fun Y ↦ geomMean p Y (r.eval A)) ∘ fun X ↦ l.eval (Function.update A j X) := by
        ext1 X; simp [eval_update_of_not_mem hjr]
      rw [hfun]
      have := HasFDerivWithinAt.comp_of_eq'
        (hasFDerivWithinAt_geomMean_left (posDef_eval hA l) (posDef_eval hA r) p.2)
        (ihl hl) (hmaps l) (hpt l)
      simpa [derivLabel, derivLabel_of_not_mem hjr] using this
    · have hfun : (fun X ↦ (node p l r).eval (Function.update A j X)) =
          (fun Y ↦ geomMean p (l.eval A) Y) ∘ fun X ↦ r.eval (Function.update A j X) := by
        ext1 X; simp [eval_update_of_not_mem hjl]
      rw [hfun]
      have := HasFDerivWithinAt.comp_of_eq'
        (hasFDerivWithinAt_geomMean_right (posDef_eval hA l) (posDef_eval hA r) p.2)
        (ihr hr) (hmaps r) (hpt r)
      simpa [derivLabel, derivLabel_of_not_mem hjl] using this

/-- **Euler identity for the root**: `∂_{A_j} M[A_j] = w_j M`.

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex` line 169,
propagated along the tree. -/
theorem derivLabel_self (hA : ∀ i, (A i).PosDef) (T : MeanTree ι) (j : ι) :
    T.derivLabel A j (A j) = T.weight j • T.eval A := by
  induction T with
  | leaf i =>
    by_cases hij : i = j
    · subst hij; simp [derivLabel]
    · simp [derivLabel, hij, Ne.symm hij]
  | node p l r ihl ihr =>
    simp only [derivLabel, _root_.add_apply, ContinuousLinearMap.comp_apply,
      ihl, ihr, ContinuousLinearMap.map_smul_of_tower, eval_node]
    rw [geomMeanDerivLeft_self (posDef_eval hA l) (posDef_eval hA r) p.2,
      geomMeanDerivRight_self (posDef_eval hA l) (posDef_eval hA r) p.2, weight_node,
      smul_smul, smul_smul, ← add_smul]
    congr 1; ring

/-- The derivative of the root in one input is `k`-positive for every `k`. -/
theorem isNPositiveMap_derivLabel (hA : ∀ i, (A i).PosDef) (T : MeanTree ι) (j : ι)
    (k : ℕ) : IsNPositiveMap k (T.derivLabel A j).toLinearMap := by
  induction T with
  | leaf i =>
    unfold derivLabel
    split_ifs
    · exact isNPositiveMap_id k
    · simpa using IsNPositiveMap.zero (n := n) k
  | node p l r ihl ihr =>
    have h1 := isNPositiveMap_geomMeanDerivLeft (posDef_eval hA l) (posDef_eval hA r) p.2 k
    have h2 := isNPositiveMap_geomMeanDerivRight (posDef_eval hA l) (posDef_eval hA r) p.2 k
    rw [derivLabel, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_comp,
      ContinuousLinearMap.toLinearMap_comp]
    exact (IsNPositiveMap.comp h1 ihl).add (IsNPositiveMap.comp h2 ihr)

/-- The normalized leaf map
`Φ_j(Z) = w_j⁻¹ M^{-1/2} ∂_{A_j} M[A_j^{1/2} Z A_j^{1/2}] M^{-1/2}`. -/
noncomputable def leafMap (A : ι → Matrix n n ℂ) (j : ι) (T : MeanTree ι) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  normalizedDerivMap (T.derivLabel A j) (T.weight j) (T.eval A) (A j)

/-- **The leaf identity** `M^{-1/2} ∂_{A_j} M[A_j^{1/2} Z A_j^{1/2}] M^{-1/2} = w_j Φ_j(Z)`
for a label of positive terminal weight.

Area-law paper, display `transport:leaf-map`, `06-transport.tex` lines 147--149. -/
theorem sandwich_derivLabel_eq_smul_leafMap (T : MeanTree ι) {j : ι} (hw : T.weight j ≠ 0)
    (Z : Matrix n n ℂ) :
    T.eval A ^ (-(1 / 2) : ℝ) * T.derivLabel A j (A j ^ (1 / 2 : ℝ) * Z * A j ^ (1 / 2 : ℝ)) *
        T.eval A ^ (-(1 / 2) : ℝ) = T.weight j • T.leafMap A j Z := by
  simp only [leafMap, normalizedDerivMap, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, sandwichL_apply, smul_smul, mul_inv_cancel₀ hw, one_smul]

/-- **The leaf map is completely positive.**

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 144--147 and
171--172. -/
theorem isNPositiveMap_leafMap (hA : ∀ i, (A i).PosDef) (T : MeanTree ι) (j : ι) (k : ℕ) :
    IsNPositiveMap k (T.leafMap A j).toLinearMap :=
  isNPositiveMap_normalizedDerivMap (isNPositiveMap_derivLabel hA T j k) (T.weight_nonneg j)
    (posDef_eval hA T) (hA j)

/-- **The leaf map is unital** for a label of positive terminal weight.

Area-law paper, Lemma 7.2 (`transport:cp`), `06-transport.tex` lines 144--147 and
169--172. -/
theorem leafMap_one (hA : ∀ i, (A i).PosDef) (T : MeanTree ι) {j : ι}
    (hw : T.weight j ≠ 0) : T.leafMap A j 1 = 1 :=
  normalizedDerivMap_one hw (posDef_eval hA T) (hA j) (derivLabel_self hA T j)

/-- **Along an empty path the leaf map is the identity.**

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex` line 172. -/
theorem leafMap_leaf (hA : ∀ i, (A i).PosDef) (j : ι) (Z : Matrix n n ℂ) :
    (leaf j : MeanTree ι).leafMap A j Z = Z := by
  have h1 := (hA j).rpow_neg_mul_rpow (1 / 2)
  have h2 := (hA j).rpow_mul_rpow_neg (1 / 2)
  simp only [leafMap, normalizedDerivMap, derivLabel, ↓reduceIte, weight_leaf,
    Pi.single_eq_same, inv_one, one_smul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, sandwichL_apply, eval_leaf]
  calc A j ^ (-(1 / 2) : ℝ) * (A j ^ (1 / 2 : ℝ) * Z * A j ^ (1 / 2 : ℝ)) *
        A j ^ (-(1 / 2) : ℝ)
      = (A j ^ (-(1 / 2) : ℝ) * A j ^ (1 / 2 : ℝ)) * Z *
          (A j ^ (1 / 2 : ℝ) * A j ^ (-(1 / 2) : ℝ)) := by noncomm_ring
    _ = Z := by rw [h1, h2, one_mul, mul_one]

/-- The normalized edge map at the first child of `node p l r`. -/
noncomputable def edgeMapLeft (A : ι → Matrix n n ℂ) (p : I) (l r : MeanTree ι) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  normalizedDerivMap (geomMeanDerivLeft p (l.eval A) (r.eval A)) (1 - p)
    ((node p l r).eval A) (l.eval A)

/-- The normalized edge map at the second child of `node p l r`. -/
noncomputable def edgeMapRight (A : ι → Matrix n n ℂ) (p : I) (l r : MeanTree ι) :
    Matrix n n ℂ →L[ℂ] Matrix n n ℂ :=
  normalizedDerivMap (geomMeanDerivRight p (l.eval A) (r.eval A)) p
    ((node p l r).eval A) (r.eval A)

/-- Composition of normalized maps: the square-root normalizations cancel at the
middle vertex. -/
private theorem normalizedDerivMap_comp {L₁ L₂ : Matrix n n ℂ →L[ℂ] Matrix n n ℂ}
    {w₁ w₂ : ℝ} {M D E : Matrix n n ℂ} (hD : D.PosDef) (Z : Matrix n n ℂ) :
    normalizedDerivMap L₁ w₁ M D (normalizedDerivMap L₂ w₂ D E Z) =
      normalizedDerivMap (L₁ ∘L L₂) (w₁ * w₂) M E Z := by
  have h1 := hD.rpow_mul_rpow_neg (1 / 2)
  have h2 := hD.rpow_neg_mul_rpow (1 / 2)
  have key : ∀ Y : Matrix n n ℂ,
      D ^ (1 / 2 : ℝ) * (D ^ (-(1 / 2) : ℝ) * Y * D ^ (-(1 / 2) : ℝ)) * D ^ (1 / 2 : ℝ) = Y := by
    intro Y
    calc D ^ (1 / 2 : ℝ) * (D ^ (-(1 / 2) : ℝ) * Y * D ^ (-(1 / 2) : ℝ)) * D ^ (1 / 2 : ℝ)
        = (D ^ (1 / 2 : ℝ) * D ^ (-(1 / 2) : ℝ)) * Y * (D ^ (-(1 / 2) : ℝ) * D ^ (1 / 2 : ℝ)) := by
          noncomm_ring
      _ = Y := by rw [h1, h2, one_mul, mul_one]
  simp only [normalizedDerivMap, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    sandwichL_apply]
  rw [mul_smul_comm, smul_mul_assoc, key, ContinuousLinearMap.map_smul_of_tower, mul_smul_comm,
    smul_mul_assoc, smul_smul, mul_inv]

/-- **Composition from the leaf to the root, first child.** If the label `j` occurs in
the first subtree, the leaf map of `node p l r` is the normalized edge map at the
first child composed with the leaf map of `l`.

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex`
lines 170--172. -/
theorem leafMap_node_left (hA : ∀ i, (A i).PosDef) (p : I) (l r : MeanTree ι) {j : ι}
    (hjr : j ∉ r.labels) (Z : Matrix n n ℂ) :
    (node p l r).leafMap A j Z = edgeMapLeft A p l r (l.leafMap A j Z) := by
  simp only [edgeMapLeft, leafMap]
  rw [normalizedDerivMap_comp (posDef_eval hA l)]
  simp [derivLabel, derivLabel_of_not_mem hjr, weight_node, weight_eq_zero_of_not_mem hjr]

/-- **Composition from the leaf to the root, second child.** If the label `j` occurs in
the second subtree, the leaf map of `node p l r` is the normalized edge map at the
second child composed with the leaf map of `r`.

Area-law paper, proof of Lemma 7.2 (`transport:cp`), `06-transport.tex`
lines 170--172. -/
theorem leafMap_node_right (hA : ∀ i, (A i).PosDef) (p : I) (l r : MeanTree ι) {j : ι}
    (hjl : j ∉ l.labels) (Z : Matrix n n ℂ) :
    (node p l r).leafMap A j Z = edgeMapRight A p l r (r.leafMap A j Z) := by
  simp only [edgeMapRight, leafMap]
  rw [normalizedDerivMap_comp (posDef_eval hA r)]
  simp [derivLabel, derivLabel_of_not_mem hjl, weight_node, weight_eq_zero_of_not_mem hjl]

end MeanTree

end Matrix
