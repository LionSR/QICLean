/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RegionSplit
import QICLean.Entropy.ConditionalSkewPhase
import QICLean.Representation.MarkedSimilaritySymbol

/-!
# The skew bound of Lemma 6.4

Lemma 6.4 of the area-law paper (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, lines 640–660 and 838–843) finishes by applying the conditional skew estimate
(Lemma 5.3) pointwise to the symbol `f_θ`. Lemma 5.3 is stated on tensor factors
`(P₀ P₁)((x U) F)`; this file reads it on regions of `V`, for a partition `P = P₀ P₁`,
`Y = x U`, `F` and an operator `0 ≤ h ≤ 1` supported on `P₀ x`.

## Main declarations

* `TensorPower.SkewPartition`, `TensorPower.SkewPartition.equiv` — the coordinates.
* `TensorPower.SkewPartition.skewFun_eq_markedScalarSymbol` — `f_θ` is the function of
  Lemma 5.3 in these coordinates.
* `TensorPower.SkewPartition.markedScalarSymbol_skew_le` — Lemma 5.3 for `f_θ`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 5.3 (`lem:skew`), `04-conditional.tex`, lines 487–507, and Lemma 6.4 (`lem:symbol`),
  `05-replicas.tex`, lines 640–660 and 838–843.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix Entropy Entropy.ConditionalSkew
open scoped Kronecker ComplexOrder MatrixOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

/-- A partition `V = (P₀ ∪ P₁) ∪ (x ∪ U) ∪ F` into the regions of Lemmas 5.3 and 6.4. -/
structure SkewPartition (P₀ P₁ x U F : Finset V) : Prop where
  P₀P₁ : Disjoint P₀ P₁
  xU : Disjoint x U
  PY : Disjoint (P₀ ∪ P₁) (x ∪ U)
  PF : Disjoint (P₀ ∪ P₁) F
  YF : Disjoint (x ∪ U) F
  cover : ∀ v, v ∈ P₀ ∪ P₁ ∨ v ∈ x ∪ U ∨ v ∈ F

namespace SkewPartition

variable {P₀ P₁ x U F : Finset V} (hp : SkewPartition P₀ P₁ x U F)
include hp

omit [Fintype V] in
theorem P_W : Disjoint (P₀ ∪ P₁) ((x ∪ U) ∪ F) := Finset.disjoint_union_right.mpr ⟨hp.PY, hp.PF⟩

omit [Fintype V] in
theorem cover_P (v : V) : v ∈ P₀ ∪ P₁ ∨ v ∈ (x ∪ U) ∪ F := by
  rcases hp.cover v with h | h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_union_left _ h)
  · exact Or.inr (Finset.mem_union_right _ h)

omit [Fintype V] in
theorem P₀x : Disjoint P₀ x :=
  Finset.disjoint_of_subset_left Finset.subset_union_left
    (Finset.disjoint_of_subset_right Finset.subset_union_left hp.PY)

/-- The coordinates `V ≅ (P₀ P₁)((x U) F)`. -/
def equiv : SiteConfig n ≃ (RegionConfig n P₀ × RegionConfig n P₁) ×
    ((RegionConfig n x × RegionConfig n U) × RegionConfig n F) :=
  (regionSplitEquiv hp.P_W hp.cover_P).trans (Equiv.prodCongr (regionUnionEquiv hp.P₀P₁)
    ((regionUnionEquiv hp.YF).trans (Equiv.prodCongr (regionUnionEquiv hp.xU) (Equiv.refl _))))

omit [Fintype V] in
theorem isRegionSplit_P :
    IsRegionSplit (P₀ ∪ P₁) (regionUnionEquiv hp.P₀P₁) (SkewPartition.equiv (n := n) hp) := by
  have h := (isRegionSplit_regionSplitEquiv (n := n) hp.P_W hp.cover_P).trans_prodCongr
    (regionUnionEquiv hp.P₀P₁)
    ((regionUnionEquiv hp.YF).trans (Equiv.prodCongr (regionUnionEquiv hp.xU) (Equiv.refl _)))
  rwa [Equiv.refl_trans] at h

omit [Fintype V] in
theorem equiv_apply (σ : SiteConfig n) :
    SkewPartition.equiv hp σ = (((fun v : {v // v ∈ P₀} => σ v), (fun v : {v // v ∈ P₁} => σ v)),
      (((fun v : {v // v ∈ x} => σ v), (fun v : {v // v ∈ U} => σ v)),
        (fun v : {v // v ∈ F} => σ v))) := rfl

omit [Fintype V] [DecidableEq V] hp in
theorem restrict_eq_iff {D : Finset V} {σ τ : SiteConfig n} :
    ((fun v : {v // v ∈ D} => σ v) = fun v : {v // v ∈ D} => τ v) ↔ ∀ v ∈ D, σ v = τ v :=
  ⟨fun h v hv => congrFun h ⟨v, hv⟩, fun h => funext fun v => h v.1 v.2⟩

omit [Fintype V] in
theorem mem_cases (v : V) : v ∈ P₀ ∨ v ∈ P₁ ∨ v ∈ x ∨ v ∈ U ∨ v ∈ F := by
  rcases hp.cover v with h | h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases Finset.mem_union.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

omit [Fintype V] in
theorem not_mem_of_mem {v : V} :
    (v ∈ P₀ → v ∉ P₁ ∧ v ∉ x ∧ v ∉ U ∧ v ∉ F) ∧ (v ∈ P₁ → v ∉ P₀ ∧ v ∉ x ∧ v ∉ U ∧ v ∉ F) ∧
    (v ∈ x → v ∉ P₀ ∧ v ∉ P₁ ∧ v ∉ U ∧ v ∉ F) ∧ (v ∈ U → v ∉ P₀ ∧ v ∉ P₁ ∧ v ∉ x ∧ v ∉ F) ∧
    (v ∈ F → v ∉ P₀ ∧ v ∉ P₁ ∧ v ∉ x ∧ v ∉ U) := by
  have d01 : v ∈ P₀ → v ∉ P₁ := fun h => Finset.disjoint_left.mp hp.P₀P₁ h
  have dxU : v ∈ x → v ∉ U := fun h => Finset.disjoint_left.mp hp.xU h
  have dPY : v ∈ P₀ ∪ P₁ → v ∉ x ∪ U := fun h => Finset.disjoint_left.mp hp.PY h
  have dPF : v ∈ P₀ ∪ P₁ → v ∉ F := fun h => Finset.disjoint_left.mp hp.PF h
  have dYF : v ∈ x ∪ U → v ∉ F := fun h => Finset.disjoint_left.mp hp.YF h
  simp only [Finset.mem_union] at dPY dPF dYF
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h' <;> tauto

/-- `(P₀ P₁)((x U) F) ≃ (x U)((P₀ P₁) F)`. -/
def regroupY {A₀ A₁ X' U' F' : Type*} :
    (A₀ × A₁) × ((X' × U') × F') ≃ (X' × U') × ((A₀ × A₁) × F') where
  toFun q := (q.2.1, (q.1, q.2.2))
  invFun r := (r.2.1, (r.1, r.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- `(P₀ P₁)((x U) F) ≃ (P₀ x)(P₁ (U F))`, the regrouping of Lemma 5.3. -/
def regroupH {A₀ A₁ X' U' F' : Type*} :
    (A₀ × A₁) × ((X' × U') × F') ≃ (A₀ × X') × (A₁ × (U' × F')) where
  toFun := regroup
  invFun r := ((r.1.1, r.2.1), ((r.1.2, r.2.2.1), r.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
theorem isRegionSplit_Y : IsRegionSplit (x ∪ U) (regionUnionEquiv hp.xU)
    ((SkewPartition.equiv (n := n) hp).trans regroupY) where
  fst σ := rfl
  snd σ τ := by
    simp only [Equiv.trans_apply, equiv_apply, regroupY, Equiv.coe_fn_mk, Prod.mk.injEq,
      restrict_eq_iff]
    constructor
    · rintro ⟨⟨h0, h1⟩, hF⟩ v hv
      rcases hp.mem_cases v with h | h | h | h | h
      · exact h0 v h
      · exact h1 v h
      · exact absurd (Finset.mem_union_left _ h) hv
      · exact absurd (Finset.mem_union_right _ h) hv
      · exact hF v h
    · intro h
      have nm := fun v => hp.not_mem_of_mem (v := v)
      refine ⟨⟨fun v hv => h v ?_, fun v hv => h v ?_⟩, fun v hv => h v ?_⟩ <;>
        simp only [Finset.mem_union, not_or] <;> have := nm v <;> tauto

omit [Fintype V] in
theorem isRegionSplit_H : IsRegionSplit (P₀ ∪ x) (regionUnionEquiv hp.P₀x)
    ((SkewPartition.equiv (n := n) hp).trans regroupH) where
  fst σ := rfl
  snd σ τ := by
    change ((fun v : {v // v ∈ P₁} => σ v), ((fun v : {v // v ∈ U} => σ v),
        (fun v : {v // v ∈ F} => σ v))) = ((fun v : {v // v ∈ P₁} => τ v),
        ((fun v : {v // v ∈ U} => τ v), (fun v : {v // v ∈ F} => τ v))) ↔ _
    simp only [Prod.mk.injEq, restrict_eq_iff]
    constructor
    · rintro ⟨h1, hU, hF⟩ v hv
      rcases hp.mem_cases v with h | h | h | h | h
      · exact absurd (Finset.mem_union_left _ h) hv
      · exact h1 v h
      · exact absurd (Finset.mem_union_right _ h) hv
      · exact hU v h
      · exact hF v h
    · intro h
      have nm := fun v => hp.not_mem_of_mem (v := v)
      refine ⟨fun v hv => h v ?_, fun v hv => h v ?_, fun v hv => h v ?_⟩ <;>
        simp only [Finset.mem_union, not_or] <;> have := nm v <;> tauto

end SkewPartition

end TensorPower
