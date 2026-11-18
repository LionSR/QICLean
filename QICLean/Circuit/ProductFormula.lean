/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Parallel
import QICLean.Circuit.Core.LightCone
import QICLean.Analysis.HermitianProductFormula
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Product-formula circuits

Let `T : κ → Finset S` be a finite family of supports, and colour the indices so that indices of
one colour have disjoint supports: a colouring `c` with `m` colours of the graph `overlapGraph T`
in which two distinct indices are adjacent when their supports meet. Given a gate `g k` on each
support, the product-formula circuit `productCircuit c g n` makes `n` sweeps, each consisting of
the `m` colour classes in turn; the class `i` is one layer with the gates `g k`, `c k = i`, on
their disjoint supports and the identity elsewhere. The gates need not be unitary.

The circuit is unbranched, has depth at most `n m`, and, when every gate has an outcome, it has
`n |κ|` gates and meets each site `s` in `n` times as many gates as there are supports containing
`s`. For plain gates of one operator `V k` its Kraus operator is
`(∏_{k ∈ colourOrder c} V_k ⊗ 1)^n`, the colour classes in order, the head applied first,
and its Heisenberg picture is the conjugation by that operator.

For matrices `h_k` on the supports, the Trotter circuit `trotterCircuit c h t n` has the gates
`e^{-i (t/n) h_k}`. Its Kraus operator is the first-order product formula
`ProductFormula.lieEvolution` of the placed matrices `h_k ⊗ 1` in the order `colourOrder c`. For
Hermitian `h_k` its gates are unitary, and its error against `e^{-itH}`, `H = ∑_k h_k ⊗ 1`, and the
error of its Heisenberg picture against `e^{itH} A e^{-itH}` are those of the product formula. On
an operator supported on `R` its Heisenberg picture agrees with that of the Trotter circuit of
the family restricted to the supports inside any region containing the `n m`-fold
neighbourhood of `R` (`localFamilyInside`).

## Main definitions

* `QuantumCircuit.Geometry.ofSupports` — the cells `T k`, each of cost one.
* `QuantumCircuit.overlapGraph`, `QuantumCircuit.colourClass`, `QuantumCircuit.colourOrder`.
* `QuantumCircuit.colourSweeps`, `QuantumCircuit.productLayer`, `QuantumCircuit.productCircuit`.
* `QuantumCircuit.trotterGate`, `QuantumCircuit.trotterCircuit`,
  `QuantumCircuit.localFamilyInside`.

## Main results

* `QuantumCircuit.colourOrder_perm` — the colour classes list every index once.
* `QuantumCircuit.isUnbranched_productCircuit`, `QuantumCircuit.depth_productCircuit_le`,
  `QuantumCircuit.gateCount_productCircuit`, `QuantumCircuit.participation_productCircuit`.
* `QuantumCircuit.kraus_productCircuit_single`, `QuantumCircuit.dual_productCircuit_single` —
  the Kraus operator and the Heisenberg picture for plain gates.
* `QuantumCircuit.dual_productCircuit_mem_supportedOperators` — the light cone.
* `QuantumCircuit.kraus_trotterCircuit`, `QuantumCircuit.dual_trotterCircuit_eq`,
  `QuantumCircuit.forall_isUnitary_trotterCircuit`.
* `QuantumCircuit.norm_kraus_trotterCircuit_sub_le`,
  `QuantumCircuit.norm_dual_trotterCircuit_sub_le` — the Trotter errors.
* `QuantumCircuit.dual_trotterCircuit_eq_restrict`,
  `QuantumCircuit.norm_dual_trotterCircuit_sub_le_restrict` — only the light cone matters.
-/

open Matrix ManyBody ProductFormula SpectralFilter
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The geometry whose cells are the supports `T k`, each of cost one. -/
abbrev Geometry.ofSupports (T : κ → Finset S) : Geometry S where
  Cell := κ
  cell := T
  cost _ := 1

instance (T : κ → Finset S) : Fintype (Geometry.ofSupports T).Cell :=
  inferInstanceAs (Fintype κ)

/-! ### Colourings -/

/-- The overlap graph of a family of supports: distinct indices are adjacent when their supports
meet. -/
def overlapGraph (T : κ → Finset S) : SimpleGraph κ :=
  SimpleGraph.fromRel fun k l ↦ ¬Disjoint (T k) (T l)

variable {T : κ → Finset S} {m : ℕ}

omit [Fintype S] [DecidableEq S] [Fintype κ] [DecidableEq κ] in
/-- Distinct indices of one colour have disjoint supports. -/
theorem disjoint_of_colour_eq (c : (overlapGraph T).Coloring (Fin m)) {k l : κ} (hkl : k ≠ l)
    (h : c k = c l) : Disjoint (T k) (T l) := by
  by_contra hd
  exact c.valid ((SimpleGraph.fromRel_adj _ _ _).mpr ⟨hkl, Or.inl hd⟩) h

/-- The indices of the colour `i`. -/
def colourClass (c : (overlapGraph T).Coloring (Fin m)) (i : Fin m) : Finset κ :=
  Finset.univ.filter fun k ↦ c k = i

omit [Fintype S] [DecidableEq S] [DecidableEq κ] in
theorem mem_colourClass {c : (overlapGraph T).Coloring (Fin m)} {i : Fin m} {k : κ} :
    k ∈ colourClass c i ↔ c k = i := by
  simp [colourClass]

omit [Fintype S] [DecidableEq S] [DecidableEq κ] in
theorem pairwiseDisjoint_colourClass (c : (overlapGraph T).Coloring (Fin m)) (i : Fin m) :
    ((colourClass c i : Finset κ) : Set κ).PairwiseDisjoint T := by
  intro k hk l hl hkl
  exact disjoint_of_colour_eq c hkl
    ((mem_colourClass.mp hk).trans (mem_colourClass.mp hl).symm)

/-- The indices colour by colour, each colour class in the order of `Finset.toList`. -/
noncomputable def colourOrder (c : (overlapGraph T).Coloring (Fin m)) : List κ :=
  (List.ofFn fun i ↦ (colourClass c i).toList).flatten

omit [Fintype S] [DecidableEq S] [DecidableEq κ] in
theorem nodup_colourOrder (c : (overlapGraph T).Coloring (Fin m)) : (colourOrder c).Nodup := by
  refine List.nodup_flatten.mpr ⟨fun l hl ↦ ?_, List.pairwise_ofFn.mpr fun i j hij ↦ ?_⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact Finset.nodup_toList _
  · intro k hi hj
    rw [Finset.mem_toList, mem_colourClass] at hi hj
    exact absurd (hi.symm.trans hj) hij.ne

omit [Fintype S] [DecidableEq S] [DecidableEq κ] in
theorem mem_colourOrder (c : (overlapGraph T).Coloring (Fin m)) (k : κ) : k ∈ colourOrder c := by
  rw [colourOrder, List.mem_flatten]
  exact ⟨_, List.mem_ofFn.mpr ⟨c k, rfl⟩, Finset.mem_toList.mpr (mem_colourClass.mpr rfl)⟩

omit [Fintype S] [DecidableEq S] [DecidableEq κ] in
/-- The colour classes list every index exactly once. -/
theorem colourOrder_perm (c : (overlapGraph T).Coloring (Fin m)) :
    (colourOrder c).Perm Finset.univ.toList :=
  (List.perm_ext_iff_of_nodup (nodup_colourOrder c) (Finset.nodup_toList _)).mpr fun k ↦
    iff_of_true (mem_colourOrder c k) (Finset.mem_toList.mpr (Finset.mem_univ k))

/-! ### The circuit -/

/-- The colours of `n` sweeps, each through the `m` colours in order. -/
def colourSweeps (n m : ℕ) : List (Fin m) :=
  (List.replicate n (List.finRange m)).flatten

theorem length_colourSweeps (n m : ℕ) : (colourSweeps n m).length = n * m := by
  simp [colourSweeps, List.length_flatten, List.map_replicate, List.sum_replicate]

theorem sum_map_colourSweeps (n : ℕ) (F : Fin m → ℕ) :
    ((colourSweeps n m).map F).sum = n * ∑ i, F i := by
  simp [colourSweeps, List.map_flatten, List.sum_flatten, List.map_replicate, List.sum_replicate,
    Fin.sum_univ_def]

private theorem reverse_prod_flatten {M : Type*} [Monoid M] (L : List (List M)) :
    L.flatten.reverse.prod = (L.map fun l ↦ l.reverse.prod).reverse.prod := by
  induction L with
  | nil => simp
  | cons l L ih => simp [List.reverse_append, List.prod_append, ih]

theorem reverse_prod_map_colourSweeps {M : Type*} [Monoid M] (n : ℕ) (U : Fin m → M) :
    ((colourSweeps n m).map U).reverse.prod = ((List.finRange m).map U).reverse.prod ^ n := by
  rw [colourSweeps, List.map_flatten, List.map_replicate, reverse_prod_flatten, List.map_replicate,
    List.reverse_replicate, List.prod_replicate]

variable {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The layer of the colour `i`: the gates `g k`, `c k = i`, on their disjoint supports, and the
identity elsewhere. -/
def productLayer (c : (overlapGraph T).Coloring (Fin m)) (g : (k : κ) → G (T k) X X)
    (i : Fin m) : Layer (Geometry.ofSupports T) G X X :=
  Layer.ofCells (Γ := Geometry.ofSupports T) (colourClass c i) (pairwiseDisjoint_colourClass c i)
    fun b ↦ g b.1

/-- **The product-formula circuit**: `n` sweeps, each the `m` colour layers in order. -/
def productCircuit (c : (overlapGraph T).Coloring (Fin m)) (g : (k : κ) → G (T k) X X)
    (n : ℕ) : Circuit (Geometry.ofSupports T) G X X :=
  Circuit.seq ((colourSweeps n m).map (productLayer c g))

section Costs

variable (c : (overlapGraph T).Coloring (Fin m)) (g : (k : κ) → G (T k) X X) (n : ℕ)

omit [Fintype S] in
theorem isUnbranched_productCircuit : (productCircuit c g n).IsUnbranched :=
  Circuit.isUnbranched_seq _

/-- The product-formula circuit has depth at most `n m`. -/
theorem depth_productCircuit_le : (productCircuit c g n).depth ≤ n * m := by
  refine (Circuit.depth_seq_le _).trans ((List.sum_le_length_nsmul _ 1 fun d hd ↦ ?_).trans_eq ?_)
  · obtain ⟨L, -, rfl⟩ := List.mem_map.mp hd
    exact Layer.depth_le_one L
  · simp [length_colourSweeps]

omit [∀ s, Fintype (X s)] [Fintype S] in
private theorem nonempty_index_productLayer (hg : ∀ k, Nonempty (GateFamily.Outcome (g k))) :
    ∀ L ∈ (colourSweeps n m).map (productLayer c g), Nonempty L.Index := fun L hL ↦ by
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hL
  exact Layer.nonempty_index_ofCells (Γ := Geometry.ofSupports T) _ _ _ fun b ↦ hg b.1

/-- When every gate has an outcome, the product-formula circuit has `n |κ|` gates. -/
theorem gateCount_productCircuit (hg : ∀ k, Nonempty (GateFamily.Outcome (g k))) :
    (productCircuit c g n).gateCount = n * Fintype.card κ := by
  rw [Circuit.gateCount, productCircuit,
    Circuit.total_seq _ _ (nonempty_index_productLayer c g n hg), List.map_map,
    sum_map_colourSweeps]
  congr 1
  simp only [Function.comp_def, productLayer, Layer.gateCount_eq_sum, Layer.ofCells,
    Geometry.ofSupports, Finset.sum_const, smul_eq_mul, mul_one]
  exact (Finset.card_eq_sum_card_fiberwise (f := c) (t := Finset.univ)
    fun _ _ ↦ Finset.mem_univ _).symm

/-- When every gate has an outcome, the product-formula circuit meets the site `s` in `n` times
as many gates as there are supports containing `s`. -/
theorem participation_productCircuit (hg : ∀ k, Nonempty (GateFamily.Outcome (g k))) (s : S) :
    (productCircuit c g n).participation s = n * (Finset.univ.filter fun k ↦ s ∈ T k).card := by
  rw [Circuit.participation, productCircuit,
    Circuit.total_seq _ _ (nonempty_index_productLayer c g n hg), List.map_map,
    sum_map_colourSweeps]
  congr 1
  simp only [Function.comp_def, Layer.meets_eq_card, productLayer, Layer.ofCells,
    Geometry.ofSupports, zero_lt_one, and_true]
  rw [Finset.card_eq_sum_card_fiberwise (f := c) (t := Finset.univ) fun _ _ ↦ Finset.mem_univ _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [colourClass, Finset.filter_filter, Finset.filter_filter]
  simp only [and_comm]

/-- **The light cone.** If every gate and the identity are trace-preserving, the Heisenberg
picture of the product-formula circuit maps an operator supported on `R` to an operator
supported on the `n m`-fold neighbourhood of `R`. -/
theorem dual_productCircuit_mem_supportedOperators (ev : Interpretation G)
    (hTP : (productCircuit c g n).Forall ev KrausFamily.IsTP) {R : Finset S}
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R) :
    (productCircuit c g n).dual ev A ∈
      supportedOperators X ((Geometry.ofSupports T).neighbourhood^[n * m] R) :=
  supportedOperators_mono ((Circuit.lightCone_subset_neighbourhood (fun _ ↦ zero_lt_one) _ R).trans
    ((Geometry.ofSupports T).iterate_neighbourhood_mono (depth_productCircuit_le c g n) le_rfl))
    (Circuit.dual_mem_supportedOperators_lightCone ev _ (isUnbranched_productCircuit c g n) hTP hA)

end Costs

/-! ### Plain gates of one operator -/

section Single

variable (c : (overlapGraph T).Coloring (Fin m))
  (V : (k : κ) → Matrix (RegionConfig X (T k)) (RegionConfig X (T k)) ℂ) (n : ℕ)

private theorem kraus_productLayer_single (i : Fin m)
    (p : (productLayer (G := KrausGate) c (fun k ↦ KrausFamily.single (V k)) i).Index) :
    (productLayer (G := KrausGate) c (fun k ↦ KrausFamily.single (V k)) i).kraus KrausGate.ev p =
      ((colourClass c i).toList.map fun k ↦ place (T k) (V k)).reverse.prod := by
  let e : {k // k ∈ (colourClass c i).toList} → {k // k ∈ colourClass c i} :=
    fun k ↦ ⟨k.1, Finset.mem_toList.mp k.2⟩
  have he : Function.Injective e := fun a b hab ↦
    Subtype.ext (by simpa [e] using congrArg Subtype.val hab)
  refine (Layer.kraus_ofCells (Γ := Geometry.ofSupports T) KrausGate.ev _ _ _
    ((colourClass c i).toList.attach.map e).reverse
    (List.nodup_reverse.mpr ((List.nodup_attach.mpr (Finset.nodup_toList _)).map he))
    (fun b ↦ List.mem_reverse.mpr (List.mem_map.mpr
      ⟨⟨b.1, Finset.mem_toList.mpr b.2⟩, List.mem_attach _ _, rfl⟩)) p).trans ?_
  rw [List.map_reverse, List.map_map, ← List.map_reverse]
  rw [List.map_reverse]
  congr 1
  conv_rhs => rw [← List.attach_map_subtype_val (colourClass c i).toList, List.map_map]
  rfl

/-- **Plain gates.** With the gates `V k` of one operator each, the product-formula circuit has
the Kraus operator `(∏_{k ∈ colourOrder c} V_k ⊗ 1)^n`, the head of `colourOrder c` applied
first. -/
theorem kraus_productCircuit_single
    (p : (productCircuit (G := KrausGate) c (fun k ↦ KrausFamily.single (V k)) n).Index) :
    (productCircuit (G := KrausGate) c (fun k ↦ KrausFamily.single (V k)) n).kraus
        KrausGate.ev p =
      ((colourOrder c).map fun k ↦ place (T k) (V k)).reverse.prod ^ n := by
  refine (Circuit.kraus_seq_map KrausGate.ev (productLayer c _) (fun i ↦
    ((colourClass c i).toList.map fun k ↦ place (T k) (V k)).reverse.prod) (colourSweeps n m)
    (fun i _ q ↦ kraus_productLayer_single c V i q) p).trans ?_
  rw [reverse_prod_map_colourSweeps, colourOrder, List.map_flatten, List.map_ofFn,
    reverse_prod_flatten, List.map_ofFn, List.ofFn_eq_map]
  rfl

/-- **Plain gates, Heisenberg picture.** With the gates `V k` of one operator each, the
product-formula circuit has a single branch, and its Heisenberg picture is the conjugation
`A ↦ W† A W` by its Kraus operator `W`. -/
theorem dual_productCircuit_single (A : Matrix (Config X) (Config X) ℂ) :
    (productCircuit (G := KrausGate) c (fun k ↦ KrausFamily.single (V k)) n).dual
        KrausGate.ev A =
      (((colourOrder c).map fun k ↦ place (T k) (V k)).reverse.prod ^ n)ᴴ * A *
        ((colourOrder c).map fun k ↦ place (T k) (V k)).reverse.prod ^ n := by
  have hF : ∀ (P : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β],
      KrausFamily α β → Prop), (∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
        [DecidableEq β] (K : KrausFamily α β), K.Index = Unit → P K) →
      (productCircuit (G := KrausGate) c (fun k ↦ KrausFamily.single (V k)) n).Forall
        KrausGate.ev P := fun P hP ↦
    Circuit.forall_seq _ _ fun L hL ↦ by
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hL
      exact Layer.forall_ofCells _ (hP _ rfl) _ _ _ fun _ ↦ hP _ rfl
  obtain ⟨u⟩ := Circuit.nonempty_unique_index KrausGate.ev
    (hF _ fun K hK ↦ hK ▸ ⟨inferInstanceAs (Unique Unit)⟩)
  rw [Circuit.dual_eq_of_subsingleton _ _ u.default, kraus_productCircuit_single]

end Single

/-! ### The Trotter circuit -/

section Trotter

variable (c : (overlapGraph T).Coloring (Fin m))
  (h : (k : κ) → Matrix (RegionConfig X (T k)) (RegionConfig X (T k)) ℂ)

/-- The plain gate `e^{-i (t/n) h_k}` on the support `T k`. -/
noncomputable def trotterGate (t : ℝ) (n : ℕ) (k : κ) : KrausGate (T k) X X :=
  KrausFamily.single (hermitianUnitaryPath (h k) (-t / n))

/-- **The Trotter circuit**: the product-formula circuit of the gates `e^{-i (t/n) h_k}`. -/
noncomputable def trotterCircuit (t : ℝ) (n : ℕ) : Circuit (Geometry.ofSupports T) KrausGate X X :=
  productCircuit c (trotterGate h t n) n

/-- The family `h_k` for the supports inside the region `L`, and `0` for the others: its gates
outside `L` are the identity. -/
noncomputable def localFamilyInside (L : Finset S) (k : κ) :
    Matrix (RegionConfig X (T k)) (RegionConfig X (T k)) ℂ :=
  if T k ⊆ L then h k else 0

omit [DecidableEq κ] in
private theorem prod_trotterGate (t : ℝ) (n : ℕ) :
    ((colourOrder c).map fun k ↦
        place (T k) (hermitianUnitaryPath (h k) (-t / n))).reverse.prod ^ n =
      lieEvolution (fun k ↦ place (T k) (h k)) (colourOrder c) t n := by
  rw [lieEvolution_eq]
  simp only [place_hermitianUnitaryPath]

/-- The Kraus operator of the Trotter circuit is the first-order product formula for the placed
matrices in the order `colourOrder c`. -/
theorem kraus_trotterCircuit (t : ℝ) (n : ℕ) (p : (trotterCircuit c h t n).Index) :
    (trotterCircuit c h t n).kraus KrausGate.ev p =
      lieEvolution (fun k ↦ place (T k) (h k)) (colourOrder c) t n :=
  (kraus_productCircuit_single c _ n p).trans (prod_trotterGate c h t n)

/-- The Heisenberg picture of the Trotter circuit is the conjugation by its Kraus operator. -/
theorem dual_trotterCircuit_eq (t : ℝ) (n : ℕ) (A : Matrix (Config X) (Config X) ℂ) :
    (trotterCircuit c h t n).dual KrausGate.ev A =
      (lieEvolution (fun k ↦ place (T k) (h k)) (colourOrder c) t n)ᴴ * A *
        lieEvolution (fun k ↦ place (T k) (h k)) (colourOrder c) t n := by
  rw [← prod_trotterGate c h]
  exact dual_productCircuit_single (V := fun k ↦ hermitianUnitaryPath (h k) (-t / n)) c n A

variable {h} (hh : ∀ k, (h k).IsHermitian)
include hh

omit [Fintype S] in
/-- For Hermitian `h_k` the gates of the Trotter circuit are unitary. -/
theorem forall_isUnitary_trotterCircuit (t : ℝ) (n : ℕ) :
    (trotterCircuit c h t n).Forall KrausGate.ev KrausFamily.IsUnitary := by
  refine Circuit.forall_seq _ _ fun L hL ↦ ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hL
  exact Layer.forall_ofCells _ (fun {_} _ _ ↦ KrausFamily.isUnitary_single (one_mem _)) _ _ _
    fun b ↦ KrausFamily.isUnitary_single (hermitianUnitaryPath_mem_unitary (hh b.1) _)

/-- **The light cone of the Trotter circuit.** -/
theorem dual_trotterCircuit_mem_supportedOperators (t : ℝ) (n : ℕ) {R : Finset S}
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R) :
    (trotterCircuit c h t n).dual KrausGate.ev A ∈
      supportedOperators X ((Geometry.ofSupports T).neighbourhood^[n * m] R) :=
  dual_productCircuit_mem_supportedOperators c _ n KrausGate.ev
    ((forall_isUnitary_trotterCircuit c hh t n).mono fun _ ↦ KrausFamily.IsUnitary.isTP) hA

/-- **First-order Trotter error of the circuit.** For Hermitian `h_k`,
`‖U - e^{-itH}‖ ≤ t²/(2n) ∑_{i<j} ‖[h_i ⊗ 1, h_j ⊗ 1]‖` with `H = ∑_k h_k ⊗ 1`. -/
theorem norm_kraus_trotterCircuit_sub_le (t : ℝ) {n : ℕ} (hn : 0 < n)
    (p : (trotterCircuit c h t n).Index) :
    ‖(trotterCircuit c h t n).kraus KrausGate.ev p -
        hermitianUnitaryPath (∑ k, place (T k) (h k)) (-t)‖ ≤
      t ^ 2 / (2 * n) * commSum (fun k ↦ place (T k) (h k)) (colourOrder c) := by
  rw [kraus_trotterCircuit, ← gen_eq_sum _ (colourOrder_perm c)]
  exact norm_lieEvolution_sub_le (fun k ↦ isHermitian_place (hh k)) _ t hn

/-- **Local observables.** For Hermitian `h_k`, the Heisenberg picture of the Trotter circuit
differs from `e^{itH} A e^{-itH}` by at most `2 ‖A‖ t²/(2n) ∑_{i<j} ‖[h_i ⊗ 1, h_j ⊗ 1]‖`. -/
theorem norm_dual_trotterCircuit_sub_le (t : ℝ) {n : ℕ} (hn : 0 < n)
    (A : Matrix (Config X) (Config X) ℂ) :
    ‖(trotterCircuit c h t n).dual KrausGate.ev A -
        hermitianUnitaryPath (∑ k, place (T k) (h k)) t * A *
          hermitianUnitaryPath (∑ k, place (T k) (h k)) (-t)‖ ≤
      2 * ‖A‖ * (t ^ 2 / (2 * n) * commSum (fun k ↦ place (T k) (h k)) (colourOrder c)) := by
  rw [dual_trotterCircuit_eq, ← gen_eq_sum _ (colourOrder_perm c)]
  exact norm_lieEvolution_conj_sub_le (fun k ↦ isHermitian_place (hh k)) _ t hn A

omit [Fintype S] [Fintype κ] [DecidableEq κ] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
theorem isHermitian_localFamilyInside (L : Finset S) (k : κ) :
    (localFamilyInside h L k).IsHermitian := by
  rw [localFamilyInside]
  split_ifs
  · exact hh k
  · exact isHermitian_zero

omit hh

omit [Fintype κ] in
/-- Conjugating an operator supported on `R` by the product of unitaries `P k` on pairwise
disjoint supports `T k`: the factors whose supports miss `R` drop out, so the result does not
change when they are replaced, and it is supported on `R` together with the supports that meet
`R`. -/
private theorem conj_prod_of_pairwiseDisjoint {P P' : κ → Matrix (Config X) (Config X) ℂ}
    (hP : ∀ k, P k ∈ unitary (Matrix (Config X) (Config X) ℂ))
    (hP' : ∀ k, P' k ∈ unitary (Matrix (Config X) (Config X) ℂ))
    (hPs : ∀ k, P k ∈ supportedOperators X (T k)) (hPs' : ∀ k, P' k ∈ supportedOperators X (T k))
    {R : Finset S} (hnear : ∀ k, (T k ∩ R).Nonempty → P' k = P k)
    {B : Matrix (Config X) (Config X) ℂ} (hB : B ∈ supportedOperators X R) :
    ∀ l : List κ, l.Pairwise (fun a b ↦ Disjoint (T a) (T b)) →
      ((l.map P).reverse.prod)ᴴ * B * (l.map P).reverse.prod =
          ((l.map P').reverse.prod)ᴴ * B * (l.map P').reverse.prod ∧
        ((l.map P).reverse.prod)ᴴ * B * (l.map P).reverse.prod ∈
          supportedOperators X (R ∪ (l.filter fun k ↦ (T k ∩ R).Nonempty).toFinset.biUnion T)
  | [], _ => by simpa using hB
  | a :: l, hl => by
    obtain ⟨ih1, ih2⟩ := conj_prod_of_pairwiseDisjoint hP hP' hPs hPs' hnear hB l hl.of_cons
    have hc : ∀ W Q : Matrix (Config X) (Config X) ℂ,
        (W * Q)ᴴ * B * (W * Q) = Qᴴ * (Wᴴ * B * W) * Q := fun W Q ↦ by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, hc]
    set C := ((l.map P).reverse.prod)ᴴ * B * (l.map P).reverse.prod
    by_cases ha : (T a ∩ R).Nonempty
    · rw [hnear a ha, ← ih1, List.filter_cons_of_pos (by simpa using ha), List.toFinset_cons,
        Finset.biUnion_insert]
      refine ⟨rfl, mul_mem (mul_mem ?_ ?_) ?_⟩
      · exact supportedOperators_mono (by intro v hv; simp [hv])
          (star_mem (hPs a) : (P a)ᴴ ∈ _)
      · exact supportedOperators_mono (Finset.union_subset_union le_rfl
          Finset.subset_union_right) ih2
      · exact supportedOperators_mono (by intro v hv; simp [hv]) (hPs a)
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      have hdisj : Disjoint (R ∪ (l.filter fun k ↦ (T k ∩ R).Nonempty).toFinset.biUnion T)
          (T a) := by
        refine Finset.disjoint_union_left.mpr ⟨?_, ?_⟩
        · rw [disjoint_comm, Finset.disjoint_iff_inter_eq_empty]
          exact Finset.not_nonempty_iff_eq_empty.mp ha
        · refine (Finset.disjoint_biUnion_left _ _ _).mpr fun k hk ↦ ?_
          exact ((List.pairwise_cons.mp hl).1 k (List.mem_of_mem_filter
            (List.mem_toFinset.mp hk))).symm
      have hdrop : ∀ Q, Q ∈ unitary (Matrix (Config X) (Config X) ℂ) →
          Q ∈ supportedOperators X (T a) → ∀ D, D ∈ supportedOperators X
            (R ∪ (l.filter fun k ↦ (T k ∩ R).Nonempty).toFinset.biUnion T) → Qᴴ * D * Q = D := by
        intro Q hQ hQs D hD
        rw [Matrix.mul_assoc, (commute_of_mem_supportedOperators_of_disjoint hD hQs hdisj).eq,
          ← Matrix.mul_assoc, ← star_eq_conjTranspose, Unitary.star_mul_self_of_mem hQ,
          Matrix.one_mul]
      rw [hdrop _ (hP a) (hPs a) C ih2, hdrop _ (hP' a) (hPs' a) _ (ih1 ▸ ih2)]
      exact ⟨ih1, ih2⟩

/-- Conjugating by a sequence of such products, the last first: the factors whose supports miss
the growing support drop out. -/
private theorem conj_prod_seq {P P' : κ → Matrix (Config X) (Config X) ℂ}
    (hP : ∀ k, P k ∈ unitary (Matrix (Config X) (Config X) ℂ))
    (hP' : ∀ k, P' k ∈ unitary (Matrix (Config X) (Config X) ℂ))
    (hPs : ∀ k, P k ∈ supportedOperators X (T k)) (hPs' : ∀ k, P' k ∈ supportedOperators X (T k))
    {L : Finset S} (hL : ∀ k, T k ⊆ L → P' k = P k) {R : Finset S}
    {B : Matrix (Config X) (Config X) ℂ} (hB : B ∈ supportedOperators X R) :
    ∀ Ls : List (List κ), (∀ l ∈ Ls, l.Pairwise (fun a b ↦ Disjoint (T a) (T b))) →
      (Geometry.ofSupports T).neighbourhood^[Ls.length] R ⊆ L →
      ((Ls.map fun l ↦ (l.map P).reverse.prod).reverse.prod)ᴴ * B *
          (Ls.map fun l ↦ (l.map P).reverse.prod).reverse.prod =
        ((Ls.map fun l ↦ (l.map P').reverse.prod).reverse.prod)ᴴ * B *
          (Ls.map fun l ↦ (l.map P').reverse.prod).reverse.prod ∧
      ((Ls.map fun l ↦ (l.map P).reverse.prod).reverse.prod)ᴴ * B *
          (Ls.map fun l ↦ (l.map P).reverse.prod).reverse.prod ∈
        supportedOperators X ((Geometry.ofSupports T).neighbourhood^[Ls.length] R)
  | [], _, _ => by simpa using hB
  | l :: Ls, hLs, hlen => by
    set Γ := Geometry.ofSupports T
    have hlen' : Γ.neighbourhood^[Ls.length] R ⊆ L :=
      (Γ.iterate_neighbourhood_mono (Nat.le_succ _) le_rfl).trans hlen
    obtain ⟨ih1, ih2⟩ := conj_prod_seq hP hP' hPs hPs' hL hB Ls
      (fun l' hl' ↦ hLs l' (List.mem_cons_of_mem l hl')) hlen'
    have hc : ∀ W Q : Matrix (Config X) (Config X) ℂ,
        (W * Q)ᴴ * B * (W * Q) = Qᴴ * (Wᴴ * B * W) * Q := fun W Q ↦ by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, hc,
      List.length_cons]
    have hnear : ∀ k, (T k ∩ Γ.neighbourhood^[Ls.length] R).Nonempty → P' k = P k := by
      intro k hk
      refine hL k ((?_ : T k ⊆ Γ.neighbourhood^[Ls.length + 1] R).trans hlen)
      rw [Function.iterate_succ_apply']
      intro v hv
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, hv⟩)
    obtain ⟨h1, h2⟩ := conj_prod_of_pairwiseDisjoint hP hP' hPs hPs' hnear ih2 l
      (hLs l List.mem_cons_self)
    obtain ⟨h1', -⟩ := conj_prod_of_pairwiseDisjoint hP hP' hPs hPs' hnear (ih1 ▸ ih2) l
      (hLs l List.mem_cons_self)
    refine ⟨h1.trans (by rw [ih1]), supportedOperators_mono ?_ h2⟩
    rw [Function.iterate_succ_apply']
    refine Finset.union_subset (Γ.subset_neighbourhood _) fun v hv ↦ ?_
    obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hv
    have hk' := (List.mem_filter.mp (List.mem_toFinset.mp hk)).2
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hk'⟩, hvk⟩)

omit [DecidableEq κ] in
private theorem colourOrder_prod_pow (P : κ → Matrix (Config X) (Config X) ℂ) (n : ℕ) :
    ((colourOrder c).map P).reverse.prod ^ n =
      (((List.replicate n (List.ofFn fun i ↦ (colourClass c i).toList)).flatten).map
        fun l ↦ (l.map P).reverse.prod).reverse.prod := by
  rw [List.map_flatten, List.map_replicate, reverse_prod_flatten, List.map_replicate,
    List.reverse_replicate, List.prod_replicate, colourOrder, List.map_flatten,
    reverse_prod_flatten, List.map_map]
  rfl

include hh

/-- **Only the light cone matters.** For Hermitian `h_k` and an operator `A` supported on `R`, the
Heisenberg picture of the Trotter circuit agrees on `A` with that of the Trotter circuit of
`localFamilyInside h L`, for any region `L` containing the `n m`-fold neighbourhood of `R`. -/
theorem dual_trotterCircuit_eq_restrict (t : ℝ) (n : ℕ) {R L : Finset S}
    (hRL : (Geometry.ofSupports T).neighbourhood^[n * m] R ⊆ L)
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R) :
    (trotterCircuit c h t n).dual KrausGate.ev A =
      (trotterCircuit c (localFamilyInside h L) t n).dual KrausGate.ev A := by
  rw [dual_trotterCircuit_eq, dual_trotterCircuit_eq, lieEvolution_eq, lieEvolution_eq,
    colourOrder_prod_pow, colourOrder_prod_pow]
  have hlen : ((List.replicate n (List.ofFn fun i ↦ (colourClass c i).toList)).flatten).length =
      n * m := by
    simp [List.length_flatten, List.map_replicate, List.sum_replicate]
  refine (conj_prod_seq
    (fun k ↦ hermitianUnitaryPath_mem_unitary (isHermitian_place (hh k)) _)
    (fun k ↦ hermitianUnitaryPath_mem_unitary
      (isHermitian_place (isHermitian_localFamilyInside hh L k)) _)
    (fun k ↦ hermitianUnitaryPath_mem_supportedOperators (place_mem_supportedOperators _) _)
    (fun k ↦ hermitianUnitaryPath_mem_supportedOperators (place_mem_supportedOperators _) _)
    (fun k hk ↦ by simp [localFamilyInside, hk]) hA _ (fun l hl ↦ ?_) (hlen ▸ hRL)).1
  obtain ⟨l', hl', hll'⟩ := List.mem_flatten.mp hl
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ((List.eq_of_mem_replicate hl') ▸ hll')
  exact (Finset.nodup_toList _).pairwise_of_set_pairwise fun k hk l hl hkl ↦
    pairwiseDisjoint_colourClass c i (Finset.mem_toList.mp hk) (Finset.mem_toList.mp hl) hkl

/-- **Local observables, through the light cone.** For Hermitian `h_k`, an operator `A` supported
on `R` and a region `L` containing the `n m`-fold neighbourhood of `R`, the Heisenberg picture of
the Trotter circuit differs from `e^{itH} A e^{-itH}` by at most the Trotter error of the family
restricted to `L` plus the distance between the evolutions of `A` under `H_L` and `H`, where
`H_L = ∑_{T_k ⊆ L} h_k ⊗ 1`. -/
theorem norm_dual_trotterCircuit_sub_le_restrict (t : ℝ) {n : ℕ} (hn : 0 < n) {R L : Finset S}
    (hRL : (Geometry.ofSupports T).neighbourhood^[n * m] R ⊆ L)
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R) :
    ‖(trotterCircuit c h t n).dual KrausGate.ev A -
        hermitianUnitaryPath (∑ k, place (T k) (h k)) t * A *
          hermitianUnitaryPath (∑ k, place (T k) (h k)) (-t)‖ ≤
      2 * ‖A‖ * (t ^ 2 / (2 * n) *
          commSum (fun k ↦ place (T k) (localFamilyInside h L k)) (colourOrder c)) +
        ‖hermitianUnitaryPath (∑ k, place (T k) (localFamilyInside h L k)) t * A *
            hermitianUnitaryPath (∑ k, place (T k) (localFamilyInside h L k)) (-t) -
          hermitianUnitaryPath (∑ k, place (T k) (h k)) t * A *
            hermitianUnitaryPath (∑ k, place (T k) (h k)) (-t)‖ := by
  rw [dual_trotterCircuit_eq_restrict c hh t n hRL hA]
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add
    (norm_dual_trotterCircuit_sub_le c (isHermitian_localFamilyInside hh L) t hn A) le_rfl)

end Trotter

end QuantumCircuit
