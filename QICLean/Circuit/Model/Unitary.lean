/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.LightCone
import QICLean.Circuit.Core.LocalGate
import QICLean.Circuit.Core.Parallel
import QICLean.Circuit.Core.Seq
import QICLean.ManyBody.Sites.PlaceAlong

/-!
# Unitary circuits

A unitary circuit on a geometry `Γ` on the system `X` is the restriction of `Circuit` in which
every layer goes from `X` to `X` and every gate and onsite family has a single unitary Kraus
operator. It is the sequence of its layers, `Circuit.seq`, so it has one branch, and its
operator is the Kraus operator of that branch: the product of the operators of the layers, the
first layer on the right. Its depth and gate count are those of the circuit. A one-site unitary
is an onsite family and costs nothing.

Two classes of matrices are defined from it. A matrix `U` is a unitary circuit of depth `T`
when some unitary circuit of depth at most `T` has operator `U`, and a product of gates of cost
`K` when some unitary circuit of gate count at most `K` has operator `U`. On a ring these are
the local circuits of depth `T` of arXiv:2307.01696 (main text before Theorem 1); on the edges
of a graph they are the depth-`ℓ` circuits of arXiv:2103.13367 (Definition "Depth-`ℓ` quantum
circuits"); on the edges of a path they are the products of two-site gates on neighbouring
sites of an open chain. Every statement "of depth `T`" means depth at most `T`, so both classes
are monotone in the bound.

The identity, composition, monotonicity and the light cone are the theorems of the circuit
core: the composition is the concatenation of the sequences of layers, whose costs add
(`Circuit.total_seq`), and the light cone is `Circuit.dual_mem_supportedOperators_lightCone`
for the Heisenberg picture `A ↦ Uᴴ A U` of the one branch. The adjoint is the sequence of the
adjoint layers in reverse order (`Circuit.seqAdjoint`), of the same depth and gate count, since
the costs depend only on the cells.

A vector is prepared in depth `T` when it is a unitary circuit of depth `T` applied to a product
vector; when the cells have positive cost, connected correlations of operators on regions with
disjoint `T`-fold neighbourhoods vanish in it (arXiv:2307.01696, Supplemental Material, proof of
Theorem 1).

The declarations restate on the circuit core `BondLayer`, `circuitOp`, `IsBondCircuitOfDepth`
and `IsBondPreparedInDepth` of `TNLean/Circuit/LocalCircuit.lean`, and `IsPairProduct` of
`TNLean/Circuit/PairProduct.lean`, at commit `414a18fb88` (Apache-2.0). The changes: any
geometry, any finite basis at each site, and depth or gate count at most the bound in place of
exactly `T` layers or a list of at most `K` gates; one-site unitaries are onsite families of
cost `0`.

## Main definitions

* `QuantumCircuit.UnitaryCircuit` — the unitary restriction of `Circuit`.
* `QuantumCircuit.UnitaryCircuit.op`, `QuantumCircuit.UnitaryCircuit.depth`,
  `QuantumCircuit.UnitaryCircuit.gateCount` — its operator and costs.
* `QuantumCircuit.UnitaryCircuit.id`, `QuantumCircuit.UnitaryCircuit.comp`,
  `QuantumCircuit.UnitaryCircuit.adjoint`, `QuantumCircuit.UnitaryCircuit.gate`,
  `QuantumCircuit.UnitaryCircuit.onsite` — the circuits used to build others.
* `QuantumCircuit.IsUnitaryCircuit` — a unitary circuit of depth at most `T`.
* `QuantumCircuit.IsGateProduct` — a product of gates of total cost at most `K`.
* `QuantumCircuit.IsPreparedInDepth` — a vector prepared from a product vector in depth `T`.

## Main results

* `QuantumCircuit.UnitaryCircuit.op_comp`, `QuantumCircuit.UnitaryCircuit.op_adjoint`,
  `QuantumCircuit.UnitaryCircuit.op_mem_unitaryGroup`.
* `QuantumCircuit.UnitaryCircuit.depth_eq_sum`, `QuantumCircuit.UnitaryCircuit.gateCount_eq_sum`,
  `QuantumCircuit.UnitaryCircuit.depth_le_gateCount`.
* `QuantumCircuit.IsGateProduct.place_singleton`, `QuantumCircuit.IsGateProduct.smul_one` — a
  one-site unitary and a global phase cost nothing.
* `QuantumCircuit.UnitaryCircuit.conjTranspose_mul_mul_mem_supportedOperators` — the light cone.
* `QuantumCircuit.IsGateProduct.isUnitaryCircuit` — a product of gates of total cost at most `K`
  has depth at most `K`.
* `QuantumCircuit.dotProduct_prod_mul_mul` — a product vector over disjoint regions.
* `QuantumCircuit.IsPreparedInDepth.dotProduct_mul_mul`,
  `QuantumCircuit.IsPreparedInDepth.dotProduct_mul_eq` — vanishing connected correlations.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-! ### Unitary layers -/

namespace Layer

omit [Fintype S] in
/-- A layer whose gates and onsite families are unitary has exactly one Kraus index. -/
theorem nonempty_unique_index_of_forall_isUnitary {Y : S → Type} [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] {L : Layer Γ KrausGate X Y}
    (h : L.Forall KrausGate.ev KrausFamily.IsUnitary) : Nonempty (Unique L.Index) := by
  have i₁ : ∀ b : L.cells, Unique (GateFamily.Outcome (L.gate b)) := fun b ↦ (h.1 b).1.some
  have i₂ : ∀ s : L.Free, Unique (L.onsite s).Index := fun s ↦ (h.2 s).1.some
  exact ⟨{ default := (fun b ↦ (i₁ b).default, fun s ↦ (i₂ s).default)
           uniq := fun ⟨f, g⟩ ↦ Prod.ext (funext fun b ↦ (i₁ b).uniq (f b))
             (funext fun s ↦ (i₂ s).uniq (g s)) }⟩

omit [Fintype S] in
/-- The adjoint of a unitary layer is unitary. -/
theorem forall_isUnitary_adjoint {Y : S → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    {L : Layer Γ KrausGate X Y} (h : L.Forall KrausGate.ev KrausFamily.IsUnitary) :
    L.adjoint.Forall KrausGate.ev KrausFamily.IsUnitary :=
  ⟨fun b ↦ (h.1 b).adjoint, fun s ↦ (h.2 s).adjoint⟩

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
/-- The adjoint of a layer has the depth of the layer. -/
@[simp] theorem depth_adjoint {Y : S → Type} (L : Layer Γ KrausGate X Y) :
    L.adjoint.depth = L.depth :=
  rfl

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
/-- The adjoint of a layer has the gate count of the layer. -/
@[simp] theorem gateCount_adjoint {Y : S → Type} (L : Layer Γ KrausGate X Y) :
    L.adjoint.gateCount = L.gateCount :=
  rfl

omit [Fintype S] in
/-- A layer of one unitary gate is unitary. -/
theorem forall_isUnitary_single (b : Γ.Cell)
    {V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ}
    (hV : V ∈ unitaryGroup _ ℂ) :
    (single b (KrausFamily.single V) : Layer Γ KrausGate X X).Forall KrausGate.ev
      KrausFamily.IsUnitary :=
  forall_single (P := KrausFamily.IsUnitary) KrausGate.ev
    (KrausFamily.isUnitary_single (one_mem _)) b (KrausFamily.single V)
    (KrausFamily.isUnitary_single hV)

omit [Fintype S] in
/-- A layer of one-site unitaries is unitary. -/
theorem forall_isUnitary_ofOnsite {u : (s : S) → Matrix (X s) (X s) ℂ}
    (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ) :
    (ofOnsite fun s ↦ KrausFamily.single (u s) : Layer Γ KrausGate X X).Forall
      KrausGate.ev KrausFamily.IsUnitary :=
  ⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun s ↦ KrausFamily.isUnitary_single (hu s.1)⟩

end Layer

omit [Fintype S] in
/-- The sequence of a concatenation of layers is the composition of the sequences. -/
theorem Circuit.seq_append :
    (Ls Ls' : List (Layer Γ KrausGate X X)) →
      Circuit.seq (Ls ++ Ls') = (Circuit.seq Ls).comp (Circuit.seq Ls')
  | [], _ => rfl
  | L :: Ls, Ls' => congrArg (Circuit.step L) (funext fun _ ↦ Circuit.seq_append Ls Ls')

/-! ### Unitary circuits -/

variable (Γ X) in
/-- A unitary circuit on the geometry `Γ` on the system `X`: a sequence of layers of plain gates
from `X` to `X` whose gates and onsite families are unitary. It is the restriction of `Circuit`
in which every Kraus family has one unitary member and the system does not change; the circuit
is `Circuit.seq` of the layers.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits"), and
arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (`V = V_ℓ ⋯ V_2 V_1`, each
layer containing "quantum gates acting on disjoint pairs of nearest-neighbor spins"), with the
pairs replaced by the cells of `Γ`. -/
structure UnitaryCircuit where
  /-- The layers, in the order applied. -/
  layers : List (Layer Γ KrausGate X X)
  /-- Every gate and onsite family is unitary. -/
  isUnitary : ∀ L ∈ layers, L.Forall KrausGate.ev KrausFamily.IsUnitary

namespace UnitaryCircuit

/-- The circuit of a unitary circuit: the sequence of its layers. -/
def toCircuit (c : UnitaryCircuit Γ X) : Circuit Γ KrausGate X X :=
  Circuit.seq c.layers

omit [Fintype S] in
theorem forall_isUnitary (c : UnitaryCircuit Γ X) :
    c.toCircuit.Forall KrausGate.ev KrausFamily.IsUnitary :=
  Circuit.forall_seq _ c.layers c.isUnitary

omit [Fintype S] in
theorem forall_isTP (c : UnitaryCircuit Γ X) :
    c.toCircuit.Forall KrausGate.ev KrausFamily.IsTP :=
  c.forall_isUnitary.mono fun _ h ↦ h.isTP

omit [Fintype S] in
theorem isUnbranched (c : UnitaryCircuit Γ X) : c.toCircuit.IsUnbranched :=
  Circuit.isUnbranched_seq c.layers

/-- A unitary circuit has one branch. -/
noncomputable instance instUniqueIndex (c : UnitaryCircuit Γ X) : Unique c.toCircuit.Index :=
  (Circuit.nonempty_unique_index KrausGate.ev (c.forall_isUnitary.mono fun _ h ↦ h.1)).some

/-- The operator of a unitary circuit: the Kraus operator of its one branch. -/
noncomputable def op (c : UnitaryCircuit Γ X) : Matrix (Config X) (Config X) ℂ :=
  c.toCircuit.kraus KrausGate.ev default

/-- Every Kraus operator of a unitary circuit is its operator. -/
theorem kraus_eq_op (c : UnitaryCircuit Γ X) (p : c.toCircuit.Index) :
    c.toCircuit.kraus KrausGate.ev p = c.op :=
  congrArg _ (Subsingleton.elim p default)

/-- Two equal circuits, the second with a single branch, have the same Kraus operators. -/
private theorem kraus_eq_of_eq {C C' : Circuit Γ KrausGate X X} (h : C = C') (p : C.Index)
    (p' : C'.Index) [Subsingleton C'.Index] :
    C.kraus KrausGate.ev p = C'.kraus KrausGate.ev p' := by
  subst h
  exact congrArg _ (Subsingleton.elim p p')

/-- The depth of a unitary circuit. -/
def depth (c : UnitaryCircuit Γ X) : ℕ :=
  c.toCircuit.depth

/-- The gate count of a unitary circuit. -/
def gateCount (c : UnitaryCircuit Γ X) : ℕ :=
  c.toCircuit.gateCount

omit [Fintype S] in
/-- Every layer of a unitary circuit has a Kraus index. -/
theorem nonempty_index (c : UnitaryCircuit Γ X) : ∀ L ∈ c.layers, Nonempty L.Index :=
  fun L hL ↦ (Layer.nonempty_unique_index_of_forall_isUnitary (c.isUnitary L hL)).map
    fun u ↦ u.default

/-- The depth of a unitary circuit is the sum of the depths of its layers. -/
theorem depth_eq_sum (c : UnitaryCircuit Γ X) : c.depth = (c.layers.map Layer.depth).sum :=
  Circuit.total_seq _ c.layers c.nonempty_index

/-- The gate count of a unitary circuit is the sum of the gate counts of its layers. -/
theorem gateCount_eq_sum (c : UnitaryCircuit Γ X) :
    c.gateCount = (c.layers.map Layer.gateCount).sum :=
  Circuit.total_seq _ c.layers c.nonempty_index

/-- The depth of a unitary circuit is at most its gate count. -/
theorem depth_le_gateCount (c : UnitaryCircuit Γ X) : c.depth ≤ c.gateCount :=
  Circuit.depth_le_gateCount _

/-- The Heisenberg picture of a unitary circuit is conjugation by its operator. -/
theorem dual_eq (c : UnitaryCircuit Γ X) (A : Matrix (Config X) (Config X) ℂ) :
    c.toCircuit.dual KrausGate.ev A = c.opᴴ * A * c.op :=
  Circuit.dual_eq_of_subsingleton _ _ default A

/-- The operator of a unitary circuit is unitary. -/
theorem op_mem_unitaryGroup (c : UnitaryCircuit Γ X) : c.op ∈ unitaryGroup (Config X) ℂ := by
  refine mem_unitaryGroup_iff'.mpr ?_
  have h := c.toCircuit.dual_one_of_forall KrausGate.ev c.forall_isTP
  rwa [c.dual_eq, Matrix.mul_one] at h

theorem conjTranspose_op_mul_op (c : UnitaryCircuit Γ X) : c.opᴴ * c.op = 1 :=
  mem_unitaryGroup_iff'.mp c.op_mem_unitaryGroup

theorem op_mul_conjTranspose_op (c : UnitaryCircuit Γ X) : c.op * c.opᴴ = 1 :=
  mem_unitaryGroup_iff.mp c.op_mem_unitaryGroup

/-! ### The identity and composition -/

variable (Γ X) in
/-- The empty unitary circuit. -/
def id : UnitaryCircuit Γ X :=
  ⟨[], by simp⟩

@[simp] theorem op_id : (id Γ X).op = 1 :=
  rfl

@[simp] theorem depth_id : (id Γ X).depth = 0 :=
  rfl

@[simp] theorem gateCount_id : (id Γ X).gateCount = 0 :=
  rfl

/-- The unitary circuit `c` followed by `c'`. -/
def comp (c c' : UnitaryCircuit Γ X) : UnitaryCircuit Γ X :=
  ⟨c.layers ++ c'.layers, fun L hL ↦ (List.mem_append.mp hL).elim (c.isUnitary L)
    (c'.isUnitary L)⟩

omit [Fintype S] in
theorem toCircuit_comp (c c' : UnitaryCircuit Γ X) :
    (c.comp c').toCircuit = c.toCircuit.comp c'.toCircuit :=
  Circuit.seq_append c.layers c'.layers

/-- The operator of a composition is the product of the operators, the first circuit on the
right. -/
theorem op_comp (c c' : UnitaryCircuit Γ X) : (c.comp c').op = c'.op * c.op := by
  set q : (c.toCircuit.comp c'.toCircuit).Index :=
    (c.toCircuit.compIndexEquiv c'.toCircuit).symm (default, default)
  have : Subsingleton (c.toCircuit.comp c'.toCircuit).Index :=
    (c.toCircuit.compIndexEquiv c'.toCircuit).subsingleton
  rw [op, kraus_eq_of_eq (c.toCircuit_comp c') default q, Circuit.kraus_comp, c.kraus_eq_op,
    c'.kraus_eq_op]

theorem depth_comp (c c' : UnitaryCircuit Γ X) : (c.comp c').depth = c.depth + c'.depth := by
  simp only [depth_eq_sum, comp, List.map_append, List.sum_append]

theorem gateCount_comp (c c' : UnitaryCircuit Γ X) :
    (c.comp c').gateCount = c.gateCount + c'.gateCount := by
  simp only [gateCount_eq_sum, comp, List.map_append, List.sum_append]

/-! ### The adjoint -/

/-- The adjoint of a unitary circuit: the adjoint layers in reverse order. -/
def adjoint (c : UnitaryCircuit Γ X) : UnitaryCircuit Γ X :=
  ⟨c.layers.reverse.map Layer.adjoint, fun L hL ↦ by
    obtain ⟨L', hL', rfl⟩ := List.mem_map.mp hL
    exact Layer.forall_isUnitary_adjoint (c.isUnitary L' (List.mem_reverse.mp hL'))⟩

/-- The Kraus operators of the layers of a unitary circuit, each the operator of its layer. -/
private theorem exists_forall₂_kraus (c : UnitaryCircuit Γ X) :
    ∃ Us : List (Matrix (Config X) (Config X) ℂ),
      List.Forall₂ (fun L U ↦ ∀ i, L.kraus KrausGate.ev i = U) c.layers Us := by
  obtain ⟨Ls, hLs⟩ := c
  induction Ls with
  | nil => exact ⟨[], .nil⟩
  | cons L Ls ih =>
    obtain ⟨Us, hUs⟩ := ih fun L' hL' ↦ hLs L' (List.mem_cons_of_mem L hL')
    obtain ⟨u⟩ := Layer.nonempty_unique_index_of_forall_isUnitary (hLs L List.mem_cons_self)
    exact ⟨L.kraus KrausGate.ev default :: Us,
      .cons (fun i ↦ congrArg _ (u.uniq i)) hUs⟩

/-- The operator of the adjoint circuit is the adjoint of the operator. -/
theorem op_adjoint (c : UnitaryCircuit Γ X) : c.adjoint.op = c.opᴴ := by
  obtain ⟨Us, hUs⟩ := c.exists_forall₂_kraus
  refine (Circuit.kraus_seqAdjoint hUs (default : c.adjoint.toCircuit.Index)).trans ?_
  rw [← c.kraus_eq_op default]
  exact congrArg _ (Circuit.kraus_seq KrausGate.ev hUs _).symm

theorem depth_adjoint (c : UnitaryCircuit Γ X) : c.adjoint.depth = c.depth := by
  simp only [depth_eq_sum, adjoint, List.map_map, List.map_reverse, List.sum_reverse]
  rfl

theorem gateCount_adjoint (c : UnitaryCircuit Γ X) : c.adjoint.gateCount = c.gateCount := by
  simp only [gateCount_eq_sum, adjoint, List.map_map, List.map_reverse, List.sum_reverse]
  rfl

/-! ### One layer, one gate, and one-site unitaries -/

/-- The unitary circuit of one layer. -/
def ofLayer (L : Layer Γ KrausGate X X) (hL : L.Forall KrausGate.ev KrausFamily.IsUnitary) :
    UnitaryCircuit Γ X :=
  ⟨[L], by simpa using hL⟩

theorem op_ofLayer (L : Layer Γ KrausGate X X) (hL : L.Forall KrausGate.ev KrausFamily.IsUnitary)
    (i : L.Index) : (ofLayer L hL).op = L.kraus KrausGate.ev i := by
  rw [← (ofLayer L hL).kraus_eq_op ⟨i, ()⟩]
  exact Matrix.one_mul _

theorem depth_ofLayer (L : Layer Γ KrausGate X X)
    (hL : L.Forall KrausGate.ev KrausFamily.IsUnitary) : (ofLayer L hL).depth = L.depth := by
  simp [depth_eq_sum, ofLayer]

theorem gateCount_ofLayer (L : Layer Γ KrausGate X X)
    (hL : L.Forall KrausGate.ev KrausFamily.IsUnitary) :
    (ofLayer L hL).gateCount = L.gateCount := by
  simp [gateCount_eq_sum, ofLayer]

/-- The unitary circuit of the unitary `V` on the cell `b`: one layer with this gate and the
identity elsewhere. -/
def gate (b : Γ.Cell)
    (V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) : UnitaryCircuit Γ X :=
  ofLayer (Layer.single b (KrausFamily.single V)) (Layer.forall_isUnitary_single b hV)

/-- The operator of a gate is its unitary placed on its cell. -/
theorem op_gate (b : Γ.Cell)
    (V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) : (gate b V hV).op = place (Γ.cell b) V := by
  obtain ⟨i⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary
    (Layer.forall_isUnitary_single (Γ := Γ) b hV)).map fun u ↦ u.default
  exact (op_ofLayer _ _ i).trans (Layer.kraus_single _ b _ i)

theorem gateCount_gate (b : Γ.Cell)
    (V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) : (gate b V hV).gateCount = Γ.cost b :=
  (gateCount_ofLayer _ _).trans (Layer.gateCount_single _ _)

theorem depth_gate_le (b : Γ.Cell)
    (V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ)
    (hV : V ∈ unitaryGroup _ ℂ) : (gate b V hV).depth ≤ 1 :=
  (depth_ofLayer _ _).trans_le (Layer.depth_le_one _)

/-- The unitary circuit of one-site unitaries `u s` at every site: one layer with no cells. -/
def onsite (u : (s : S) → Matrix (X s) (X s) ℂ) (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ) :
    UnitaryCircuit Γ X :=
  ofLayer (Layer.ofOnsite fun s ↦ KrausFamily.single (u s)) (Layer.forall_isUnitary_ofOnsite hu)

/-- The operator of one-site unitaries is their tensor product. -/
theorem op_onsite (u : (s : S) → Matrix (X s) (X s) ℂ) (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ) :
    (onsite (Γ := Γ) u hu).op = prodOp u :=
  (op_ofLayer _ _ (fun b ↦ absurd b.2 (Finset.notMem_empty _), fun _ ↦ ())).trans
    (Layer.kraus_ofOnsite _ _ _)

theorem depth_onsite (u : (s : S) → Matrix (X s) (X s) ℂ)
    (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ) : (onsite (Γ := Γ) u hu).depth = 0 :=
  (depth_ofLayer _ _).trans (Layer.depth_ofOnsite _)

theorem gateCount_onsite (u : (s : S) → Matrix (X s) (X s) ℂ)
    (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ) : (onsite (Γ := Γ) u hu).gateCount = 0 :=
  (gateCount_ofLayer _ _).trans ((Layer.gateCount_eq_sum _).trans rfl)

/-! ### The light cone -/

/-- **The backward light cone.** For a unitary circuit `U` and an operator `A` supported on `R`,
the operator `Uᴴ A U` is supported on the backward light cone of `R`. -/
theorem conjTranspose_mul_mul_mem_supportedOperators_lightCone (c : UnitaryCircuit Γ X)
    {R : Finset S} {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R) :
    c.opᴴ * A * c.op ∈ supportedOperators X (c.toCircuit.lightCone R) := by
  rw [← c.dual_eq]
  exact c.toCircuit.dual_mem_supportedOperators_lightCone _ c.isUnbranched c.forall_isTP hA

/-- **The light cone in terms of depth.** On a geometry whose cells have positive cost, for a
unitary circuit `U` of depth at most `T` and an operator `A` supported on `R`, the operator
`Uᴴ A U` is supported on the `T`-fold neighbourhood of `R`.

Source: arXiv:2307.01696, main text after Theorem 1 ("strictly finite light cone") and
Supplemental Material, proof of Theorem 1. -/
theorem conjTranspose_mul_mul_mem_supportedOperators [Fintype Γ.Cell]
    (hpos : ∀ b, 0 < Γ.cost b) (c : UnitaryCircuit Γ X) {T : ℕ} (hT : c.depth ≤ T)
    {R : Finset S} {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R) :
    c.opᴴ * A * c.op ∈ supportedOperators X (Γ.neighbourhood^[T] R) :=
  supportedOperators_mono ((c.toCircuit.lightCone_subset_neighbourhood hpos R).trans
    (Γ.iterate_neighbourhood_mono hT le_rfl))
    (c.conjTranspose_mul_mul_mem_supportedOperators_lightCone hA)

end UnitaryCircuit

/-! ### Unitary circuits of bounded depth, and products of gates -/

section Classes

variable (Γ) in
/-- `U` is a unitary circuit of depth at most `T` on the geometry `Γ`: the operator of a unitary
circuit of depth at most `T`.

Source: arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local quantum circuits");
arXiv:2103.13367, main text, Definition "Depth-`ℓ` quantum circuits", on the cells of `Γ`. -/
def IsUnitaryCircuit (T : ℕ) (U : Matrix (Config X) (Config X) ℂ) : Prop :=
  ∃ c : UnitaryCircuit Γ X, c.depth ≤ T ∧ c.op = U

variable (Γ) in
/-- `U` is a product of gates of total cost at most `K` on the geometry `Γ`: the operator of a
unitary circuit of gate count at most `K`. On the edges of a path, with every edge of cost `1`,
these are the products of at most `K` unitaries on two neighbouring sites of an open chain.

Source: arXiv:2307.01696, main text before Theorem 1 and paragraph "The sequential-RG circuit"
(gates with constant support expressed through local gates). -/
def IsGateProduct (K : ℕ) (U : Matrix (Config X) (Config X) ℂ) : Prop :=
  ∃ c : UnitaryCircuit Γ X, c.gateCount ≤ K ∧ c.op = U

namespace IsUnitaryCircuit

variable {T T' : ℕ} {U V : Matrix (Config X) (Config X) ℂ}

variable (Γ X) in
theorem one (T : ℕ) : IsUnitaryCircuit Γ T (1 : Matrix (Config X) (Config X) ℂ) :=
  ⟨UnitaryCircuit.id Γ X, Nat.zero_le T, rfl⟩

theorem mono (h : IsUnitaryCircuit Γ T U) (hT : T ≤ T') : IsUnitaryCircuit Γ T' U :=
  let ⟨c, hc, hU⟩ := h
  ⟨c, hc.trans hT, hU⟩

/-- **Circuits in series.** Applying `V` and then `U` is a circuit of depth at most the sum. -/
theorem mul (hU : IsUnitaryCircuit Γ T U) (hV : IsUnitaryCircuit Γ T' V) :
    IsUnitaryCircuit Γ (T + T') (U * V) := by
  obtain ⟨c, hc, rfl⟩ := hU
  obtain ⟨c', hc', rfl⟩ := hV
  exact ⟨c'.comp c, by rw [UnitaryCircuit.depth_comp]; omega, UnitaryCircuit.op_comp _ _⟩

/-- **The inverse of a circuit.** The adjoint of a circuit of depth at most `T` is a circuit of
depth at most `T`: its layers are the adjoint layers in reverse order. -/
theorem conjTranspose (h : IsUnitaryCircuit Γ T U) : IsUnitaryCircuit Γ T Uᴴ := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c.adjoint, c.depth_adjoint.trans_le hc, c.op_adjoint⟩

theorem mem_unitaryGroup (h : IsUnitaryCircuit Γ T U) : U ∈ unitaryGroup (Config X) ℂ := by
  obtain ⟨c, -, rfl⟩ := h
  exact c.op_mem_unitaryGroup

theorem pow (h : IsUnitaryCircuit Γ T U) (k : ℕ) : IsUnitaryCircuit Γ (k * T) (U ^ k) := by
  induction k with
  | zero => simpa using one Γ X 0
  | succ k ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul h

/-- One-site unitaries at every site form a circuit of depth `0`. -/
theorem prodOp {u : (s : S) → Matrix (X s) (X s) ℂ} (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ)
    (T : ℕ) : IsUnitaryCircuit Γ T (ManyBody.prodOp u) :=
  ⟨UnitaryCircuit.onsite u hu, (UnitaryCircuit.depth_onsite u hu).trans_le (Nat.zero_le T),
    UnitaryCircuit.op_onsite u hu⟩

/-- A unitary placed on a cell is a circuit of depth at most `1`. -/
theorem place {b : Γ.Cell}
    {V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ}
    (hV : V ∈ unitaryGroup _ ℂ) : IsUnitaryCircuit Γ 1 (ManyBody.place (Γ.cell b) V) :=
  ⟨UnitaryCircuit.gate b V hV, UnitaryCircuit.depth_gate_le b V hV,
    UnitaryCircuit.op_gate b V hV⟩

/-- **The backward light cone.** On a geometry whose cells have positive cost, if `U` is a
circuit of depth at most `T` and `A` is supported on `R`, then `Uᴴ A U` is supported on the
`T`-fold neighbourhood of `R`.

Source: arXiv:2307.01696, main text after Theorem 1 ("`|ψ_N⟩` have a strictly finite light
cone") and Supplemental Material, proof of Theorem 1. -/
theorem conjTranspose_mul_mul_mem_supportedOperators [Fintype Γ.Cell]
    (hpos : ∀ b, 0 < Γ.cost b) (h : IsUnitaryCircuit Γ T U) {R : Finset S}
    {A : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R) :
    Uᴴ * A * U ∈ supportedOperators X (Γ.neighbourhood^[T] R) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact c.conjTranspose_mul_mul_mem_supportedOperators hpos hc hA

end IsUnitaryCircuit

namespace IsGateProduct

variable {K K' : ℕ} {U V : Matrix (Config X) (Config X) ℂ}

variable (Γ X) in
theorem one (K : ℕ) : IsGateProduct Γ K (1 : Matrix (Config X) (Config X) ℂ) :=
  ⟨UnitaryCircuit.id Γ X, Nat.zero_le K, rfl⟩

theorem mono (h : IsGateProduct Γ K U) (hK : K ≤ K') : IsGateProduct Γ K' U :=
  let ⟨c, hc, hU⟩ := h
  ⟨c, hc.trans hK, hU⟩

/-- Products of gates multiply, with additive gate count. -/
theorem mul (hU : IsGateProduct Γ K U) (hV : IsGateProduct Γ K' V) :
    IsGateProduct Γ (K + K') (U * V) := by
  obtain ⟨c, hc, rfl⟩ := hU
  obtain ⟨c', hc', rfl⟩ := hV
  exact ⟨c'.comp c, by rw [UnitaryCircuit.gateCount_comp]; omega, UnitaryCircuit.op_comp _ _⟩

/-- The adjoint of a product of gates is the product of the adjoint gates in reverse order. -/
theorem conjTranspose (h : IsGateProduct Γ K U) : IsGateProduct Γ K Uᴴ := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c.adjoint, c.gateCount_adjoint.trans_le hc, c.op_adjoint⟩

theorem mem_unitaryGroup (h : IsGateProduct Γ K U) : U ∈ unitaryGroup (Config X) ℂ := by
  obtain ⟨c, -, rfl⟩ := h
  exact c.op_mem_unitaryGroup

/-- Repeating a product of gates multiplies its gate count by the number of repetitions. -/
theorem pow (h : IsGateProduct Γ K U) (k : ℕ) : IsGateProduct Γ (k * K) (U ^ k) := by
  induction k with
  | zero => simpa using one Γ X 0
  | succ k ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul h

/-- A product of a list of products of at most `K` gates has at most `length * K` gates. -/
theorem list_prod (l : List (Matrix (Config X) (Config X) ℂ))
    (hl : ∀ U ∈ l, IsGateProduct Γ K U) : IsGateProduct Γ (l.length * K) l.prod := by
  induction l with
  | nil => simpa using one Γ X 0
  | cons U l ih =>
    rw [List.prod_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact (hl U List.mem_cons_self).mul (ih fun V h ↦ hl V (List.mem_cons_of_mem U h))

/-- One-site unitaries at every site cost nothing. -/
theorem prodOp {u : (s : S) → Matrix (X s) (X s) ℂ} (hu : ∀ s, u s ∈ unitaryGroup (X s) ℂ)
    (K : ℕ) : IsGateProduct Γ K (ManyBody.prodOp u) :=
  ⟨UnitaryCircuit.onsite u hu, (UnitaryCircuit.gateCount_onsite u hu).trans_le (Nat.zero_le K),
    UnitaryCircuit.op_onsite u hu⟩

/-- A unitary placed on a cell is one gate, of the cost of the cell. -/
theorem place {b : Γ.Cell}
    {V : Matrix (RegionConfig X (Γ.cell b)) (RegionConfig X (Γ.cell b)) ℂ}
    (hV : V ∈ unitaryGroup _ ℂ) : IsGateProduct Γ (Γ.cost b) (ManyBody.place (Γ.cell b) V) :=
  ⟨UnitaryCircuit.gate b V hV, (UnitaryCircuit.gateCount_gate b V hV).le,
    UnitaryCircuit.op_gate b V hV⟩

/-- A unitary supported on a cell is one gate, of the cost of the cell. -/
theorem of_mem_supportedOperators {b : Γ.Cell} {Z : Matrix (Config X) (Config X) ℂ}
    (hZu : Z ∈ unitaryGroup (Config X) ℂ) (hZ : Z ∈ supportedOperators X (Γ.cell b)) :
    IsGateProduct Γ (Γ.cost b) Z := by
  by_cases hne : ∀ s, Nonempty (X s)
  · obtain ⟨V, rfl⟩ := exists_eq_place_of_mem_supportedOperators hZ
    exact place (place_mem_unitaryGroup_iff.mp hZu)
  · push Not at hne
    obtain ⟨s, hs⟩ := hne
    have : IsEmpty (Config X) := ⟨fun σ ↦ hs.false (σ s)⟩
    rw [Subsingleton.elim Z (ManyBody.place (Γ.cell b) 1)]
    exact place (one_mem _)

/-- A product of products of gates along a list has cost at most the sum of their costs. -/
theorem list_prod_map {ι : Type*} (l : List ι) (F : ι → Matrix (Config X) (Config X) ℂ)
    (k : ι → ℕ) (h : ∀ c ∈ l, IsGateProduct Γ (k c) (F c)) :
    IsGateProduct Γ (l.map k).sum (l.map F).prod := by
  induction l with
  | nil => exact one Γ X 0
  | cons c l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons]
    exact (h c List.mem_cons_self).mul (ih fun c' hc' ↦ h c' (List.mem_cons_of_mem c hc'))

omit [∀ s, Fintype (X s)] in
/-- The placement of a matrix on one site is the product operator with that matrix at the site
and the identity elsewhere. -/
private theorem place_singleton_eq_prodOp (a : S)
    (V : Matrix (RegionConfig X {a}) (RegionConfig X {a}) ℂ) :
    ManyBody.place {a} V = ManyBody.prodOp (Function.update (fun s ↦ (1 : Matrix (X s) (X s) ℂ)) a
      (V.submatrix (siteEquiv X a).symm (siteEquiv X a).symm)) := by
  rw [← placeAt_eq_prodOp, ← place_siteEquiv_eq_placeAt, submatrix_submatrix,
    Equiv.symm_comp_self, submatrix_id_id]

/-- A unitary on one site is an onsite family and costs nothing. -/
theorem place_singleton (a : S) {V : Matrix (RegionConfig X {a}) (RegionConfig X {a}) ℂ}
    (hV : V ∈ unitaryGroup _ ℂ) (K : ℕ) : IsGateProduct Γ K (ManyBody.place {a} V) := by
  rw [place_singleton_eq_prodOp]
  refine prodOp (fun s ↦ ?_) K
  by_cases hs : s = a
  · subst hs
    rw [Function.update_self]
    exact submatrix_equiv_mem_unitary.mpr hV
  · rw [Function.update_of_ne hs]
    exact one_mem _

omit [∀ s, Fintype (X s)] in
/-- A scalar multiple of the identity is the product operator with the scalar at one site. -/
private theorem smul_one_eq_prodOp (s₀ : S) (μ : ℂ) :
    (μ • 1 : Matrix (Config X) (Config X) ℂ) =
      ManyBody.prodOp fun s ↦ if s = s₀ then μ • (1 : Matrix (X s) (X s) ℂ) else 1 := by
  ext σ τ
  have h (s : S) : (if s = s₀ then μ • (1 : Matrix (X s) (X s) ℂ) else 1) (σ s) (τ s) =
      (if s = s₀ then μ else 1) * (1 : Matrix (X s) (X s) ℂ) (σ s) (τ s) := by
    split_ifs <;> simp
  rw [prodOp_apply, Finset.prod_congr rfl fun s _ ↦ h s, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ s₀]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← prodOp_apply, prodOp_one, Matrix.smul_apply, smul_eq_mul]

/-- **A global phase costs nothing.** On a nonempty set of sites, `μ • 1` with `|μ| = 1` is a
one-site phase, hence a product of gates of every cost. -/
theorem smul_one [Nonempty S] {μ : ℂ} (hμ : ‖μ‖ = 1) (K : ℕ) :
    IsGateProduct Γ K (μ • 1 : Matrix (Config X) (Config X) ℂ) := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  rw [smul_one_eq_prodOp s₀]
  refine prodOp (fun s ↦ ?_) K
  split_ifs
  · refine mem_unitaryGroup_iff'.mpr ?_
    rw [star_smul, star_one, smul_mul_smul_comm, Matrix.one_mul, Complex.star_def,
      Complex.conj_mul', hμ]
    simp
  · exact one_mem _

/-- **Gate count bounds depth.** A product of gates of total cost at most `K` is a circuit of
depth at most `K`. -/
theorem isUnitaryCircuit (h : IsGateProduct Γ K U) : IsUnitaryCircuit Γ K U := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, c.depth_le_gateCount.trans hc, rfl⟩

end IsGateProduct

end Classes

/-! ### Preparation in depth `T` -/

section Preparation

variable (Γ) in
/-- A vector is prepared in depth `T` on `Γ` when it is a unitary circuit of depth at most `T`
applied to a product vector `σ ↦ ∏ₛ vₛ(σₛ)`.

Source: arXiv:2307.01696, main text before Theorem 1 ("a sequence obtained from depth-`T`
local quantum circuits applied to product states"). -/
def IsPreparedInDepth (T : ℕ) (ψ : Config X → ℂ) : Prop :=
  ∃ U, IsUnitaryCircuit Γ T U ∧ ∃ v : (s : S) → X s → ℂ, ψ = U *ᵥ fun σ ↦ ∏ s, v s (σ s)

namespace IsPreparedInDepth

variable {T T' : ℕ} {ψ : Config X → ℂ}

theorem mono (h : IsPreparedInDepth Γ T ψ) (hT : T ≤ T') : IsPreparedInDepth Γ T' ψ :=
  let ⟨U, hU, v, hψ⟩ := h
  ⟨U, hU.mono hT, v, hψ⟩

/-- A circuit of depth `T'` applied to a vector prepared in depth `T` gives a vector prepared in
depth `T + T'`. -/
theorem mulVec (h : IsPreparedInDepth Γ T ψ) {V : Matrix (Config X) (Config X) ℂ}
    (hV : IsUnitaryCircuit Γ T' V) : IsPreparedInDepth Γ (T + T') (V *ᵥ ψ) := by
  obtain ⟨U, hU, v, rfl⟩ := h
  exact ⟨V * U, add_comm T' T ▸ hV.mul hU, v, Matrix.mulVec_mulVec _ _ _⟩

/-- A product vector is prepared in depth `0`. -/
theorem prod (v : (s : S) → X s → ℂ) : IsPreparedInDepth Γ 0 fun σ ↦ ∏ s, v s (σ s) :=
  ⟨1, IsUnitaryCircuit.one Γ X 0, v, (Matrix.one_mulVec _).symm⟩

end IsPreparedInDepth

omit [∀ s, DecidableEq (X s)] in
/-- The expectation of a product operator in a product vector is the product of the expectations
at the sites. -/
private theorem dotProduct_prodOp_mulVec (v : (s : S) → X s → ℂ)
    (m : (s : S) → Matrix (X s) (X s) ℂ) :
    star (fun σ : Config X ↦ ∏ s, v s (σ s)) ⬝ᵥ
        (ManyBody.prodOp m *ᵥ fun σ : Config X ↦ ∏ s, v s (σ s)) =
      ∏ s, star (v s) ⬝ᵥ (m s *ᵥ v s) := by
  simp only [dotProduct, mulVec, prodOp_apply, Pi.star_apply, star_prod, Finset.mul_sum,
    ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum]
  refine Fintype.sum_congr _ _ fun σ ↦ ?_
  rw [Finset.prod_univ_sum]
  refine Fintype.sum_congr _ _ fun τ ↦ ?_
  simp only [Finset.prod_mul_distrib]

/-- **Product vectors over disjoint regions.** For a product vector `φ` and operators `A`, `B`
supported on disjoint regions, `⟨φ|AB|φ⟩⟨φ|φ⟩ = ⟨φ|A|φ⟩⟨φ|B|φ⟩`. -/
theorem dotProduct_prod_mul_mul (v : (s : S) → X s → ℂ) {D D' : Finset S}
    (hDD' : Disjoint D D') {A B : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X D) (hB : B ∈ supportedOperators X D') :
    star (fun σ : Config X ↦ ∏ s, v s (σ s)) ⬝ᵥ
        ((A * B) *ᵥ fun σ : Config X ↦ ∏ s, v s (σ s)) *
      (star (fun σ : Config X ↦ ∏ s, v s (σ s)) ⬝ᵥ fun σ : Config X ↦ ∏ s, v s (σ s)) =
    (star (fun σ : Config X ↦ ∏ s, v s (σ s)) ⬝ᵥ (A *ᵥ fun σ : Config X ↦ ∏ s, v s (σ s))) *
      (star (fun σ : Config X ↦ ∏ s, v s (σ s)) ⬝ᵥ
        (B *ᵥ fun σ : Config X ↦ ∏ s, v s (σ s))) := by
  set φ : Config X → ℂ := fun σ ↦ ∏ s, v s (σ s)
  have hφ : star φ ⬝ᵥ φ =
      star φ ⬝ᵥ (ManyBody.prodOp (fun s ↦ (1 : Matrix (X s) (X s) ℂ)) *ᵥ φ) := by
    rw [prodOp_one, Matrix.one_mulVec]
  let f : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config X) (Config X) ℂ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun A B ↦ star φ ⬝ᵥ ((A * B) *ᵥ φ) * (star φ ⬝ᵥ φ))
      (by simp [Matrix.add_mulVec, add_mul])
      (by simp [Matrix.smul_mulVec, dotProduct_smul, mul_assoc])
      (by simp [Matrix.mul_add, Matrix.add_mulVec, add_mul])
      (by simp [Matrix.smul_mulVec, dotProduct_smul, mul_assoc])
  let g : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config X) (Config X) ℂ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun A B ↦ star φ ⬝ᵥ (A *ᵥ φ) * (star φ ⬝ᵥ (B *ᵥ φ)))
      (by simp [Matrix.add_mulVec, add_mul])
      (by simp [Matrix.smul_mulVec, dotProduct_smul, mul_assoc])
      (by simp [Matrix.add_mulVec, mul_add])
      (by simp [Matrix.smul_mulVec, dotProduct_smul, mul_left_comm])
  refine eq_of_mem_supportedOperators₂ f g (fun m m' hm hm' ↦ ?_) hA hB
  simp only [f, g, LinearMap.mk₂_apply]
  rw [hφ, prodOp_mul, dotProduct_prodOp_mulVec, dotProduct_prodOp_mulVec,
    dotProduct_prodOp_mulVec, dotProduct_prodOp_mulVec, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ ↦ ?_
  by_cases hs : s ∈ D
  · rw [hm' s (Finset.disjoint_left.mp hDD' hs), Matrix.mul_one, Matrix.one_mulVec]
  · rw [hm s hs, Matrix.one_mul, Matrix.one_mulVec, mul_comm]

/-- **Vanishing connected correlations beyond the light cone.** On a geometry whose cells have
positive cost, for a vector `ψ` prepared in depth `T` and operators `A`, `B` supported on regions
whose `T`-fold neighbourhoods are disjoint, `⟨ψ|AB|ψ⟩⟨ψ|ψ⟩ = ⟨ψ|A|ψ⟩⟨ψ|B|ψ⟩`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1: "since `ψ` is created
from a product state by a depth-`T` circuit, every connected correlation for operators at a
distance larger than `2T` vanishes". -/
theorem IsPreparedInDepth.dotProduct_mul_mul [Fintype Γ.Cell] (hpos : ∀ b, 0 < Γ.cost b)
    {T : ℕ} {ψ : Config X → ℂ} (hψ : IsPreparedInDepth Γ T ψ) {R R' : Finset S}
    (hRR' : Disjoint (Γ.neighbourhood^[T] R) (Γ.neighbourhood^[T] R'))
    {A B : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R)
    (hB : B ∈ supportedOperators X R') :
    star ψ ⬝ᵥ ((A * B) *ᵥ ψ) * (star ψ ⬝ᵥ ψ) =
      (star ψ ⬝ᵥ (A *ᵥ ψ)) * (star ψ ⬝ᵥ (B *ᵥ ψ)) := by
  obtain ⟨U, hU, v, rfl⟩ := hψ
  set φ : Config X → ℂ := fun σ ↦ ∏ s, v s (σ s)
  have hconj (M : Matrix (Config X) (Config X) ℂ) :
      star (U *ᵥ φ) ⬝ᵥ (M *ᵥ (U *ᵥ φ)) = star φ ⬝ᵥ ((Uᴴ * M * U) *ᵥ φ) := by
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hunit : Uᴴ * U = 1 := mem_unitaryGroup_iff'.mp hU.mem_unitaryGroup
  have hAB : Uᴴ * (A * B) * U = (Uᴴ * A * U) * (Uᴴ * B * U) := by
    have h1 : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU.mem_unitaryGroup
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, h1, Matrix.one_mul]
  have hone := hconj 1
  rw [Matrix.mul_one, hunit, Matrix.one_mulVec, Matrix.one_mulVec] at hone
  rw [hconj, hconj, hconj, hone, hAB]
  exact dotProduct_prod_mul_mul v hRR' (hU.conjTranspose_mul_mul_mem_supportedOperators hpos hA)
    (hU.conjTranspose_mul_mul_mem_supportedOperators hpos hB)

/-- For a unit vector `ψ` prepared in depth `T`, on a geometry whose cells have positive cost,
the connected correlation of operators on regions with disjoint `T`-fold neighbourhoods
vanishes: `⟨AB⟩ = ⟨A⟩⟨B⟩`.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1. -/
theorem IsPreparedInDepth.dotProduct_mul_eq [Fintype Γ.Cell] (hpos : ∀ b, 0 < Γ.cost b)
    {T : ℕ} {ψ : Config X → ℂ} (hψ : IsPreparedInDepth Γ T ψ) (hnorm : star ψ ⬝ᵥ ψ = 1)
    {R R' : Finset S} (hRR' : Disjoint (Γ.neighbourhood^[T] R) (Γ.neighbourhood^[T] R'))
    {A B : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X R)
    (hB : B ∈ supportedOperators X R') :
    star ψ ⬝ᵥ ((A * B) *ᵥ ψ) = (star ψ ⬝ᵥ (A *ᵥ ψ)) * (star ψ ⬝ᵥ (B *ᵥ ψ)) := by
  have h := hψ.dotProduct_mul_mul hpos hRR' hA hB
  rwa [hnorm, mul_one] at h

end Preparation

end QuantumCircuit
