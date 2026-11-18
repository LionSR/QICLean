/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.LayerDual

/-!
# Circuits

A circuit from the system `X` to the system `Z` on a geometry `Γ` is either finished, or a layer
from `X` to some system `Y` followed by a circuit from `Y` to `Z` that may depend on the Kraus
index (the outcome) of the layer. The dependence is measurement with classical feedback; a
circuit that ignores it is unbranched. The intermediate systems are part of the circuit, so a
circuit may add and remove ancillas and change local dimensions.

The semantics is a Kraus family indexed by the branches, the paths through the circuit: the
Kraus operator of a branch is the product of the Kraus operators of its layers, in the order
applied. The map of the circuit is `ρ ↦ ∑ₚ Kₚ ρ Kₚᴴ`, the sum over all outcomes, and its
Heisenberg picture is `A ↦ ∑ₚ Kₚᴴ A Kₚ`.

Composition attaches a continuation to every branch (`append`); attaching the same circuit to
every branch is `comp`, and `done` is its identity.

## Main definitions

* `QuantumCircuit.Circuit` — the circuits.
* `QuantumCircuit.Circuit.Index`, `QuantumCircuit.Circuit.kraus`,
  `QuantumCircuit.Circuit.krausFamily`, `QuantumCircuit.Circuit.map`,
  `QuantumCircuit.Circuit.dual` — the semantics.
* `QuantumCircuit.Circuit.append`, `QuantumCircuit.Circuit.comp` — composition.
* `QuantumCircuit.Circuit.ofLayer` — the circuit of one layer.
* `QuantumCircuit.Circuit.seq` — an unbranched sequence of layers on one system.

## Main results

* `QuantumCircuit.Circuit.done_comp`, `QuantumCircuit.Circuit.comp_done` — `done` is the
  identity of composition.
* `QuantumCircuit.Circuit.kraus_append`, `QuantumCircuit.Circuit.kraus_comp` — the Kraus
  operators of a composition are the products of those of its parts.
* `QuantumCircuit.Circuit.map_comp`, `QuantumCircuit.Circuit.map_done` — composition of maps.
* `QuantumCircuit.Circuit.map_append`, `QuantumCircuit.Circuit.map_step` — the map along the
  branches, and layer by layer.
* `QuantumCircuit.Circuit.trace_map_mul` — the map and the Heisenberg picture are dual.
* `QuantumCircuit.Circuit.dual_step`, `QuantumCircuit.Circuit.dual_done` — the Heisenberg
  picture layer by layer.
* `QuantumCircuit.Circuit.step_eq_ofLayer_comp`, `QuantumCircuit.Circuit.dual_step_of_forall_eq`
  — a step whose continuations agree.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A circuit from the system `X` to the system `Z` on the geometry `Γ` with gates of the family
`G`: either `done`, or a layer `L` from `X` to a system `Y` followed by a circuit from `Y`
that depends on the Kraus index of `L`. -/
inductive Circuit (Γ : Geometry S) (G : Finset S → (S → Type) → (S → Type) → Type 1)
    [GateFamily G] : (S → Type) → (S → Type) → Type 1
  /-- The empty circuit. -/
  | done (X : S → Type) : Circuit Γ G X X
  /-- A layer followed by a circuit chosen by the outcome of the layer. -/
  | step {X Y Z : S → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
      (L : Layer Γ G X Y) (next : L.Index → Circuit Γ G Y Z) : Circuit Γ G X Z

namespace Circuit

variable {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-- The branches of a circuit: an outcome of every layer along a path. -/
def Index : {X Z : S → Type} → Circuit Γ G X Z → Type
  | _, _, done _ => Unit
  | _, _, step L next => Σ i : L.Index, (next i).Index

instance instFintypeIndex : {X Z : S → Type} → (c : Circuit Γ G X Z) → Fintype c.Index
  | _, _, done _ => inferInstanceAs (Fintype Unit)
  | _, _, step L next =>
      letI := fun i ↦ instFintypeIndex (next i)
      inferInstanceAs (Fintype (Σ i : L.Index, (next i).Index))

/-- The Kraus operator of a branch: the product of the Kraus operators of its layers, the first
layer on the right. -/
def kraus (ev : Interpretation G) : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (c : Circuit Γ G X Z) → c.Index →
      Matrix (Config Z) (Config X) ℂ
  | _, _, _, _, done _, _ => 1
  | _, _, _, _, step L next, p => (next p.1).kraus ev p.2 * L.kraus ev p.1

variable {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

@[simp] theorem kraus_done (ev : Interpretation G) (p : (done X : Circuit Γ G X X).Index) :
    (done X : Circuit Γ G X X).kraus ev p = 1 :=
  rfl

theorem kraus_step (ev : Interpretation G) [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (L : Layer Γ G X Y) (next : L.Index → Circuit Γ G Y Z) (i : L.Index) (j : (next i).Index) :
    (step L next).kraus ev ⟨i, j⟩ = (next i).kraus ev j * L.kraus ev i :=
  rfl

/-- The Kraus family of a circuit, indexed by its branches. -/
def krausFamily (ev : Interpretation G) (c : Circuit Γ G X Z) :
    KrausFamily (Config X) (Config Z) :=
  ⟨c.Index, c.kraus ev⟩

/-- The map `ρ ↦ ∑ₚ Kₚ ρ Kₚᴴ` of a circuit, the sum over all its branches. -/
noncomputable def map [∀ s, Fintype (Z s)] (ev : Interpretation G) (c : Circuit Γ G X Z) :
    Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ :=
  (c.krausFamily ev).map

/-- The Heisenberg picture `A ↦ ∑ₚ Kₚᴴ A Kₚ` of a circuit. -/
noncomputable def dual [∀ s, Fintype (Z s)] (ev : Interpretation G) (c : Circuit Γ G X Z)
    (A : Matrix (Config Z) (Config Z) ℂ) : Matrix (Config X) (Config X) ℂ :=
  ∑ p, (c.kraus ev p)ᴴ * A * c.kraus ev p

/-- The Heisenberg picture of a circuit, layer by layer: the first layer applied to the
Heisenberg pictures of the continuations. -/
theorem dual_step [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)]
    (ev : Interpretation G) (L : Layer Γ G X Y) (next : L.Index → Circuit Γ G Y Z)
    (A : Matrix (Config Z) (Config Z) ℂ) :
    (step L next).dual ev A = ∑ i, (L.kraus ev i)ᴴ * (next i).dual ev A * L.kraus ev i := by
  change ∑ p : Σ i : L.Index, (next i).Index, ((step L next).kraus ev p)ᴴ * A *
    (step L next).kraus ev p = _
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dual, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [kraus_step, conjTranspose_mul, Matrix.mul_assoc]

/-- The map and the Heisenberg picture of a circuit are dual for the trace pairing. -/
theorem trace_map_mul [∀ s, Fintype (Z s)] (ev : Interpretation G) (c : Circuit Γ G X Z)
    (ρ : Matrix (Config X) (Config X) ℂ) (A : Matrix (Config Z) (Config Z) ℂ) :
    (c.map ev ρ * A).trace = (ρ * c.dual ev A).trace := by
  rw [map, KrausFamily.trace_map_mul]
  simp only [KrausFamily.map_apply, KrausFamily.adjoint, conjTranspose_conjTranspose]
  rfl

/-- The empty circuit has the identity as Heisenberg picture. -/
@[simp] theorem dual_done (ev : Interpretation G) (A : Matrix (Config X) (Config X) ℂ) :
    (done X : Circuit Γ G X X).dual ev A = A := by
  change ∑ _ : Unit, (1 : Matrix (Config X) (Config X) ℂ)ᴴ * A * 1 = A
  simp

/-! ### Composition -/

/-- Attach the continuation `k p` to every branch `p` of a circuit. -/
def append : {X₁ X₂ X₃ : S → Type} → (c : Circuit Γ G X₁ X₂) → (c.Index → Circuit Γ G X₂ X₃) →
    Circuit Γ G X₁ X₃
  | _, _, _, done _, k => k ()
  | _, _, _, step L next, k => step L fun i ↦ (next i).append fun j ↦ k ⟨i, j⟩

/-- Attach the same circuit to every branch. -/
def comp (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) : Circuit Γ G X Z :=
  c.append fun _ ↦ c'

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
@[simp] theorem done_comp (c : Circuit Γ G X Z) : (done X).comp c = c :=
  rfl

omit [Fintype S] in
/-- `done` is a right identity of composition. -/
@[simp] theorem comp_done : {X Z : S → Type} → (c : Circuit Γ G X Z) → c.comp (done Z) = c
  | _, _, done _ => rfl
  | _, _, step L next => congrArg (step L) (funext fun i ↦ comp_done (next i))

/-- The branches of `c.append k` are a branch `p` of `c` followed by a branch of `k p`. -/
def appendIndexEquiv : {X₁ X₂ X₃ : S → Type} → (c : Circuit Γ G X₁ X₂) →
    (k : c.Index → Circuit Γ G X₂ X₃) → (c.append k).Index ≃ Σ p : c.Index, (k p).Index
  | _, _, _, done _, k => (Equiv.uniqueSigma fun p : Unit ↦ (k p).Index).symm
  | _, _, _, step _ next, k =>
      (Equiv.sigmaCongrRight fun i ↦ appendIndexEquiv (next i) fun j ↦ k ⟨i, j⟩).trans
        (Equiv.sigmaAssoc fun i j ↦ (k ⟨i, j⟩).Index).symm

/-- The Kraus operator of a branch of `c.append k` is the product of those of its parts. -/
theorem kraus_append (ev : Interpretation G) : {X₁ X₂ : S → Type} → [∀ s, Fintype (X₁ s)] →
    [∀ s, DecidableEq (X₁ s)] → [∀ s, Fintype (X₂ s)] → [∀ s, DecidableEq (X₂ s)] →
    (c : Circuit Γ G X₁ X₂) → (k : c.Index → Circuit Γ G X₂ Z) → (q : (c.append k).Index) →
      (c.append k).kraus ev q =
        (k (c.appendIndexEquiv k q).1).kraus ev (c.appendIndexEquiv k q).2 *
          c.kraus ev (c.appendIndexEquiv k q).1
  | _, _, i₁, i₂, i₃, i₄, done _, k, q => by
      obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
      obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
      rw [kraus_done, Matrix.mul_one]
      rfl
  | _, _, _, _, _, _, step L next, k, q => by
      obtain ⟨i, q⟩ := q
      change ((next i).append fun j ↦ k ⟨i, j⟩).kraus ev q * L.kraus ev i = _
      rw [kraus_append ev (next i) (fun j ↦ k ⟨i, j⟩) q, Matrix.mul_assoc]
      rfl

/-- The branches of `c.comp c'` are pairs of branches. -/
def compIndexEquiv (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) :
    (c.comp c').Index ≃ c.Index × c'.Index :=
  (c.appendIndexEquiv fun _ ↦ c').trans (Equiv.sigmaEquivProd _ _)

theorem kraus_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (ev : Interpretation G)
    (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) (q : (c.comp c').Index) :
    (c.comp c').kraus ev q =
      c'.kraus ev (c.compIndexEquiv c' q).2 * c.kraus ev (c.compIndexEquiv c' q).1 :=
  c.kraus_append ev (fun _ ↦ c') q

/-- The map of a composition is the composition of the maps. -/
theorem map_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)]
    (ev : Interpretation G) (c : Circuit Γ G X Y) (c' : Circuit Γ G Y Z) :
    (c.comp c').map ev = c'.map ev ∘ₗ c.map ev := by
  ext1 ρ
  simp only [map, krausFamily, KrausFamily.map_apply, LinearMap.comp_apply]
  rw [← (c.compIndexEquiv c').symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [kraus_comp, Equiv.apply_symm_apply, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The empty circuit is the identity map. -/
theorem map_done (ev : Interpretation G) :
    (done X : Circuit Γ G X X).map ev = LinearMap.id := by
  ext1 ρ
  simp only [map, krausFamily, KrausFamily.map_apply, LinearMap.id_apply]
  change ∑ _ : Unit, (1 : Matrix (Config X) (Config X) ℂ) * ρ * (1 : Matrix _ _ ℂ)ᴴ = ρ
  simp

/-- The map of `c.append k`: along each branch `p` of `c`, the map of the continuation `k p`
applied to `Kₚ ρ Kₚᴴ`. -/
theorem map_append [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)]
    (ev : Interpretation G) (c : Circuit Γ G X Y) (k : c.Index → Circuit Γ G Y Z)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    (c.append k).map ev ρ = ∑ p, (k p).map ev (c.kraus ev p * ρ * (c.kraus ev p)ᴴ) := by
  simp only [map, krausFamily, KrausFamily.map_apply]
  rw [← (c.appendIndexEquiv k).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ ?_
  rw [kraus_append, Equiv.apply_symm_apply, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The circuit of one layer. -/
def ofLayer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y) :
    Circuit Γ G X Y :=
  step L fun _ ↦ done Y

/-- The map of a circuit layer by layer: along each Kraus index `i` of the first layer, the map
of the continuation applied to `Kᵢ ρ Kᵢᴴ`. -/
theorem map_step [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)]
    (ev : Interpretation G) (L : Layer Γ G X Y) (next : L.Index → Circuit Γ G Y Z)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    (step L next).map ev ρ = ∑ i, (next i).map ev (L.kraus ev i * ρ * (L.kraus ev i)ᴴ) := by
  simp only [map, krausFamily, KrausFamily.map_apply]
  change ∑ p : Σ i : L.Index, (next i).Index, (step L next).kraus ev p * ρ *
    ((step L next).kraus ev p)ᴴ = _
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [kraus_step, conjTranspose_mul, Matrix.mul_assoc]

/-- The Kraus operators of the circuit of one layer are those of the layer. -/
@[simp] theorem kraus_ofLayer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (ev : Interpretation G) (L : Layer Γ G X Y) (p : (ofLayer L).Index) :
    (ofLayer L).kraus ev p = L.kraus ev p.1 :=
  Matrix.one_mul _

/-- The map of the circuit of one layer is the map of the layer's Kraus family. -/
theorem map_ofLayer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (ev : Interpretation G)
    (L : Layer Γ G X Y) : (ofLayer L).map ev = (L.krausFamily ev).map := by
  ext1 ρ
  rw [ofLayer, map_step, KrausFamily.map_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_done]; rfl

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
/-- A step whose continuations all agree is the circuit of its layer followed by any one of
them. -/
theorem step_eq_ofLayer_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (L : Layer Γ G X Y)
    {next : L.Index → Circuit Γ G Y Z} (h : ∀ i j, next i = next j) (i₀ : L.Index) :
    step L next = (ofLayer L).comp (next i₀) := by
  have hnext : next = fun _ ↦ next i₀ := funext fun i ↦ h i i₀
  conv_lhs => rw [hnext]
  rfl

/-- The Heisenberg picture of a step whose continuations all agree: the layer applied to the
Heisenberg picture of any one of them. -/
theorem dual_step_of_forall_eq [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    [∀ s, Fintype (Z s)] (ev : Interpretation G) (L : Layer Γ G X Y)
    {next : L.Index → Circuit Γ G Y Z} (h : ∀ i j, next i = next j) (i₀ : L.Index)
    (A : Matrix (Config Z) (Config Z) ℂ) :
    (step L next).dual ev A = L.dual ev ((next i₀).dual ev A) := by
  rw [dual_step]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [h i i₀]

/-- An unbranched sequence of layers on one system, applied from the head of the list. -/
def seq : List (Layer Γ G X X) → Circuit Γ G X X
  | [] => done X
  | L :: Ls => step L fun _ ↦ seq Ls

end Circuit

end QuantumCircuit
