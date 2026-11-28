/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.SeparableOperation
import QICLean.Circuit.Model.Protocol
import QICLean.Circuit.Model.Measurement

/-!
# Finite-round LOCC and branchwise product-Kraus factorization

A finite-round, finite-outcome LOCC protocol on a finite set of parties `P` is an adaptive
circuit on the singleton-cell geometry `Geometry.sites P`: each layer applies local Kraus
instruments on each party, and the continuation in `Circuit.step` may depend on the full
finite tuple of outcomes from that layer (broadcast classical feed-forward).

Product-Kraus form is **not** assumed in the definition of LOCC. Instead, we extract party-local
branch operators from any layer and any adaptive circuit on `Geometry.sites P`, and prove by
structural induction that every branch Kraus operator factors as `Matrix.piKronecker` of the
party-local operators. For bipartite protocols (`P = Bool`), reindexing `Config X` to the
party-major product basis `X false × X true` packages any circuit into a
`QuantumInfo.SeparableOperation` whose induced linear map agrees with the circuit map and
inherits trace preservation (and trace nonincrease) from local trace preservation.

On `Geometry.sites P`, every cell has cost `0`, so every circuit has depth `0`
(`Circuit.depth_sites`). Thus `IsAdaptiveProtocol (Geometry.sites P) 0 Φ` imposes no bound on
the number of interactive rounds; finite-roundness comes from the inductive structure of
`Circuit`, and round bounds use `Circuit.rounds`. No claim about topological closure or
infinite-round LOCC is made here.

## Main definitions

* `QuantumCircuit.singletonRegionConfigEquiv` — identifies configurations on a singleton cell
  `{p}` with the local basis `X p`.
* `QuantumCircuit.Layer.siteKraus` — party-local Kraus operator of a layer on `Geometry.sites P`.
* `QuantumCircuit.Circuit.partyKraus` — party-local branch Kraus operator of a circuit on
  `Geometry.sites P`.
* `QuantumCircuit.boolConfigEquiv` — identifies `Bool`-indexed configurations `Config X` with
  `X false × X true`.
* `QuantumCircuit.Circuit.toSeparableOperation` — packages a bipartite circuit on
  `Geometry.sites Bool` as a `QuantumInfo.SeparableOperation`.
* `QuantumCircuit.IsFiniteRoundLOCC` — finite-round, finite-outcome LOCC protocols on parties
  `P`, defined via `IsAdaptiveProtocol (Geometry.sites P) 0`.
* `QuantumCircuit.IsBoundedRoundLOCC` — finite-round LOCC protocols with at most `r` branching
  rounds (`Circuit.rounds`).

## Main results

* `QuantumCircuit.Layer.kraus_eq_piKronecker_siteKraus` — every branch Kraus operator of a layer
  on `Geometry.sites P` is the Kronecker product of its party-local operators.
* `QuantumCircuit.Circuit.kraus_eq_piKronecker_partyKraus` — every branch Kraus operator of an
  adaptive circuit on `Geometry.sites P` is the Kronecker product of its party-local operators.
* `QuantumCircuit.submatrix_boolConfigEquiv_piKronecker` — `Matrix.piKronecker` on `Bool`
  becomes binary Kronecker product `⊗ₖ` under `boolConfigEquiv`.
* `QuantumCircuit.Circuit.toSeparableOperation_op`,
  `QuantumCircuit.Circuit.toSeparableOperation_map`,
  `QuantumCircuit.Circuit.isTP_toSeparableOperation`,
  `QuantumCircuit.Circuit.isTraceNonincreasing_toSeparableOperation` — exact branchwise,
  channel-level, and normalization agreement between a bipartite circuit and its packaged
  `SeparableOperation`.
* `QuantumCircuit.IsFiniteRoundLOCC.exists_separableOperation` — every bipartite finite-round
  LOCC channel is realized (up to `boolConfigEquiv`) by a trace-preserving `SeparableOperation`.
-/

open Matrix ManyBody
open scoped Kronecker ComplexOrder MatrixOrder

namespace QuantumCircuit

/-! ### Singleton-cell layers and party-local branch operators -/

section SingletonEquiv

variable {P : Type}

/-- Configurations on a singleton region `{p}` are equivalent to the local basis `X p`. -/
def singletonRegionConfigEquiv (X : P → Type) (p : P) : RegionConfig X {p} ≃ X p where
  toFun f := f ⟨p, Finset.mem_singleton_self p⟩
  invFun x v := (Finset.mem_singleton.mp v.2).symm ▸ x
  left_inv f := by
    funext ⟨v, hv⟩
    obtain rfl : v = p := Finset.mem_singleton.mp hv
    rfl
  right_inv _ := rfl

private theorem singletonRegionConfigEquiv_symm_apply_config {X : P → Type} (p : P)
    (x : Config X) :
    (singletonRegionConfigEquiv X p).symm (x p) = fun v : {v // v ∈ ({p} : Finset P)} ↦ x v := by
  funext ⟨v, hv⟩
  obtain rfl : v = p := Finset.mem_singleton.mp hv
  rfl

end SingletonEquiv

section SitesFactorization

variable {P : Type} [DecidableEq P] {G : Finset P → (P → Type) → (P → Type) → Type 1} [GateFamily G]

omit [GateFamily G] in
/-- On `Geometry.sites P`, a party is covered by the cells of a layer iff it belongs to
`L.cells`. -/
theorem Layer.mem_biUnion_sites_iff {X Y : P → Type} (L : Layer (Geometry.sites P) G X Y) (p : P) :
    p ∈ L.cells.biUnion (Geometry.sites P).cell ↔ p ∈ L.cells := by
  simp [Geometry.sites]

/-- The party-local Kraus operator of a layer `L` on `Geometry.sites P` at outcome `i` and
party `p`: the gate operator reindexed from `{p}` when `p ∈ L.cells`, or the onsite operator
when `p ∉ L.cells`. -/
def Layer.siteKraus (ev : Interpretation G) {X Y : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (L : Layer (Geometry.sites P) G X Y) (i : L.Index) (p : P) :
    Matrix (Y p) (X p) ℂ :=
  if hp : p ∈ L.cells then
    (ev (L.gate ⟨p, hp⟩) (i.1 ⟨p, hp⟩)).submatrix
      (singletonRegionConfigEquiv Y p).symm
      (singletonRegionConfigEquiv X p).symm
  else
    (L.onsite ⟨p, by rwa [L.mem_biUnion_sites_iff]⟩).op
      (i.2 ⟨p, by rwa [L.mem_biUnion_sites_iff]⟩)

/-- Every branch Kraus operator of a layer on `Geometry.sites P` is the Kronecker product of its
party-local operators. -/
theorem Layer.kraus_eq_piKronecker_siteKraus [Fintype P] (ev : Interpretation G) {X Y : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (L : Layer (Geometry.sites P) G X Y) (i : L.Index) :
    L.kraus ev i = Matrix.piKronecker (L.siteKraus ev i) := by
  ext y x
  rw [Layer.kraus_apply, Matrix.piKronecker_apply,
    ← Fintype.prod_subtype_mul_prod_subtype (p := (· ∈ L.cells))]
  congr 1
  · refine @Fintype.prod_equiv _ _ ℂ (Finset.Subtype.fintype L.cells)
      (Subtype.fintype fun x ↦ x ∈ L.cells) _ (Equiv.refl _) _ _ fun b ↦ ?_
    simp only [Equiv.refl_apply, Layer.siteKraus, b.2, ↓reduceDIte, Matrix.submatrix_apply]
    exact congrArg₂ (ev (L.gate b) (i.1 b))
      (singletonRegionConfigEquiv_symm_apply_config b.1 y).symm
      (singletonRegionConfigEquiv_symm_apply_config b.1 x).symm
  · let e : L.Free ≃ {p : P // p ∉ L.cells} :=
      Equiv.subtypeEquivRight fun p ↦ not_congr (L.mem_biUnion_sites_iff p)
    refine Fintype.prod_equiv e _ _ fun ⟨p, hp⟩ ↦ ?_
    have hp' : p ∉ L.cells := (L.mem_biUnion_sites_iff p).not.mp hp
    change (L.onsite ⟨p, hp⟩).op (i.2 ⟨p, hp⟩) (y p) (x p) = L.siteKraus ev i p (y p) (x p)
    simp only [Layer.siteKraus, hp', ↓reduceDIte]

/-- The party-local Kraus operator of a branch `q` of an adaptive circuit on `Geometry.sites P`,
obtained by multiplying each party's layer operators along the branch. -/
def Circuit.partyKraus (ev : Interpretation G) :
    {X Z : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : Circuit (Geometry.sites P) G X Z) → c.Index →
    (p : P) → Matrix (Z p) (X p) ℂ
  | _, _, _, _, done _, _ => fun _ ↦ 1
  | _, _, _, _, step L next, q => fun p ↦ (next q.1).partyKraus ev q.2 p * L.siteKraus ev q.1 p

@[simp] theorem Circuit.partyKraus_done (ev : Interpretation G) {X : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    (q : (Circuit.done X : Circuit (Geometry.sites P) G X X).Index) (p : P) :
    (Circuit.done X : Circuit (Geometry.sites P) G X X).partyKraus ev q p = 1 :=
  rfl

@[simp] theorem Circuit.partyKraus_step (ev : Interpretation G) {X Y Z : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (L : Layer (Geometry.sites P) G X Y) (next : L.Index → Circuit (Geometry.sites P) G Y Z)
    (i : L.Index) (j : (next i).Index) (p : P) :
    (Circuit.step L next).partyKraus ev ⟨i, j⟩ p =
      (next i).partyKraus ev j p * L.siteKraus ev i p :=
  rfl

/-- **Branchwise product-Kraus factorization.** Every branch Kraus operator of an adaptive circuit
on `Geometry.sites P` factors as `Matrix.piKronecker` of the party-local branch operators. No
trace-preservation hypothesis is required. -/
theorem Circuit.kraus_eq_piKronecker_partyKraus [Fintype P] (ev : Interpretation G) :
    {X Z : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    (c : Circuit (Geometry.sites P) G X Z) → (q : c.Index) →
    c.kraus ev q = Matrix.piKronecker (c.partyKraus ev q)
  | _, _, _, _, done _, _ => Matrix.piKronecker_one.symm
  | _, _, _, _, step L next, q => by
      change (next q.1).kraus ev q.2 * L.kraus ev q.1 = _
      rw [kraus_eq_piKronecker_partyKraus ev (next q.1) q.2,
        L.kraus_eq_piKronecker_siteKraus ev q.1, Matrix.piKronecker_mul]
      rfl

/-! ### Zero depth on `Geometry.sites P` -/

omit [GateFamily G] in
/-- Every layer on `Geometry.sites P` has depth `0` because every singleton cell has cost `0`. -/
theorem Layer.depth_sites {X Y : P → Type} (L : Layer (Geometry.sites P) G X Y) :
    L.depth = 0 := by
  simp [Layer.depth, Geometry.sites]

/-- Every circuit on `Geometry.sites P` has depth `0`, regardless of how many rounds it has. -/
theorem Circuit.depth_sites [Fintype P] :
    {X Z : P → Type} → (c : Circuit (Geometry.sites P) G X Z) → c.depth = 0
  | _, _, done _ => rfl
  | _, _, step L next => by
      rw [Circuit.depth_step, L.depth_sites, zero_add]
      exact (Finset.sup_eq_bot_iff _ _).mpr fun i _ ↦ Circuit.depth_sites (next i)

end SitesFactorization

/-! ### Bipartite reindexing and `QuantumInfo.SeparableOperation` bridge -/

section Bipartite

/-- Equivalence between `Bool`-indexed party configurations `Config X` and the party-major
product basis `X false × X true`. -/
def boolConfigEquiv (X : Bool → Type) : Config X ≃ X false × X true where
  toFun f := (f false, f true)
  invFun p b := match b with
    | false => p.1
    | true => p.2
  left_inv f := funext fun b ↦ by cases b <;> rfl
  right_inv _ := rfl

/-- Under `boolConfigEquiv`, `Matrix.piKronecker` on `Bool` is the binary Kronecker product
`⊗ₖ`. -/
theorem submatrix_boolConfigEquiv_piKronecker {X Z : Bool → Type}
    (K : (b : Bool) → Matrix (Z b) (X b) ℂ) :
    (Matrix.piKronecker K).submatrix (boolConfigEquiv Z).symm (boolConfigEquiv X).symm =
      K false ⊗ₖ K true := by
  ext ⟨z₀, z₁⟩ ⟨x₀, x₁⟩
  simp [boolConfigEquiv, Matrix.piKronecker_apply, Matrix.kroneckerMap_apply, mul_comm]

variable {G : Finset Bool → (Bool → Type) → (Bool → Type) → Type 1} [GateFamily G]
  {X Z : Bool → Type} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- Package a bipartite adaptive circuit on `Geometry.sites Bool` as a
`QuantumInfo.SeparableOperation` indexed by the circuit branches. -/
def Circuit.toSeparableOperation (ev : Interpretation G)
    (c : Circuit (Geometry.sites Bool) G X Z) :
    QuantumInfo.SeparableOperation (X false) (X true) (Z false) (Z true) where
  Index := c.Index
  left q := c.partyKraus ev q false
  right q := c.partyKraus ev q true

/-- Branchwise agreement: each product Kraus operator of `c.toSeparableOperation ev` is the
circuit's branch Kraus operator reindexed along `boolConfigEquiv`. -/
theorem Circuit.toSeparableOperation_op (ev : Interpretation G)
    (c : Circuit (Geometry.sites Bool) G X Z) (q : c.Index) :
    (c.toSeparableOperation ev).toKrausFamily.op q =
      (c.kraus ev q).submatrix (boolConfigEquiv Z).symm (boolConfigEquiv X).symm := by
  change c.partyKraus ev q false ⊗ₖ c.partyKraus ev q true = _
  rw [c.kraus_eq_piKronecker_partyKraus ev q, submatrix_boolConfigEquiv_piKronecker]

/-- As a `KrausFamily`, `(c.toSeparableOperation ev).toKrausFamily` is the reindexing of
`c.krausFamily ev` along `boolConfigEquiv`. -/
theorem Circuit.toSeparableOperation_toKrausFamily (ev : Interpretation G)
    (c : Circuit (Geometry.sites Bool) G X Z) :
    (c.toSeparableOperation ev).toKrausFamily =
      (c.krausFamily ev).reindex (boolConfigEquiv X).symm (boolConfigEquiv Z).symm := by
  cases c <;>
    exact congrArg (KrausFamily.mk _) (funext fun q ↦ Circuit.toSeparableOperation_op ev _ q)

/-- Channel-level agreement on party-major matrices: the map of `c.toSeparableOperation ev` agrees
with `c.map ev` conjugated by `boolConfigEquiv`. -/
theorem Circuit.toSeparableOperation_map [∀ b, Fintype (Z b)] (ev : Interpretation G)
    (c : Circuit (Geometry.sites Bool) G X Z)
    (ρ : Matrix (X false × X true) (X false × X true) ℂ) :
    (c.toSeparableOperation ev).map ρ =
      (c.map ev (ρ.submatrix (boolConfigEquiv X) (boolConfigEquiv X))).submatrix
        (boolConfigEquiv Z).symm (boolConfigEquiv Z).symm := by
  rw [QuantumInfo.SeparableOperation.map, KrausFamily.map_apply, Circuit.map, KrausFamily.map_apply,
    Matrix.submatrix_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [c.toSeparableOperation_op ev q, Matrix.conjTranspose_submatrix]
  have hρ : ρ = (ρ.submatrix (boolConfigEquiv X) (boolConfigEquiv X)).submatrix
      (boolConfigEquiv X).symm (boolConfigEquiv X).symm := by
    ext a b
    simp
  conv_lhs =>
    rw [hρ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

/-- Channel-level agreement on configuration matrices: `c.map ev` is the map of
`c.toSeparableOperation ev` conjugated back along `boolConfigEquiv`. -/
theorem Circuit.map_eq_submatrix_toSeparableOperation_map [∀ b, Fintype (Z b)]
    (ev : Interpretation G) (c : Circuit (Geometry.sites Bool) G X Z)
    (σ : Matrix (Config X) (Config X) ℂ) :
    c.map ev σ =
      ((c.toSeparableOperation ev).map
        (σ.submatrix (boolConfigEquiv X).symm (boolConfigEquiv X).symm)).submatrix
        (boolConfigEquiv Z) (boolConfigEquiv Z) := by
  rw [c.toSeparableOperation_map ev]
  have hσ : (σ.submatrix (boolConfigEquiv X).symm (boolConfigEquiv X).symm).submatrix
      (boolConfigEquiv X) (boolConfigEquiv X) = σ := by
    ext a b
    simp
  rw [hσ]
  ext a b
  simp

/-- If every local Kraus family of a bipartite circuit is trace-preserving, then its packaged
`SeparableOperation` is trace-preserving. -/
theorem Circuit.isTP_toSeparableOperation [∀ b, Fintype (Z b)] (ev : Interpretation G)
    (c : Circuit (Geometry.sites Bool) G X Z) (h : c.Forall ev KrausFamily.IsTP) :
    (c.toSeparableOperation ev).IsTP := by
  rw [QuantumInfo.SeparableOperation.IsTP, c.toSeparableOperation_toKrausFamily ev]
  exact (c.isTP_krausFamily ev h).reindex (boolConfigEquiv X).symm (boolConfigEquiv Z).symm

/-- If every local Kraus family of a bipartite circuit is trace-nonincreasing, then its packaged
`SeparableOperation` is trace-nonincreasing. -/
theorem Circuit.isTraceNonincreasing_toSeparableOperation [∀ b, Fintype (Z b)]
    (ev : Interpretation G) (c : Circuit (Geometry.sites Bool) G X Z)
    (h : c.Forall ev KrausFamily.IsTraceNonincreasing) :
    (c.toSeparableOperation ev).IsTraceNonincreasing := by
  rw [QuantumInfo.SeparableOperation.IsTraceNonincreasing,
    c.toSeparableOperation_toKrausFamily ev, KrausFamily.IsTraceNonincreasing,
    KrausFamily.effect_reindex]
  have hle : (c.krausFamily ev).effect ≤ 1 := c.isTraceNonincreasing_krausFamily ev h
  rw [Matrix.le_iff] at hle ⊢
  have hsub : (1 : Matrix (X false × X true) (X false × X true) ℂ) -
      (c.krausFamily ev).effect.submatrix (boolConfigEquiv X).symm (boolConfigEquiv X).symm =
      (1 - (c.krausFamily ev).effect).submatrix
        (boolConfigEquiv X).symm (boolConfigEquiv X).symm := by
    ext a b
    simp [Matrix.one_apply]
  rw [hsub]
  exact hle.submatrix (boolConfigEquiv X).symm

end Bipartite

/-! ### Operational finite-round LOCC predicates and `LOCC ⊆ SEP` -/

section LOCC

variable (P : Type) [Fintype P] [DecidableEq P]

/-- A linear map realised by a finite-round, finite-outcome LOCC protocol on parties `P`:
an adaptive circuit of trace-preserving local Kraus instruments on `Geometry.sites P`.

The depth bound `0` reflects the zero cell cost of `Geometry.sites P` (`Circuit.depth_sites`),
not a restriction to zero rounds; finite-outcome classical feed-forward is encoded by
`Circuit.step`. No claim about topological closure or infinite-round LOCC is made here. -/
def IsFiniteRoundLOCC {X Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Z p)]
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  IsAdaptiveProtocol (Geometry.sites P) 0 Φ

/-- A linear map realised by an LOCC protocol on parties `P` with at most `r` branching rounds
(`Circuit.rounds`). -/
def IsBoundedRoundLOCC {X Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
    [∀ p, Fintype (Z p)] (r : ℕ)
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit (Geometry.sites P) KrausGate X Z,
    c.Forall KrausGate.ev KrausFamily.IsTP ∧ c.rounds ≤ r ∧ c.map KrausGate.ev = Φ

variable {P} {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] [∀ p, Fintype (Z p)]

/-- Unfolding `IsFiniteRoundLOCC`: the depth bound `0` is automatic on `Geometry.sites P`, so
`IsFiniteRoundLOCC P Φ` says precisely that `Φ` is the map of some locally trace-preserving
adaptive circuit on `Geometry.sites P`. -/
theorem isFiniteRoundLOCC_iff
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ} :
    IsFiniteRoundLOCC P Φ ↔
      ∃ c : Circuit (Geometry.sites P) KrausGate X Z,
        c.Forall KrausGate.ev KrausFamily.IsTP ∧ c.map KrausGate.ev = Φ := by
  constructor
  · rintro ⟨c, hTP, -, hmap⟩
    exact ⟨c, hTP, hmap⟩
  · rintro ⟨c, hTP, hmap⟩
    exact ⟨c, hTP, c.depth_sites.le, hmap⟩

/-- Classical feed-forward for finite-round LOCC: a layer of trace-preserving local instruments
followed, on each outcome `i`, by a finite-round LOCC protocol `Ψ i` is a finite-round LOCC
protocol. -/
theorem IsFiniteRoundLOCC.step
    (L : Layer (Geometry.sites P) KrausGate X Y)
    (hL : L.Forall KrausGate.ev KrausFamily.IsTP)
    {Ψ : L.Index → Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (hΨ : ∀ i, IsFiniteRoundLOCC P (Ψ i)) :
    IsFiniteRoundLOCC P (∑ i, Ψ i ∘ₗ singleKrausMap (L.kraus KrausGate.ev i)) := by
  simpa [IsFiniteRoundLOCC, L.depth_sites] using IsAdaptiveProtocol.step L hL hΨ

/-- The identity map is a `0`-round LOCC protocol. -/
theorem IsBoundedRoundLOCC.id :
    IsBoundedRoundLOCC P 0 (LinearMap.id : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] _) :=
  ⟨Circuit.done X, trivial, le_rfl, Circuit.map_done _⟩

/-- Monotonicity of bounded-round LOCC in the round bound. -/
theorem IsBoundedRoundLOCC.mono {r r' : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedRoundLOCC P r Φ) (hr : r ≤ r') : IsBoundedRoundLOCC P r' Φ :=
  let ⟨c, hTP, hrc, hmap⟩ := h
  ⟨c, hTP, hrc.trans hr, hmap⟩

/-- Bounded-round LOCC protocols compose, with additive round bound. -/
theorem IsBoundedRoundLOCC.comp {r r' : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ}
    {Ψ : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (hΦ : IsBoundedRoundLOCC P r Φ) (hΨ : IsBoundedRoundLOCC P r' Ψ) :
    IsBoundedRoundLOCC P (r + r') (Ψ ∘ₗ Φ) := by
  obtain ⟨c, hcTP, hcr, rfl⟩ := hΦ
  obtain ⟨c', hc'TP, hc'r, rfl⟩ := hΨ
  exact ⟨c.comp c', hcTP.comp _ hc'TP,
    (Circuit.rounds_comp c c').trans (Nat.add_le_add hcr hc'r), Circuit.map_comp _ c c'⟩

/-- Every bounded-round LOCC protocol is a finite-round LOCC protocol. -/
theorem IsBoundedRoundLOCC.isFiniteRoundLOCC {r : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedRoundLOCC P r Φ) : IsFiniteRoundLOCC P Φ :=
  let ⟨c, hTP, _, hmap⟩ := h
  isFiniteRoundLOCC_iff.mpr ⟨c, hTP, hmap⟩

/-- A map is a finite-round LOCC protocol iff it is realised with some finite round bound. -/
theorem isFiniteRoundLOCC_iff_exists_isBoundedRoundLOCC
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ} :
    IsFiniteRoundLOCC P Φ ↔ ∃ r, IsBoundedRoundLOCC P r Φ := by
  rw [isFiniteRoundLOCC_iff]
  constructor
  · rintro ⟨c, hTP, hmap⟩
    exact ⟨c.rounds, c, hTP, le_rfl, hmap⟩
  · rintro ⟨_, c, hTP, -, hmap⟩
    exact ⟨c, hTP, hmap⟩

/-- **Finite-round bipartite LOCC ⊆ SEP.** Every bipartite finite-round, finite-outcome LOCC
protocol `Φ` is realised (up to `boolConfigEquiv`) by a trace-preserving
`QuantumInfo.SeparableOperation`. -/
theorem IsFiniteRoundLOCC.exists_separableOperation {X Z : Bool → Type}
    [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)] [∀ b, Fintype (Z b)]
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsFiniteRoundLOCC Bool Φ) :
    ∃ S : QuantumInfo.SeparableOperation (X false) (X true) (Z false) (Z true),
      S.IsTP ∧
      ∀ ρ : Matrix (X false × X true) (X false × X true) ℂ,
        S.map ρ =
          (Φ (ρ.submatrix (boolConfigEquiv X) (boolConfigEquiv X))).submatrix
            (boolConfigEquiv Z).symm (boolConfigEquiv Z).symm := by
  obtain ⟨c, hTP, rfl⟩ := isFiniteRoundLOCC_iff.mp h
  exact ⟨c.toSeparableOperation KrausGate.ev, c.isTP_toSeparableOperation KrausGate.ev hTP,
    c.toSeparableOperation_map KrausGate.ev⟩

end LOCC

end QuantumCircuit
