/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.SwapRouting
import QICLean.Circuit.Compile.Universality
import QICLean.Circuit.Model.UnitaryPlacement
import QICLean.Circuit.Protocol.ZeroRegister.Projection

/-!
# Gate counts of the zero-register reflection

A unitary supported on a nonempty set `T` of sites is a unitary on the configurations of `T`,
so by two-site universality on the sites of `T` and placement on `T` it is a product of gates
on the geometry of sites and ordered pairs of cost at most `unitaryGateCount T · c₂`, a number
depending only on the bases at the sites of `T`. Each step of the reversible conjunction acts
on at most three sites of the `a + a` sites of the zero register, so with pairs of cost `1` it
costs at most `6 (d³)⁴` such gates; the conjunction of all `a` steps costs `a` times this, the
scratch phase acts on one site and is free, and the zero-register reflection costs twice the
conjunction. On the open chain of the `a + a` sites, routing every pair gate by SWAP gates
multiplies the count by `2 (a + a)`.

The circuit relabelled along the injection of the zero register into the selected flags and the
first `a` sites of a pool appended to `n` logical sites is a circuit of the same count on sites
and ordered pairs of the `n + A` sites, so on the open chain the reflection on the selected
sites costs at most `2 (n + A) · 12 (d³)⁴ a` neighbouring gates. With its clean action this
implements the selected-flags reflection, and the reflection about the range of the zero-flag
inclusion, with the whole pool returned to `0`; an empty selection is the global phase `-1`,
which costs nothing.

The declarations restate the gate counts of `TNLean/Circuit/ZeroRegisterConjunction.lean`,
`TNLean/Circuit/ZeroRegisterReflection.lean`, `TNLean/Circuit/SelectedZeroRegisterReflection.lean`,
`TNLean/Circuit/SelectedZeroRegisterReflectionPool.lean` and
`TNLean/Circuit/InitializedRegisterProjection.lean` (Apache-2.0). The changes: the count of a step
is `unitaryGateCount` of its at most three sites, at most `6 (d³)⁴` pair gates, instead of the
synthesis count `38 (d³)⁶ + 1`; the scratch phase is a one-site unitary of cost `0`; the
circuit is first a product of gates on sites and ordered pairs, and the count on the open chain
follows by routing; the pool of size `a` is the case `A = a` of the pool of size `A ≥ a`; the
empty selection needs one logical site instead of two and costs `0` instead of one gate.

## Main definitions

* `QuantumCircuit.zeroConjunctionStepGateCount`, `QuantumCircuit.zeroRegisterReflectionGateCount`
  — the counts on sites and ordered pairs.
* `QuantumCircuit.sitesAndPairsHom` — sites and ordered pairs along an injection of sites.

## Main results

* `QuantumCircuit.IsGateProduct.sitesAndPairs_of_mem_supportedOperators` — a unitary supported
  on `T` costs at most `unitaryGateCount T · c₂`.
* `QuantumCircuit.isGateProduct_zeroConjunctionStep`,
  `QuantumCircuit.isGateProduct_zeroConjunctionPerm` — the conjunction.
* `QuantumCircuit.isGateProduct_zeroRegisterReflection` — compute, phase, uncompute.
* `QuantumCircuit.isGateProduct_pathGraph_zeroRegisterReflection` — on the open chain.
* `QuantumCircuit.isGateProduct_selectedZeroRegisterReflection`,
  `QuantumCircuit.isGateProduct_pathGraph_selectedZeroRegisterReflection` — on the selected sites.
* `QuantumCircuit.exists_isGateProduct_isCleanImplementation_selectedZeroRegister`,
  `QuantumCircuit.exists_isGateProduct_isCleanImplementation_zeroFlagReflection` — clean
  implementations by neighbouring gates.
-/

open Matrix ManyBody

namespace QuantumCircuit

section Region

variable {S : Type} [Fintype S] [DecidableEq S] {X : S → Type} [∀ s, Fintype (X s)]
  [∀ s, DecidableEq (X s)]

/-- **Unitaries on a set of sites.** A unitary supported on a nonempty set `T` of sites is a
product of gates on sites and ordered pairs of cost at most `unitaryGateCount T · c₂`, where `c₂`
is the cost of a pair; the bound holds for any one-site cost `c₁`. -/
theorem IsGateProduct.sitesAndPairs_of_mem_supportedOperators (c₁ c₂ : ℕ) {T : Finset S}
    (hT : T.Nonempty) {Z : Matrix (Config X) (Config X) ℂ} (hZu : Z ∈ unitaryGroup (Config X) ℂ)
    (hZ : Z ∈ supportedOperators X T) :
    IsGateProduct (Geometry.sitesAndPairs S c₁ c₂)
      (unitaryGateCount {s // s ∈ T} (fun s ↦ X s.1) * c₂) Z := by
  by_cases hne : ∀ s, Nonempty (X s)
  · obtain ⟨V, rfl⟩ := exists_eq_place_of_mem_supportedOperators hZ
    have hV : V ∈ unitaryGroup _ ℂ := place_mem_unitaryGroup_iff.mp hZu
    have : Nonempty {s // s ∈ T} := hT.to_subtype
    refine IsGateProduct.of_restrict (isGateProduct_unitaryGateCount
      (fun s t hst Z' hZ'u hZ' ↦ ?_) hV)
    have hsub : (Geometry.sitesAndPairs S c₁ c₂).cell
        (Sum.inr ⟨(s.1, t.1), fun h ↦ hst (Subtype.ext h)⟩) ⊆ T := by
      intro v hv
      rcases Geometry.mem_sitesAndPairs_cell_inr.mp hv with rfl | rfl
      exacts [s.2, t.2]
    have hcell : ((Geometry.sitesAndPairs S c₁ c₂).restrict T).cell
        ⟨Sum.inr ⟨(s.1, t.1), fun h ↦ hst (Subtype.ext h)⟩, hsub⟩ = {s, t} := by
      ext v
      simp only [Geometry.restrict, Finset.mem_subtype, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton, Subtype.ext_iff]
    exact IsGateProduct.of_mem_supportedOperators hZ'u (hcell ▸ hZ')
  · push Not at hne
    obtain ⟨s, hs⟩ := hne
    have : IsEmpty (Config X) := ⟨fun σ ↦ hs.false (σ s)⟩
    rw [Subsingleton.elim Z 1]
    exact IsGateProduct.one _ X _

end Region

variable {d a : ℕ} [NeZero d]

/-- The count of one conjunction step on sites and ordered pairs of cost `1`. -/
def zeroConjunctionStepGateCount (d : ℕ) : ℕ :=
  6 * (d ^ 3) ^ 4

/-- Each conjunction step is a product of at most `6 (d³)⁴` gates on sites and ordered pairs of
cost `1`. -/
theorem isGateProduct_zeroConjunctionStep (hd : 2 ≤ d) (j : Fin a) :
    IsGateProduct (Geometry.sitesAndPairs (Fin (a + a)) 0 1) (zeroConjunctionStepGateCount d)
      ((zeroConjunctionStep (d := d) j).permMatrix ℂ) := by
  have h := IsGateProduct.sitesAndPairs_of_mem_supportedOperators (X := Qudits (Fin (a + a)) d)
    0 1 ⟨Fin.natAdd a j, by simp [zeroConjunctionStepSites]⟩
    (Equiv.Perm.permMatrix_mem_unitaryGroup _)
    (permMatrix_zeroConjunctionStep_mem_supportedOperators j)
  refine h.mono ?_
  rw [mul_one, zeroConjunctionStepGateCount]
  refine (unitaryGateCount_le fun _ ↦ by simpa using hd).trans ?_
  simp only [Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  have := card_zeroConjunctionStepSites_le j
  gcongr

/-- The first `k` conjunction steps are a product of at most `k` times the step count. -/
theorem isGateProduct_zeroConjunctionPerm (hd : 2 ≤ d) (k : ℕ) :
    IsGateProduct (Geometry.sitesAndPairs (Fin (a + a)) 0 1)
      (k * zeroConjunctionStepGateCount d)
      ((zeroConjunctionPerm (d := d) (a := a) k).permMatrix ℂ) := by
  induction k with
  | zero => simpa [zeroConjunctionPerm] using IsGateProduct.one _ (Qudits (Fin (a + a)) d) 0
  | succ k ih =>
    rw [zeroConjunctionPerm]
    split_ifs with hk
    · rw [Matrix.permMatrix_mul, Nat.succ_mul]
      exact ih.mul (isGateProduct_zeroConjunctionStep hd ⟨k, hk⟩)
    · exact ih.mono (Nat.mul_le_mul_right _ (Nat.le_succ k))

/-- The count of the zero-register reflection on sites and ordered pairs of cost `1`: twice the
conjunction, the scratch phase being free. -/
def zeroRegisterReflectionGateCount (d a : ℕ) : ℕ :=
  12 * (d ^ 3) ^ 4 * a

/-- **The zero-register reflection as a circuit.** Compute, phase and uncompute is a product of
at most `12 (d³)⁴ a` gates on sites and ordered pairs of cost `1`. -/
theorem isGateProduct_zeroRegisterReflection (hd : 2 ≤ d) (ha : 0 < a) :
    IsGateProduct (Geometry.sitesAndPairs (Fin (a + a)) 0 1) (zeroRegisterReflectionGateCount d a)
      (zeroRegisterReflection (d := d) ha) := by
  have hnet := isGateProduct_zeroConjunctionPerm (d := d) (a := a) hd a
  have hphase := IsGateProduct.of_mem_supportedOperators_singleton
    (Γ := Geometry.sitesAndPairs (Fin (a + a)) 0 1) (diagonal_ite_neg_one_mem_unitaryGroup _)
    (zeroScratchPhase_mem_supportedOperators (d := d) ha) 0
  refine ((hnet.mul hphase).mul hnet.conjTranspose).mono (le_of_eq ?_)
  simp only [zeroRegisterReflectionGateCount, zeroConjunctionStepGateCount]
  ring

/-- On the open chain of the `a + a` sites, the zero-register reflection is a product of at most
`2 (a + a) · 12 (d³)⁴ a` neighbouring gates. -/
theorem isGateProduct_pathGraph_zeroRegisterReflection (hd : 2 ≤ d) (ha : 0 < a) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (a + a)))
      (2 * (a + a) * zeroRegisterReflectionGateCount d a) (zeroRegisterReflection (d := d) ha) :=
  (isGateProduct_zeroRegisterReflection hd ha).of_sitesAndPairs le_rfl

section Selected

variable {n A : ℕ}

/-- Along an injection `ι : Fin m ↪ Fin N` of sites, each site and each ordered pair of distinct
sites of `Fin m` goes to the cell of its image under `ι`. -/
def sitesAndPairsHom {m N : ℕ} (c₁ c₂ : ℕ) (ι : Fin m ↪ Fin N) :
    (Geometry.sitesAndPairs (Fin m) c₁ c₂).Hom (Geometry.sitesAndPairs (Fin N) c₁ c₂) ι where
  cellMap := ⟨Sum.map ι fun p ↦ ⟨(ι p.1.1, ι p.1.2), ι.injective.ne p.2⟩, by
    rintro (p | p) (q | q) h <;> simp only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq,
      Sum.inr.injEq, reduceCtorEq, Subtype.mk.injEq, Prod.mk.injEq] at h
    · rw [ι.injective h]
    · rw [Subtype.ext (Prod.ext (ι.injective h.1) (ι.injective h.2))]⟩
  cell_cellMap := by
    rintro (p | p) <;> simp <;> rfl

/-- The sites of the zero register, identified with the region they occupy among the `n + A`
sites: the selected flags and the first `a` pool sites. -/
private noncomputable def selectedSitesEquiv (s : Fin a ↪ Fin n) (hpool : a ≤ A) :
    Fin (a + a) ≃ {v // v ∈ Finset.univ.map (selectedZeroRegisterSites s hpool)} :=
  (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans
    (Finset.univ.equivMap (selectedZeroRegisterSites s hpool))

/-- **The reflection on the selected sites as a circuit.** With pairs of cost `1`, the
zero-register reflection on the selected flags and the first `a` pool sites is a product of at
most `12 (d³)⁴ a` gates on sites and ordered pairs of the `n + A` sites. -/
theorem isGateProduct_selectedZeroRegisterReflection (hd : 2 ≤ d) (s : Fin a ↪ Fin n)
    (hpool : a ≤ A) (ha : 0 < a) :
    IsGateProduct (Geometry.sitesAndPairs (Fin (n + A)) 0 1)
      (zeroRegisterReflectionGateCount d a)
      (selectedZeroRegisterReflection (d := d) s hpool ha) := by
  set ι := selectedZeroRegisterSites s hpool
  set D := Finset.univ.map ι
  have h := ((isGateProduct_zeroRegisterReflection (d := d) hd ha).isUnitaryCircuitOn_of_hom
    (X := Qudits (Fin (n + A)) d) (selectedSitesEquiv s hpool) (sitesAndPairsHom 0 1 ι)
    (by rintro (p | p) <;> rfl)).2
  convert h using 1
  ext z z'
  have hcfg : ∀ y : Fin (n + A) → Fin d,
      (siteConfigurationEquiv (selectedSitesEquiv s hpool) fun _ ↦ Equiv.refl _).symm
        (fun v : {v // v ∈ D} ↦ y v) = y ∘ ι := fun y ↦ funext fun p ↦ by
    rw [siteConfigurationEquiv_symm_apply]
    rfl
  have hoff : (∀ v ∉ D, z v = z' v) ↔ ∀ v ∉ Set.range ι, z v = z' v := by simp [D]
  rw [selectedZeroRegisterReflection_apply, place_apply, reindex_apply, submatrix_apply]
  split_ifs with h₁ h₂ h₂
  · exact (congrArg₂ (zeroRegisterReflection ha) (hcfg z) (hcfg z')).symm
  · exact absurd (hoff.mpr h₁) h₂
  · exact absurd (hoff.mp h₂) h₁
  · rfl

/-- On the open chain of the `n + A` sites, the reflection on the selected sites is a product of
at most `2 (n + A) · 12 (d³)⁴ a` neighbouring gates. -/
theorem isGateProduct_pathGraph_selectedZeroRegisterReflection (hd : 2 ≤ d) (s : Fin a ↪ Fin n)
    (hpool : a ≤ A) (ha : 0 < a) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (n + A)))
      (2 * (n + A) * zeroRegisterReflectionGateCount d a)
      (selectedZeroRegisterReflection (d := d) s hpool ha) :=
  (isGateProduct_selectedZeroRegisterReflection hd s hpool ha).of_sitesAndPairs le_rfl

/-- **Selected flags with a shared clean pool.** For `n ≥ 1` logical sites and a pool of
`A ≥ a` sites, the selected-flags reflection has a clean implementation, with the whole pool as
workspace, by a product of at most `2 (n + A) · 12 (d³)⁴ a` neighbouring gates; for an empty
selection it is the global phase `-1`, which costs nothing. -/
theorem exists_isGateProduct_isCleanImplementation_selectedZeroRegister (hd : 2 ≤ d)
    (hn : 0 < n) (s : Fin a ↪ Fin n) (hpool : a ≤ A) :
    ∃ U, IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (n + A)))
        (2 * (n + A) * zeroRegisterReflectionGateCount d a) U ∧
      IsCleanImplementation
        (basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d))) U
        (selectedZeroRegisterLogical s) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have : Nonempty (Fin (n + A)) := ⟨⟨0, by omega⟩⟩
    refine ⟨(-1 : ℂ) • 1, IsGateProduct.smul_one (by simp) _, ?_⟩
    rw [IsCleanImplementation, selectedZeroRegisterLogical_empty]
    simp
  · exact ⟨_, isGateProduct_pathGraph_selectedZeroRegisterReflection hd s hpool ha,
      isCleanImplementation_selectedZeroRegisterReflection hd s hpool ha⟩

/-- **The reflection about the zero-flag range.** The same circuit implements the reflection
`1 - 2 E E†` about the range of the zero-flag inclusion `E`. -/
theorem exists_isGateProduct_isCleanImplementation_zeroFlagReflection (hd : 2 ≤ d)
    (hn : 0 < n) (s : Fin a ↪ Fin n) (hpool : a ≤ A) :
    ∃ U, IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (n + A)))
        (2 * (n + A) * zeroRegisterReflectionGateCount d a) U ∧
      IsCleanImplementation
        (basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d))) U
        (subspaceReflection (basisInclusion (zeroFlagEmbedding (d := d) s) *
          (basisInclusion (zeroFlagEmbedding (d := d) s))ᴴ)) := by
  rw [← selectedZeroRegisterLogical_eq_subspaceReflection]
  exact exists_isGateProduct_isCleanImplementation_selectedZeroRegister hd hn s hpool

end Selected

end QuantumCircuit
