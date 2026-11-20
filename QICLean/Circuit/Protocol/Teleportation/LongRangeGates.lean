/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Fin.Tuple.Embedding
import QICLean.Circuit.Protocol.Teleportation.Chains

/-!
# Layers of gates between distant sites in constant depth with measurements

The paragraph "Tree-RG circuit with measurements" of arXiv:2307.01696 observes that the
isometries of eq. (16) "act on a constant number of sites which, although spatially separated,
can be teleported at neighboring registers with a constant overhead", so that "every isometry in
eq. (16) takes constant time using measurement". This file proves this for a whole layer of
two-site gates on pairwise disjoint stretches of the ring.

A *long-range gate* (`QuantumCircuit.LongRangeGate`) is a two-site unitary `u` on the sites `a`
and `a + 2L + 1` of the ring, with `2L + 1 < N`. For a list of long-range gates whose stretches
`a, a + 1, …, a + 2L + 1` are pairwise disjoint, two teleportation rounds of total depth at most
`5` (`QuantumCircuit.LongRangeGate.rounds`) do the following, in parallel for all the gates:
teleport the content of `a` along the forward chain of `L` hops to `a + 2L`; apply `u` to the
neighbouring pair `{a + 2L, a + 2L + 1}`; teleport the content of `a + 2L` back to `a` along the
backward chain. On the vectors with `|0⟩` at the `2L` sites strictly between `a` and
`a + 2L + 1` for every gate, the circuit implements the product of the gates `u` at the sites
`a`, `a + 2L + 1` (`QuantumCircuit.LongRangeGate.isImplementationOn_rounds`). No outcome is
post-selected, and the depth does not depend on the distances `2L + 1` nor on the number of
gates.

**Scope restriction (odd separations, disjoint stretches):** a gate joins the sites `a` and
`a + 2L + 1`, at odd separation, the stretches of the gates of a layer are pairwise disjoint, and
the `2L` sites strictly between `a` and `a + 2L + 1` carry `|0⟩`; gates at even separation or on
overlapping stretches are not covered, whereas the cited paragraph of arXiv:2307.01696 speaks of
teleporting spatially separated sites in general. Documented in TNLean's
`docs/paper-gaps/mswc24_tree_measurement_scope.tex`.

## Main definitions

* `QuantumCircuit.placeAlong` — a matrix on `ι` sites placed along an injection into the sites.
* `QuantumCircuit.LongRangeGate`, `QuantumCircuit.LongRangeGate.op`.
* `QuantumCircuit.LongRangeGate.rounds` — the two rounds applying a layer of long-range gates.

## Main results

* `QuantumCircuit.placeAlong_apply`, `QuantumCircuit.sitePermOp_mul_placeAlong_mul` — the
  entries of a placement along an injection, and its conjugation by a permutation of sites.
* `QuantumCircuit.TeleportHop.valid_flatMap`, `QuantumCircuit.TeleportHop.sitePerm_flatMap_apply`
  — chains on pairwise disjoint sets of sites run in parallel.
* `QuantumCircuit.LongRangeGate.depth_rounds_le` — the two rounds have depth at most `5`.
* `QuantumCircuit.LongRangeGate.isImplementationOn_rounds`.

The declarations restate `TNLean/Circuit/Teleportation/LongRangeGates.lean` at commit
`414a18fb88` (Apache-2.0). The changes: the gates on the ring are placements along injections
`QuantumCircuit.placeAlong`, in place of TNLean's `embedOp`; the layer of local gates is
`Layer.ofList`; the two rounds form one circuit, `Circuit.comp`, of depth at most `5`, which
implements the product of the gates; the permutation matrices are `ManyBody.sitePermOp`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), eq. (16) and paragraph "Tree-RG circuit with
  measurements".
-/

open Matrix ManyBody

/-- A permutation fixing every point outside `S` maps `S` into `S`. -/
theorem Equiv.Perm.apply_mem_of_forall_notMem {α : Type*} {π : Equiv.Perm α}
    {S : Set α} (hπ : ∀ i ∉ S, π i = i) {i : α} (hi : i ∈ S) : π i ∈ S := by
  by_contra h
  exact h (by rw [π.injective (hπ _ h)]; exact hi)

/-- Conjugating a product by `P` with inverse `Q` conjugates every factor. -/
theorem List.mul_prod_mul_of_mul_eq_one {M : Type*} [Monoid M] {P Q : M}
    (hQP : Q * P = 1) (hPQ : P * Q = 1) (l : List M) :
    P * l.prod * Q = (l.map fun X ↦ P * X * Q).prod := by
  induction l with
  | nil => simpa using hPQ
  | cons X l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    calc P * (X * l.prod) * Q = P * X * (Q * P) * l.prod * Q := by
          rw [hQP, mul_one]; simp only [mul_assoc]
      _ = P * X * Q * (P * l.prod * Q) := by simp only [mul_assoc]

namespace QuantumCircuit

/-! ### Placements along injections -/

section PlaceAlong

variable {S ι : Type} [Fintype S] [DecidableEq S] [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The sites of `ι` are the sites of the image of an injection `f : ι ↪ S`. -/
noncomputable def placeAlongSiteEquiv (f : ι ↪ S) : ι ≃ {v // v ∈ Finset.univ.map f} :=
  (Equiv.subtypeUnivEquiv Finset.mem_univ).symm.trans (Finset.univ.equivMap f)

/-- The configurations of the image of an injection `f : ι ↪ S` are the configurations of `ι`. -/
noncomputable def placeAlongEquiv (f : ι ↪ S) :
    RegionConfig (Qudits S d) (Finset.univ.map f) ≃ Config (Qudits ι d) :=
  (siteConfigurationEquiv (placeAlongSiteEquiv f) fun _ ↦ Equiv.refl (Fin d)).symm

omit [Fintype S] [DecidableEq S] [DecidableEq ι] in
theorem placeAlongSiteEquiv_apply (f : ι ↪ S) (i : ι) : (placeAlongSiteEquiv f i : S) = f i :=
  rfl

/-- The matrix `X` on the sites `ι` placed along the injection `f`: `X` acts on the sites `f i`,
and the identity on the others. -/
noncomputable def placeAlong (f : ι ↪ S)
    (X : Matrix (Config (Qudits ι d)) (Config (Qudits ι d)) ℂ) :
    Matrix (Config (Qudits S d)) (Config (Qudits S d)) ℂ :=
  place (Finset.univ.map f) (X.submatrix (placeAlongEquiv f) (placeAlongEquiv f))

omit [DecidableEq ι] in
/-- The entries of a placement along an injection. -/
theorem placeAlong_apply (f : ι ↪ S) (X : Matrix (Config (Qudits ι d)) (Config (Qudits ι d)) ℂ)
    (σ τ : Config (Qudits S d)) :
    placeAlong f X σ τ = if ∀ v ∉ Finset.univ.map f, σ v = τ v then X (σ ∘ f) (τ ∘ f) else 0 := by
  have h : ∀ ρ : Config (Qudits S d), placeAlongEquiv f (fun v ↦ ρ v) = ρ ∘ f := fun ρ ↦
    funext fun i ↦ by
      rw [placeAlongEquiv, siteConfigurationEquiv_symm_apply]
      rfl
  rw [placeAlong, place_apply, submatrix_apply, h, h]

omit [DecidableEq ι] in
theorem placeAlong_mem_supportedOperators (f : ι ↪ S)
    (X : Matrix (Config (Qudits ι d)) (Config (Qudits ι d)) ℂ) :
    placeAlong f X ∈ supportedOperators (Qudits S d) (Finset.univ.map f) :=
  place_mem_supportedOperators _

theorem placeAlong_mem_unitaryGroup (f : ι ↪ S)
    {X : Matrix (Config (Qudits ι d)) (Config (Qudits ι d)) ℂ}
    (hX : X ∈ unitaryGroup (Config (Qudits ι d)) ℂ) :
    placeAlong f X ∈ unitaryGroup (Config (Qudits S d)) ℂ :=
  place_mem_unitaryGroup (submatrix_equiv_mem_unitary.mpr hX)

omit [DecidableEq ι] in
/-- **Relabelling the sites of a placement.** Conjugating `X` placed along `f` by the permutation
of sites `π` places `X` along `π ∘ f`. -/
theorem sitePermOp_mul_placeAlong_mul (π : Equiv.Perm S) (f : ι ↪ S)
    (X : Matrix (Config (Qudits ι d)) (Config (Qudits ι d)) ℂ) :
    sitePermOp π * placeAlong f X * sitePermOp π⁻¹ = placeAlong (f.trans π.toEmbedding) X := by
  ext σ τ
  rw [← conjTranspose_sitePermOp, sitePermOp_mul_mul_conjTranspose, reindex_apply,
    submatrix_apply]
  have hinv : ∀ ρ : Config (Qudits S d), (siteConfigurationEquiv (X := Qudits S d)
      (X' := Qudits S d) π fun _ ↦ Equiv.refl (Fin d)).symm ρ = ρ ∘ π := fun ρ ↦ by
    rw [Equiv.symm_apply_eq, siteConfigurationEquiv_refl_apply]
    funext v
    exact congrArg ρ (π.apply_symm_apply v).symm
  rw [hinv, hinv, placeAlong_apply, placeAlong_apply]
  refine if_congr ⟨fun h w hw ↦ ?_, fun h v hv ↦ h (π v) ?_⟩ rfl rfl
  · have := h (π.symm w) fun hm ↦ hw ?_
    · rwa [Function.comp_apply, Function.comp_apply, π.apply_symm_apply] at this
    · obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hm
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, by simp [hi]⟩
  · intro hm
    obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hm
    exact hv (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, π.injective (by simpa using hi)⟩)

end PlaceAlong

/-! ### Parallel chains -/

namespace TeleportHop

section Parallel

variable {S : Type} [DecidableEq S] {Γ : Geometry S}

theorem mem_allSites_flatMap {ι : Type*} {l : List ι} {f : ι → List (TeleportHop Γ)}
    {i : S} : i ∈ allSites (l.flatMap f) ↔ ∃ g ∈ l, i ∈ allSites (f g) := by
  simp only [mem_allSites, List.mem_flatMap]
  exact ⟨fun ⟨h, ⟨g, hg, hh⟩, hi⟩ ↦ ⟨g, hg, h, hh, hi⟩,
    fun ⟨g, hg, h, hh, hi⟩ ↦ ⟨h, ⟨g, hg, hh⟩, hi⟩⟩

theorem mem_pairSites_flatMap {ι : Type*} {l : List ι} {f : ι → List (TeleportHop Γ)}
    {i : S} : i ∈ pairSites (l.flatMap f) ↔ ∃ g ∈ l, i ∈ pairSites (f g) := by
  induction l with
  | nil => simp [pairSites]
  | cons g l ih => simp [List.flatMap_cons, pairSites_append, ih]

/-- Two hops with disjoint sites can follow each other in a valid list. -/
theorem after_of_disjoint {h h' : TeleportHop Γ} (hd : Disjoint h.sites h'.sites) :
    After h h' := by
  have hmem : ∀ {i}, i ∈ h.sites → i ∉ h'.sites := fun hi hi' ↦
    Finset.disjoint_left.mp hd hi hi'
  refine ⟨hmem (by simp [sites]), hmem (by simp [sites]), fun he ↦ ?_, fun he ↦ ?_⟩
  · exact hmem (show h.c ∈ h.sites by simp [sites]) (he ▸ by simp [sites])
  · exact hmem (show h.c ∈ h.sites by simp [sites]) (he ▸ by simp [sites])

/-- The sites of a hop of a list are sites of the list. -/
theorem sites_subset_allSites {h : TeleportHop Γ} {hs : List (TeleportHop Γ)} (hh : h ∈ hs) :
    h.sites ⊆ allSites hs :=
  fun _ hi ↦ mem_allSites.mpr ⟨h, hh, hi⟩

/-- **Parallel chains.** Lists of hops whose sites lie in pairwise disjoint sets form a valid
list when concatenated. -/
theorem valid_flatMap {ι : Type*} {l : List ι} {f : ι → List (TeleportHop Γ)}
    {D : ι → Finset S} (hf : ∀ g ∈ l, Valid (f g)) (hD : ∀ g ∈ l, allSites (f g) ⊆ D g)
    (hl : l.Pairwise fun g g' ↦ Disjoint (D g) (D g')) : Valid (l.flatMap f) := by
  rw [valid_iff_pairwise, List.pairwise_flatMap]
  refine ⟨fun g hg ↦ valid_iff_pairwise.mp (hf g hg), ?_⟩
  refine List.Pairwise.imp_of_mem (fun {g g'} hg hg' hd h hh h' hh' ↦ ?_) hl
  exact after_of_disjoint (hd.mono ((sites_subset_allSites hh).trans (hD g hg))
    ((sites_subset_allSites hh').trans (hD g' hg')))

/-- On the set `D g`, the permutation of sites of parallel chains is that of the chain `f g`. -/
theorem sitePerm_flatMap_apply {ι : Type*} {l : List ι} {f : ι → List (TeleportHop Γ)}
    {D : ι → Finset S} (hD : ∀ g ∈ l, allSites (f g) ⊆ D g)
    (hl : l.Pairwise fun g g' ↦ Disjoint (D g) (D g')) {g : ι} (hg : g ∈ l) {i : S}
    (hi : i ∈ D g) : sitePerm (l.flatMap f) i = sitePerm (f g) i := by
  induction l with
  | nil => simp at hg
  | cons g₀ l ih =>
    rw [List.pairwise_cons] at hl
    have hD' : ∀ g ∈ l, allSites (f g) ⊆ D g := fun g hg ↦ hD g (List.mem_cons_of_mem _ hg)
    rw [List.flatMap_cons, sitePerm_append, Equiv.Perm.mul_apply]
    rcases List.mem_cons.mp hg with rfl | hg
    · have hfix : sitePerm (l.flatMap f) i = i := sitePerm_apply_of_notMem fun hi' ↦ by
        obtain ⟨g', hg', hi'⟩ := mem_allSites_flatMap.mp hi'
        exact Finset.disjoint_left.mp (hl.1 g' hg') hi (hD' g' hg' hi')
      rw [hfix]
    · rw [ih hD' hl.2 hg]
      refine sitePerm_apply_of_notMem fun hi' ↦ ?_
      have hmem : sitePerm (f g) i ∈ D g :=
        Equiv.Perm.apply_mem_of_forall_notMem (S := (D g : Set S))
          (fun j hj ↦ sitePerm_apply_of_notMem fun hj' ↦ hj (hD' g hg hj')) hi
      exact Finset.disjoint_left.mp (hl.1 g hg) (hD g₀ List.mem_cons_self hi') hmem

/-- Off the sets `D g`, the permutation of sites of parallel chains is the identity. -/
theorem sitePerm_flatMap_apply_of_notMem {ι : Type*} {l : List ι}
    {f : ι → List (TeleportHop Γ)} {D : ι → Finset S} (hD : ∀ g ∈ l, allSites (f g) ⊆ D g)
    {i : S} (hi : ∀ g ∈ l, i ∉ D g) : sitePerm (l.flatMap f) i = i := by
  refine sitePerm_apply_of_notMem fun hi' ↦ ?_
  obtain ⟨g, hg, hi'⟩ := mem_allSites_flatMap.mp hi'
  exact hi g hg (hD g hg hi')

end Parallel

end TeleportHop

/-! ### Long-range gates -/

variable {d N : ℕ} [NeZero N]

/-- A *long-range gate*: a two-site unitary `u` acting on the sites `a` and `a + 2L + 1` of the
ring, with `2L + 1 < N`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" (isometries acting on
"a constant number of sites which, although spatially separated, can be teleported at
neighboring registers"). -/
structure LongRangeGate (d N : ℕ) [NeZero N] where
  /-- The first site of the gate. -/
  a : Fin N
  /-- The number of hops of the chain from `a` to `a + 2L`. -/
  L : ℕ
  lt : 2 * L + 1 < N
  /-- The two-site unitary, acting on the sites `a` and `a + 2L + 1`. -/
  u : Matrix (Config (Qudits (Fin 2) d)) (Config (Qudits (Fin 2) d)) ℂ
  u_mem_unitaryGroup : u ∈ unitaryGroup (Config (Qudits (Fin 2) d)) ℂ

namespace LongRangeGate

open Fin.NatCast TeleportHop

variable (g : LongRangeGate d N)

/-- The far site `a + 2L + 1` of the gate. -/
def far : Fin N := g.a + ((2 * g.L + 1 : ℕ) : Fin N)

/-- The site `a + 2L` to which the content of `a` is teleported, the left site of the
neighbouring pair `{a + 2L, a + 2L + 1}`. -/
def near : Fin N := g.a + ((2 * g.L : ℕ) : Fin N)

/-- The stretch `a, a + 1, …, a + 2L + 1` of the gate. -/
def span : Finset (Fin N) := (Finset.range (2 * g.L + 2)).image fun j : ℕ ↦ g.a + (j : Fin N)

/-- The `2L` sites `a + 1, …, a + 2L` strictly between the two sites of the gate. -/
def interior : Finset (Fin N) :=
  (Finset.Icc 1 (2 * g.L)).image fun j : ℕ ↦ g.a + (j : Fin N)

/-- The `2L` sites `a, …, a + 2L - 1`, which carry `|0⟩` after the forward chain. -/
def cleared : Finset (Fin N) := (Finset.range (2 * g.L)).image fun j : ℕ ↦ g.a + (j : Fin N)

theorem mem_span {i : Fin N} : i ∈ g.span ↔ ∃ j ≤ 2 * g.L + 1, i = g.a + (j : Fin N) := by
  simp only [span, Finset.mem_image, Finset.mem_range]
  exact ⟨fun ⟨j, hj, h⟩ ↦ ⟨j, by omega, h.symm⟩, fun ⟨j, hj, h⟩ ↦ ⟨j, by omega, h.symm⟩⟩

theorem mem_interior {i : Fin N} :
    i ∈ g.interior ↔ ∃ j, 1 ≤ j ∧ j ≤ 2 * g.L ∧ i = g.a + (j : Fin N) := by
  simp only [interior, Finset.mem_image, Finset.mem_Icc]
  exact ⟨fun ⟨j, hj, h⟩ ↦ ⟨j, hj.1, hj.2, h.symm⟩, fun ⟨j, h1, h2, h⟩ ↦ ⟨j, ⟨h1, h2⟩, h.symm⟩⟩

theorem near_ne_far : g.near ≠ g.far :=
  add_natCast_ne g.a (by have := g.lt; omega) g.lt (by omega)

theorem a_ne_far : g.a ≠ g.far := by
  intro h
  refine add_natCast_ne g.a (j := 0) (k := 2 * g.L + 1) (by have := g.lt; omega) g.lt
    (by omega) ?_
  rw [Nat.cast_zero, add_zero]
  exact h

omit [NeZero N] in
private theorem map_embFinTwo {k k' : Fin N} (h : k ≠ k') :
    Finset.univ.map (Function.Embedding.embFinTwo h) = {k, k'} := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.exists_fin_two,
    Function.Embedding.embFinTwo_apply_zero, Function.Embedding.embFinTwo_apply_one,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The gate on the ring: `u` at the sites `a` and `a + 2L + 1`. -/
noncomputable def op : Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ :=
  placeAlong (Function.Embedding.embFinTwo g.a_ne_far) g.u

/-- The gate `u` on the neighbouring pair `{a + 2L, a + 2L + 1}`. -/
noncomputable def localGate :
    Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ :=
  placeAlong (Function.Embedding.embFinTwo g.near_ne_far) g.u

/-- The forward chain of `L` hops from `a` to `a + 2L`. -/
def there : List (TeleportHop (Geometry.ring N)) := forwardChain g.a g.L (by have := g.lt; omega)

/-- The backward chain of `L` hops from `a + 2L` to `a`. -/
def back : List (TeleportHop (Geometry.ring N)) :=
  backwardChain g.a g.L (by have := g.lt; omega)

theorem localGate_mem_unitaryGroup :
    g.localGate ∈ unitaryGroup (Config (Qudits (Fin N) d)) ℂ :=
  placeAlong_mem_unitaryGroup _ g.u_mem_unitaryGroup

theorem near_add_one : g.near + 1 = g.far := by
  rw [near, far, add_natCast_succ]

theorem localGate_mem_supportedOperators :
    g.localGate ∈ supportedOperators (Qudits (Fin N) d) ((Geometry.ring N).cell g.near) := by
  rw [Geometry.ring_cell, near_add_one, ← map_embFinTwo g.near_ne_far]
  exact placeAlong_mem_supportedOperators _ _

theorem op_mem_unitaryGroup : g.op ∈ unitaryGroup (Config (Qudits (Fin N) d)) ℂ :=
  placeAlong_mem_unitaryGroup _ g.u_mem_unitaryGroup

/-- The gate acts on its two sites `a` and `a + 2L + 1`. -/
theorem op_mem_supportedOperators :
    g.op ∈ supportedOperators (Qudits (Fin N) d) {g.a, g.far} := by
  rw [← map_embFinTwo g.a_ne_far]
  exact placeAlong_mem_supportedOperators _ _

theorem far_mem_span : g.far ∈ g.span :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))

theorem cell_near_subset_span : (Geometry.ring N).cell g.near ⊆ g.span := by
  intro i hmem₀
  rw [Geometry.ring_cell, near_add_one, Finset.mem_insert, Finset.mem_singleton] at hmem₀
  rcases hmem₀ with rfl | rfl
  · exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))
  · exact g.far_mem_span

private theorem image_subset_span {t : Finset ℕ} (ht : ∀ j ∈ t, j < 2 * g.L + 2) :
    t.image (fun j : ℕ ↦ g.a + (j : Fin N)) ⊆ g.span :=
  Finset.image_subset_image fun j hj ↦ Finset.mem_range.mpr (ht j hj)

theorem interior_subset_span : g.interior ⊆ g.span :=
  g.image_subset_span fun j hj ↦ by rw [Finset.mem_Icc] at hj; omega

theorem cleared_subset_span : g.cleared ⊆ g.span :=
  g.image_subset_span fun j hj ↦ by rw [Finset.mem_range] at hj; omega

theorem allSites_there_subset_span : allSites g.there ⊆ g.span :=
  (allSites_forwardChain_subset _ _ _).trans
    (g.image_subset_span fun j hj ↦ by rw [Finset.mem_range] at hj; omega)

theorem allSites_back_subset_span : allSites g.back ⊆ g.span :=
  (allSites_backwardChain_subset _ _ _).trans
    (g.image_subset_span fun j hj ↦ by rw [Finset.mem_range] at hj; omega)

theorem disjoint_cleared_cell_near : Disjoint g.cleared ((Geometry.ring N).cell g.near) := by
  have hL := g.lt
  rw [Finset.disjoint_left]
  intro i hi hi'
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  have hj := Finset.mem_range.mp hj
  rw [Geometry.ring_cell, near_add_one, Finset.mem_insert, Finset.mem_singleton] at hi'
  rcases hi' with hi' | hi'
  · exact add_natCast_ne g.a (by omega) (by omega) (by omega) hi'
  · exact add_natCast_ne g.a (by omega) hL (by omega) hi'

theorem sitePerm_back_near : sitePerm g.back g.near = g.a := by
  rw [back, sitePerm_backwardChain, Equiv.Perm.inv_eq_iff_eq]
  exact (sitePerm_forwardChain _ _ _).1.symm

theorem sitePerm_back_far : sitePerm g.back g.far = g.far := by
  rw [back, sitePerm_backwardChain, Equiv.Perm.inv_eq_iff_eq]
  exact ((sitePerm_forwardChain _ _ _).2 _ (by omega) g.lt).symm

theorem sitePerm_back_sitePerm_there (i : Fin N) :
    sitePerm g.back (sitePerm g.there i) = i := by
  rw [back, sitePerm_backwardChain, there]
  simp

/-! ### Layers of long-range gates -/

variable {g}

section Layer

variable {gs : List (LongRangeGate d N)}
  (hgs : gs.Pairwise fun g g' ↦ Disjoint g.span g'.span)

include hgs in
theorem pairwise_disjoint_cell :
    gs.Pairwise fun g g' ↦
      Disjoint ((Geometry.ring N).cell g.near) ((Geometry.ring N).cell g'.near) :=
  hgs.imp fun {g g'} h ↦ h.mono g.cell_near_subset_span g'.cell_near_subset_span

/-- The layer of the gates `u` on the neighbouring pairs `{a + 2L, a + 2L + 1}`. -/
noncomputable def localLayer :
    Layer (Geometry.ring N) KrausGate (Qudits (Fin N) d) (Qudits (Fin N) d) :=
  Layer.ofList gs near localGate (pairwise_disjoint_cell hgs)
    fun g _ ↦ g.localGate_mem_supportedOperators

theorem kraus_localLayer (i : (localLayer hgs).Index) :
    (localLayer hgs).kraus KrausGate.ev i = (gs.map localGate).prod :=
  Layer.kraus_ofList _ _ _ _
    (fun g _ ↦ by rw [Geometry.ring_cell]; exact Finset.insert_nonempty _ _) _ i

theorem forall_isUnitary_localLayer [NeZero d] :
    (localLayer hgs).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Layer.forall_isUnitary_ofList _ _ _ _ _ fun g _ ↦ g.localGate_mem_unitaryGroup

include hgs in
theorem valid_there : Valid (gs.flatMap there) :=
  valid_flatMap (fun _ _ ↦ valid_forwardChain _ _ _) (fun g _ ↦ g.allSites_there_subset_span)
    hgs

include hgs in
theorem valid_back : Valid (gs.flatMap back) :=
  valid_flatMap (fun _ _ ↦ valid_backwardChain _ _ _) (fun g _ ↦ g.allSites_back_subset_span)
    hgs

variable [NeZero d]

include hgs in
/-- After the forward chains, the sites `a, …, a + 2L - 1` of every gate carry `|0⟩`. -/
theorem isZeroOn_sitePermOp_there {v : Config (Qudits (Fin N) d) → ℂ}
    (hv : ∀ g ∈ gs, IsZeroOn g.interior v) :
    ∀ g ∈ gs, IsZeroOn g.cleared (sitePermOp (sitePerm (gs.flatMap there)) *ᵥ v) := by
  induction gs with
  | nil => simp
  | cons g₀ gs ih =>
    rw [List.pairwise_cons] at hgs
    have hrest : ∀ g ∈ gs, IsZeroOn g.interior v := fun g hg ↦ hv g (List.mem_cons_of_mem _ hg)
    rw [List.flatMap_cons, sitePerm_append, ← sitePermOp_mul, ← mulVec_mulVec]
    have hdisj : ∀ {D : Finset (Fin N)}, D ⊆ g₀.span →
        Disjoint D (allSites (gs.flatMap there)) := by
      intro D hD
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨g, hg, hi'⟩ := mem_allSites_flatMap.mp hi'
      exact Finset.disjoint_left.mp (hgs.1 g hg) (hD hi) (g.allSites_there_subset_span hi')
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · have hw : IsZeroOn g.interior (sitePermOp (sitePerm (gs.flatMap there)) *ᵥ v) :=
        (hv g List.mem_cons_self).sitePermOp_sitePerm_mulVec (hdisj g.interior_subset_span)
      exact isZeroOn_sitePermOp_forwardChain _ _ _ hw
    · refine (ih hgs.2 hrest g hg).sitePermOp_sitePerm_mulVec ?_
      exact (hgs.1 g hg).symm.mono g.cleared_subset_span g₀.allSites_there_subset_span

include hgs in
/-- The gates on the neighbouring pairs keep `|0⟩` at the sites `a, …, a + 2L - 1` of every
gate. -/
theorem isZeroOn_localGates {w : Config (Qudits (Fin N) d) → ℂ}
    (hw : ∀ g ∈ gs, IsZeroOn g.cleared w) :
    ∀ g ∈ gs, IsZeroOn g.cleared ((gs.map localGate).prod *ᵥ w) := by
  have : Std.Symm fun g g' : LongRangeGate d N ↦ Disjoint g.span g'.span :=
    ⟨fun _ _ h ↦ h.symm⟩
  intro g hg
  refine (hw g hg).mulVec_of_mem_supportedOperators disjoint_compl_right
    (list_prod_mem fun A hA ↦ ?_)
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hA
  refine supportedOperators_mono
    (show (Geometry.ring N).cell g'.near ⊆ g.clearedᶜ from
      fun i hi ↦ Finset.mem_compl.mpr fun hi' ↦ ?_)
    g'.localGate_mem_supportedOperators
  by_cases hgg : g = g'
  · subst hgg
    exact Finset.disjoint_left.mp g.disjoint_cleared_cell_near hi' hi
  · exact Finset.disjoint_left.mp (hgs.forall hg hg' hgg) (g.cleared_subset_span hi')
      (g'.cell_near_subset_span hi)

omit [NeZero d] in
include hgs in
/-- The backward chains invert the forward chains. -/
theorem sitePerm_there_eq_symm :
    sitePerm (gs.flatMap there) = (sitePerm (gs.flatMap back)).symm := by
  refine Equiv.ext fun i ↦ ?_
  rw [Equiv.eq_symm_apply]
  by_cases hi : ∃ g ∈ gs, i ∈ g.span
  · obtain ⟨g, hg, hi⟩ := hi
    have hmem : sitePerm g.there i ∈ g.span :=
      Equiv.Perm.apply_mem_of_forall_notMem (S := (g.span : Set (Fin N)))
        (fun j hj ↦ sitePerm_apply_of_notMem fun hj' ↦ hj (g.allSites_there_subset_span hj')) hi
    rw [sitePerm_flatMap_apply (fun g _ ↦ g.allSites_there_subset_span) hgs hg hi,
      sitePerm_flatMap_apply (fun g _ ↦ g.allSites_back_subset_span) hgs hg hmem,
      sitePerm_back_sitePerm_there]
  · simp only [not_exists, not_and] at hi
    rw [sitePerm_flatMap_apply_of_notMem (fun g _ ↦ g.allSites_there_subset_span) hi,
      sitePerm_flatMap_apply_of_notMem (fun g _ ↦ g.allSites_back_subset_span) hi]

omit [NeZero d] in
include hgs in
/-- **The layer conjugated by the chains.** The backward chains, the gates on the neighbouring
pairs, and the forward chains compose to the product of the long-range gates. -/
theorem sitePermOp_back_mul_localGates_mul_sitePermOp_there :
    sitePermOp (sitePerm (gs.flatMap back)) * (gs.map localGate).prod *
        sitePermOp (sitePerm (gs.flatMap there)) = (gs.map op).prod := by
  set σ := sitePerm (gs.flatMap back)
  have hPQ : sitePermOp (α := Fin d) σ * sitePermOp σ⁻¹ = 1 := by
    rw [sitePermOp_mul, mul_inv_cancel, sitePermOp_one]
  have hQP : sitePermOp (α := Fin d) σ⁻¹ * sitePermOp σ = 1 := by
    rw [sitePermOp_mul, inv_mul_cancel, sitePermOp_one]
  rw [sitePerm_there_eq_symm hgs, show σ.symm = σ⁻¹ from rfl,
    List.mul_prod_mul_of_mul_eq_one hQP hPQ, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun g hg ↦ ?_)
  rw [Function.comp_apply, localGate, sitePermOp_mul_placeAlong_mul, op]
  have hback : ∀ {i}, i ∈ g.span → σ i = sitePerm g.back i := fun hi ↦
    sitePerm_flatMap_apply (fun g _ ↦ g.allSites_back_subset_span) hgs hg hi
  have hσ : ∀ t, ((Function.Embedding.embFinTwo g.near_ne_far).trans (Equiv.toEmbedding σ)) t =
      Function.Embedding.embFinTwo g.a_ne_far t := by
    intro t
    fin_cases t
    · change σ g.near = g.a
      rw [hback (g.cell_near_subset_span (by rw [Geometry.ring_cell]; simp)), sitePerm_back_near]
    · change σ g.far = g.far
      rw [hback g.far_mem_span, sitePerm_back_far]
  rw [Function.Embedding.ext hσ]

/-- The two teleportation rounds applying a layer of long-range gates: teleport the content of
the site `a` of every gate along its forward chain to `a + 2L`; then apply the gates `u` to the
neighbouring pairs `{a + 2L, a + 2L + 1}` and teleport the content of every `a + 2L` back to `a`
along the backward chains.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
noncomputable def rounds :
    Circuit (Geometry.ring N) KrausGate (Qudits (Fin N) d) (Qudits (Fin N) d) :=
  (round (UnitaryCircuit.id _ _) (gs.flatMap there) (valid_there hgs)).comp
    (round (UnitaryCircuit.ofLayer (localLayer hgs) (forall_isUnitary_localLayer hgs))
      (gs.flatMap back) (valid_back hgs))

/-- The two rounds have depth at most `5`, whatever the distances and the number of gates. -/
theorem depth_rounds_le : (rounds (d := d) hgs).depth ≤ 5 := by
  refine (Circuit.depth_comp _ _).trans ?_
  have h₁ := depth_round_id_le (d := d) (gs.flatMap there) (valid_there hgs)
  have h₂ := depth_round_le (UnitaryCircuit.ofLayer (localLayer (d := d) hgs)
    (forall_isUnitary_localLayer hgs)) (gs.flatMap back) (valid_back hgs)
  rw [UnitaryCircuit.depth_ofLayer] at h₂
  have := Layer.depth_le_one (localLayer (d := d) hgs)
  omega

/-- The two rounds form a measurement circuit. -/
theorem forall_rounds :
    (rounds (d := d) hgs).Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement :=
  (forall_round _ _ _).comp _ (forall_round _ _ _)

/-- **A layer of long-range gates in constant depth with measurements.** For long-range gates
on pairwise disjoint stretches, the two rounds `rounds`, of depth at most `5`, implement the
product of the gates on the vectors with `|0⟩` at the `2L` sites strictly between the two sites
of every gate: whatever the outcomes, every output is a scalar multiple of the product of the
gates `u` at the sites `a`, `a + 2L + 1` applied to the input. No outcome is post-selected.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("Isometries ... act on
a constant number of sites which, although spatially separated, can be teleported at
neighboring registers with a constant overhead ... Therefore every isometry ... takes constant
time using measurement"). -/
theorem isImplementationOn_rounds :
    (rounds (d := d) hgs).IsImplementationOn KrausGate.ev
      {v | ∀ g ∈ gs, IsZeroOn g.interior v} (gs.map op).prod := by
  have hop : (UnitaryCircuit.ofLayer (localLayer (d := d) hgs)
      (forall_isUnitary_localLayer hgs)).op = (gs.map localGate).prod := by
    obtain ⟨i⟩ := (Layer.nonempty_unique_index_of_forall_isUnitary
      (forall_isUnitary_localLayer (d := d) hgs)).map fun u ↦ u.default
    rw [UnitaryCircuit.op_ofLayer _ _ i, kraus_localLayer]
  have h := isImplementationOn_round_comp_round (valid_there hgs) (valid_back hgs)
    (UnitaryCircuit.ofLayer (localLayer (d := d) hgs) (forall_isUnitary_localLayer hgs))
  rw [hop, sitePermOp_back_mul_localGates_mul_sitePermOp_there hgs] at h
  refine h.mono fun v hv ↦ ⟨fun x hx i hi ↦ ?_, fun x hx i hi ↦ ?_⟩
  · obtain ⟨g, hg, hi⟩ := mem_pairSites_flatMap.mp hi
    exact hv g hg x hx i (pairSites_forwardChain_subset _ _ _ hi)
  · obtain ⟨g, hg, hi⟩ := mem_pairSites_flatMap.mp hi
    exact isZeroOn_localGates hgs (isZeroOn_sitePermOp_there hgs hv) g hg x hx i
      (pairSites_backwardChain_subset _ _ _ hi)

end Layer

end LongRangeGate

end QuantumCircuit
