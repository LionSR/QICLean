/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import QICLean.ManyBody.Sites.Lattice.ChainCut
import QICLean.ManyBody.Sites.GraphBall
import QICLean.Algebra.Combinatorics.IntegerHasseGraph
import QICLean.Algebra.Combinatorics.GraphDistanceTransport
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Finite domains of the integers

The sites of a finite set `Λ ⊂ ℤ` are labelled `0, …, |Λ| - 1` in increasing order, so site
`i : Fin Λ.card` sits at the integer `sitePos Λ i`. Two sites are adjacent in the induced path
graph when their positions are consecutive integers. A support of range `R` is a nonempty set
of sites of diameter at most `R` in this graph; it is a support of range `R` of the chain of
`|Λ|` sites, and it does not straddle a gap of `Λ`.

Restricting the counting of the chain of `|Λ|` sites, at most `2^{2R} |∂D|` supports of range
`R` cross a region `D`, as on the chain. The increasing labelling identifies the induced path
graph with the Hasse graph of `ℤ` induced on `Λ`; each connected component is a finite path,
so every sphere of finite radius has at most two sites, even when `Λ` is disconnected. Each
edge of the graph joins consecutive labels, so a walk visits every label between its endpoints;
hence the graph neighborhood of an order-connected set of sites is a set of consecutive labels.
No comparison between the graph distance and the distance between labels is used, and a ball
does not cross a missing edge.

Moved from TNLean, `TNLean/MPS/AreaLaw/ComponentReduction.lean` (section `Domain`, up to
`IsDomainSupport.subset_or_disjoint_of_gap`) at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`.
Changes: namespace `ManyBody` in place of `TNLean.MPS.AreaLaw`; `domainGraph` is renamed
`lineDomainGraph`, to distinguish it from the induced graph `planeDomainGraph` of a domain of `ℤ ×
ℤ`.

## Main definitions

* `ManyBody.sitePos` — the increasing labelling of a finite set of integers.
* `ManyBody.lineDomainGraph` — the induced path graph on the sites.
* `ManyBody.IsDomainSupport`, `ManyBody.DomainSupport` — the supports of range `R`.
* `ManyBody.lineDomainGraphIsoHasse` — the induced path graph as the induced Hasse graph.

## Main results

* `ManyBody.card_domain_crossingTerms_le_mul_card_boundaryEdges`,
  `ManyBody.card_domain_crossingTerms_mul_two_le` — the supports crossing a region.
* `ManyBody.lineDomainGraph_card_sphere_le_two` — every sphere has at most two sites.
* `ManyBody.domainNeighborhood_eq_interval_of_ordConnected`,
  `ManyBody.domainNeighborhood_interval_eq` — neighborhoods of intervals are intervals.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, `part0_preamble.tex`, the setting and `eq:ham`.
-/

namespace ManyBody

variable {Λ : Finset ℤ} {R : ℕ}


/-- The sites of a finite set `Λ ⊂ ℤ`, labelled `0, …, |Λ| - 1` in increasing order: site `i`
sits at the integer `sitePos Λ i`. TNLean note, `part0_preamble.tex`, the setting
(`ℋ_Λ = ⊗_{x ∈ Λ} ℂ^q`). -/
noncomputable def sitePos (Λ : Finset ℤ) : Fin Λ.card ↪o ℤ :=
  Λ.orderEmbOfFin rfl

/-- Every site sits at a point of `Λ`. -/
theorem sitePos_mem (i : Fin Λ.card) : sitePos Λ i ∈ Λ :=
  Finset.orderEmbOfFin_mem Λ rfl i

/-- Every point of `Λ` is the position of a site. -/
theorem exists_sitePos_eq {x : ℤ} (hx : x ∈ Λ) : ∃ i, sitePos Λ i = x := by
  have : x ∈ Set.range (sitePos Λ) := by
    rw [sitePos, Finset.range_orderEmbOfFin]
    exact hx
  exact this

/-- Positions grow at least as fast as labels: `j - i ≤ x_j - x_i` for `i ≤ j`. -/
theorem sub_le_sitePos_sub {i j : Fin Λ.card} (hij : i ≤ j) :
    (j.val : ℤ) - i.val ≤ sitePos Λ j - sitePos Λ i := by
  have hij' : i.val ≤ j.val := hij
  obtain ⟨k, hk⟩ : ∃ k, j.val = i.val + k := ⟨j.val - i.val, by omega⟩
  induction k generalizing j with
  | zero =>
    have : j = i := Fin.ext (by omega)
    subst this
    simp
  | succ k ih =>
    have hlt : i.val + k < Λ.card := by have := j.2; omega
    have h1 := ih (j := ⟨i.val + k, hlt⟩) (Fin.mk_le_mk.mpr (by omega)) (by simp) rfl
    have h2 : sitePos Λ ⟨i.val + k, hlt⟩ < sitePos Λ j :=
      (sitePos Λ).strictMono (Fin.mk_lt_of_lt_val (by omega))
    simp only at h1
    push_cast [hk] at h1 ⊢
    omega

/-- Two sites at consecutive integers have consecutive labels. -/
theorem val_eq_add_one_of_sitePos_eq_add_one {i j : Fin Λ.card}
    (h : sitePos Λ j = sitePos Λ i + 1) : j.val = i.val + 1 := by
  have hlt : i < j := (sitePos Λ).lt_iff_lt.mp (by omega)
  have := sub_le_sitePos_sub hlt.le
  have : i.val < j.val := hlt
  omega

/-- The induced path graph of `Λ` on its sites: two sites are adjacent when their positions
are consecutive integers. TNLean note, `part0_preamble.tex`, the setting. -/
def lineDomainGraph (Λ : Finset ℤ) : SimpleGraph (Fin Λ.card) where
  Adj i j := sitePos Λ j = sitePos Λ i + 1 ∨ sitePos Λ i = sitePos Λ j + 1
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun _ h ↦ by rcases h with h | h <;> omega⟩

/-- Along a walk of the induced path graph, position minus label is constant, and the
labels move by at most the length of the walk. -/
theorem sitePos_sub_val_of_walk {i j : Fin Λ.card} (w : (lineDomainGraph Λ).Walk i j) :
    sitePos Λ j - j.val = sitePos Λ i - i.val ∧ (j.val : ℤ) - i.val ≤ w.length ∧
      (i.val : ℤ) - j.val ≤ w.length := by
  induction w with
  | nil => simp
  | cons h p ih =>
    have h' : sitePos Λ _ = sitePos Λ _ + 1 ∨ sitePos Λ _ = sitePos Λ _ + 1 := h
    rcases h' with h' | h'
    · have := val_eq_add_one_of_sitePos_eq_add_one h'
      simp only [SimpleGraph.Walk.length_cons]
      push_cast
      omega
    · have := val_eq_add_one_of_sitePos_eq_add_one h'
      simp only [SimpleGraph.Walk.length_cons]
      push_cast
      omega

/-- A support of range `R` in `Λ`: a nonempty set of sites of diameter at most `R` in the
graph distance of the induced path graph. TNLean note, `part0_preamble.tex`, `eq:ham`. -/
def IsDomainSupport (Λ : Finset ℤ) (R : ℕ) (X : Finset (Fin Λ.card)) : Prop :=
  X.Nonempty ∧ ∀ i ∈ X, ∀ j ∈ X, (lineDomainGraph Λ).edist i j ≤ R

noncomputable instance (Λ : Finset ℤ) (R : ℕ) : DecidablePred (IsDomainSupport Λ R) :=
  Classical.decPred _

/-- The supports of range `R` in `Λ`. -/
abbrev DomainSupport (Λ : Finset ℤ) (R : ℕ) := {X : Finset (Fin Λ.card) // IsDomainSupport Λ R X}

/-- Two sites of a support of range `R` are joined by a walk of length at most `R`. -/
theorem IsDomainSupport.exists_walk {X : Finset (Fin Λ.card)} (hX : IsDomainSupport Λ R X)
    {i j : Fin Λ.card} (hi : i ∈ X) (hj : j ∈ X) :
    ∃ w : (lineDomainGraph Λ).Walk i j, w.length ≤ R := by
  have h := hX.2 i hi j hj
  have hne : (lineDomainGraph Λ).edist i j ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top R) h
  obtain ⟨w, hw⟩ := SimpleGraph.exists_walk_of_edist_ne_top hne
  exact ⟨w, by rw [← hw] at h; exact_mod_cast h⟩

/-- A support of range `R` in `Λ` is a support of range `R` of the chain of `|Λ|` sites. -/
theorem IsDomainSupport.isChainSupport {X : Finset (Fin Λ.card)} (hX : IsDomainSupport Λ R X) :
    IsChainSupport Λ.card R X := by
  refine ⟨hX.1, fun i hi j hj ↦ ?_⟩
  obtain ⟨w, hw⟩ := hX.exists_walk hi hj
  have := (sitePos_sub_val_of_walk w).2.1
  have : (w.length : ℤ) ≤ R := by exact_mod_cast hw
  omega

/-- Regard an admissible domain support as a chain support on the same labelled
sites. Source: TNLean note, part0_preamble.tex, eq:ham, lines 191–201. -/
def DomainSupport.toChainSupport (X : DomainSupport Λ R) : ChainSupport Λ.card R :=
  ⟨X.1, X.2.isChainSupport⟩

/-- Increasing labels do not identify distinct interaction supports.
Source: TNLean note, part0_preamble.tex, eq:ham, lines 191–201. -/
theorem DomainSupport.toChainSupport_injective :
    Function.Injective (DomainSupport.toChainSupport (Λ := Λ) (R := R)) := by
  exact fun X Y h ↦ Subtype.ext (congrArg (fun Z : ChainSupport Λ.card R ↦ Z.1) h)

/-- A support of range `R` does not straddle a gap of `Λ`: if the sites `p` and `p + 1` are
not at consecutive integers, every support lies in the prefix `[0, p + 1)` or avoids it. -/
theorem IsDomainSupport.subset_or_disjoint_of_gap {X : Finset (Fin Λ.card)}
    (hX : IsDomainSupport Λ R X) {p : ℕ} (hp : p + 1 < Λ.card)
    (hgap : sitePos Λ ⟨p + 1, hp⟩ ≠ sitePos Λ ⟨p, by omega⟩ + 1) :
    X ⊆ interval Λ.card 0 (p + 1) ∨ Disjoint X (interval Λ.card 0 (p + 1)) := by
  by_cases hsub : X ⊆ interval Λ.card 0 (p + 1)
  · exact Or.inl hsub
  refine Or.inr (Finset.disjoint_right.mpr fun i hiP hiX ↦ ?_)
  obtain ⟨j, hjX, hjP⟩ := Finset.not_subset.mp hsub
  rw [mem_interval] at hiP hjP
  obtain ⟨w, -⟩ := hX.exists_walk hiX hjX
  have hφ := (sitePos_sub_val_of_walk w).1
  have h1 := sub_le_sitePos_sub (i := i) (j := ⟨p, by omega⟩)
    (Fin.le_iff_val_le_val.mpr (by dsimp only; omega))
  have h2 := sub_le_sitePos_sub (i := ⟨p + 1, hp⟩) (j := j)
    (Fin.le_iff_val_le_val.mpr (by dsimp only; omega))
  have h3 : sitePos Λ ⟨p, by omega⟩ < sitePos Λ ⟨p + 1, hp⟩ :=
    (sitePos Λ).strictMono (Fin.mk_lt_mk.mpr (by omega))
  simp only at h1 h2
  omega

/-- A single site is a support of every range. -/
theorem IsDomainSupport.singleton (x : Fin Λ.card) : IsDomainSupport Λ R {x} := by
  simp [IsDomainSupport]

/-- The supports of range `R` of `Λ` crossing a region `D` inject into the supports of the
chain of `|Λ|` sites crossing it, so at most `2^{2R} |∂D|` of them cross it, with `∂D` the
boundary of `D` in the chain. -/
theorem card_domain_crossingTerms_le_mul_card_boundaryEdges (Λ : Finset ℤ) (R : ℕ)
    (D : Finset (Fin Λ.card)) :
    (crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D).card ≤
      2 ^ (2 * R) * (boundaryEdges Λ.card D).card := by
  refine (Finset.card_le_card_of_injOn
    DomainSupport.toChainSupport ?_
    DomainSupport.toChainSupport_injective.injOn).trans
      (card_crossingTerms_le_mul_card_boundaryEdges Λ.card R D)
  exact fun X hX ↦ by
    simpa only [crossingTerms, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, DomainSupport.toChainSupport] using hX

/-- Twice the number of supports of range `R` crossing a region is at most `N_R |Λ|`, with
`N_R = chainCrossConst R`. -/
theorem card_domain_crossingTerms_mul_two_le (Λ : Finset ℤ) (R : ℕ)
    (D : Finset (Fin Λ.card)) :
    (crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D).card * 2 ≤
      chainCrossConst R * Λ.card := by
  have hb : (boundaryEdges Λ.card D).card ≤ Λ.card :=
    (Finset.card_le_card fun p hp ↦ Finset.mem_range.mpr
      (by have := (mem_boundaryEdges.mp hp).1; omega)).trans (Finset.card_range _).le
  simpa only [chainCrossConst, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    Nat.mul_le_mul_right 2
      ((card_domain_crossingTerms_le_mul_card_boundaryEdges Λ R D).trans
        (Nat.mul_le_mul_left (2 ^ (2 * R)) hb))

/-! ### Spheres -/

/-- The increasing labelling identifies the induced path graph of `Λ` with the Hasse graph of
`ℤ` induced on `Λ`. -/
noncomputable def lineDomainGraphIsoHasse (Λ : Finset ℤ) :
    lineDomainGraph Λ ≃g (SimpleGraph.hasse ℤ).induce (Λ : Set ℤ) where
  toEquiv := (Λ.orderIsoOfFin rfl).toEquiv
  map_rel_iff' := by
    intro i j
    change (sitePos Λ i ⋖ sitePos Λ j ∨ sitePos Λ j ⋖ sitePos Λ i) ↔ _
    simp only [Order.covBy_iff_add_one_eq, lineDomainGraph, eq_comm]

/-- Every sphere of finite radius in the induced path graph of `Λ` has at most two sites: the
connected component of the center is a finite path. -/
theorem lineDomainGraph_card_sphere_le_two (Λ : Finset ℤ) (x : Fin Λ.card) (d : ℕ) :
    (Finset.univ.filter (fun y ↦ (lineDomainGraph Λ).edist x y = (d : ℕ∞))).card ≤ 2 := by
  classical
  let e := lineDomainGraphIsoHasse Λ
  let C := ((SimpleGraph.hasse ℤ).induce (Λ : Set ℤ)).connectedComponentMk (e x)
  let xC : C := ⟨e x, rfl⟩
  obtain ⟨φ⟩ := C.nonempty_pathGraph_iso_hasse_int_induce_finset Λ
  have hyC (y : Fin Λ.card) (hy : (lineDomainGraph Λ).edist x y = (d : ℕ∞)) :
      e y ∈ C.supp := by
    exact (C.mem_supp_iff _).mpr (SimpleGraph.ConnectedComponent.sound
      ((SimpleGraph.reachable_of_edist_ne_top
        (hy.trans_ne (ENat.natCast_ne_top d))).map e.toHom).symm)
  let f : (Finset.univ.filter (fun y ↦ (lineDomainGraph Λ).edist x y = (d : ℕ∞))) →
      (Finset.univ.filter (fun z ↦
        (SimpleGraph.pathGraph (Nat.card C)).edist (φ.symm xC) z = (d : ℕ∞))) :=
    fun y ↦ ⟨φ.symm ⟨e y.val, hyC y.val (Finset.mem_filter.mp y.property).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (φ.symm.edist_eq xC _).trans ((C.edist_eq xC _).trans
          ((e.edist_eq x y.val).trans (Finset.mem_filter.mp y.property).2))⟩⟩
  have hf : Function.Injective f := fun u v huv ↦
    Subtype.ext (e.injective (congrArg Subtype.val
      (φ.symm.injective (congrArg Subtype.val huv))))
  exact (Finset.card_le_card_of_injective hf).trans
    (SimpleGraph.pathGraph_card_sphere_le_two (Nat.card C) (φ.symm xC) d)

/-! ### Neighborhoods of intervals -/

open SimpleGraph

/-- A walk of the induced path graph visits every label between its endpoints. -/
private theorem mem_support_of_between {i j : Fin Λ.card} (p : (lineDomainGraph Λ).Walk i j) :
    ∀ k : Fin Λ.card, min i j ≤ k → k ≤ max i j → k ∈ p.support := by
  induction p with
  | nil => grind [Walk.support_nil]
  | @cons u v w h p ih =>
    intro k hk₁ hk₂
    have hstep : v.val = u.val + 1 ∨ u.val = v.val + 1 :=
      h.elim (fun e ↦ Or.inl (val_eq_add_one_of_sitePos_eq_add_one e))
        (fun e ↦ Or.inr (val_eq_add_one_of_sitePos_eq_add_one e))
    grind [Walk.support_cons, Fin.le_def, Fin.ext_iff]

/-- A label between two sites at graph distance at most `m` is itself within graph distance `m`
of the first site. -/
private theorem edist_le_of_between {i j k : Fin Λ.card}
    (m : ℕ) (hij : (lineDomainGraph Λ).edist i j ≤ (m : ℕ∞))
    (hk₁ : min i j ≤ k) (hk₂ : k ≤ max i j) :
    (lineDomainGraph Λ).edist i k ≤ (m : ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top
    (ne_top_of_le_ne_top (ENat.natCast_ne_top m) hij)
  exact (p.takeUntil k (mem_support_of_between p k hk₁ hk₂)).edist_le.trans
    ((ENat.natCast_le_natCast.mpr (p.length_takeUntil_le_length _)).trans
      (by simpa only [hp] using hij))

/-- The union of graph balls of radius `m` about an order-connected set of centers is
order-connected. -/
private theorem neighborhood_between (I : Finset (Fin Λ.card))
    (hI : Set.OrdConnected (I : Set (Fin Λ.card)))
    (m : ℕ) {u v z : Fin Λ.card}
    (hu : u ∈ I.biUnion (fun a ↦ graphBall (lineDomainGraph Λ) a m))
    (hv : v ∈ I.biUnion (fun a ↦ graphBall (lineDomainGraph Λ) a m))
    (huz : u ≤ z) (hzv : z ≤ v) :
    z ∈ I.biUnion (fun a ↦ graphBall (lineDomainGraph Λ) a m) := by
  obtain ⟨a, ha, hau⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨b, hb, hbv⟩ := Finset.mem_biUnion.mp hv
  by_cases haz : a ≤ z
  · by_cases hzb : z ≤ b
    · exact Finset.mem_biUnion.mpr ⟨z, hI.out ha hb ⟨haz, hzb⟩,
        mem_graphBall.mpr (by simp)⟩
    · exact Finset.mem_biUnion.mpr ⟨b, hb, mem_graphBall.mpr
        (edist_le_of_between m (mem_graphBall.mp hbv)
          ((min_le_left b v).trans (le_of_lt (lt_of_not_ge hzb)))
          (hzv.trans (le_max_right b v)))⟩
  · exact Finset.mem_biUnion.mpr ⟨a, ha, mem_graphBall.mpr
      (edist_le_of_between m (mem_graphBall.mp hau) ((min_le_right a u).trans huz)
        ((le_of_lt (lt_of_not_ge haz)).trans (le_max_left a u)))⟩

/-- The graph neighborhood of radius `m` of an order-connected set of sites of `Λ` is a set of
consecutive labels. -/
theorem domainNeighborhood_eq_interval_of_ordConnected (Λ : Finset ℤ)
    (I : Finset (Fin Λ.card))
    (hI : Set.OrdConnected (I : Set (Fin Λ.card))) (m : ℕ) :
    ∃ a b : ℕ, I.biUnion (fun x ↦ graphBall (lineDomainGraph Λ) x m) =
      interval Λ.card a b := by
  by_cases hN : (I.biUnion (fun x ↦ graphBall (lineDomainGraph Λ) x m)).Nonempty
  · exact (let N := I.biUnion (fun x ↦ graphBall (lineDomainGraph Λ) x m)
      ⟨(N.min' hN).val, (N.max' hN).val + 1,
        Finset.ext fun z ↦
          (show z ∈ N ↔ (N.min' hN).val ≤ z.val ∧ z.val < (N.max' hN).val + 1 from
            ⟨fun hz ↦ ⟨Finset.min'_le N z hz,
                Nat.lt_succ_of_le (Finset.le_max' N z hz)⟩,
              fun hz ↦ neighborhood_between I hI m (Finset.min'_mem N hN)
                (Finset.max'_mem N hN) hz.1 (Nat.le_of_lt_succ hz.2)⟩).trans
            mem_interval.symm⟩)
  · exact ⟨0, 0, (Finset.not_nonempty_iff_eq_empty.mp hN).trans (by simp [interval])⟩

/-- The graph neighborhood of radius `m` of a set of consecutive labels of `Λ` is a set of
consecutive labels. -/
theorem domainNeighborhood_interval_eq (Λ : Finset ℤ) (a b m : ℕ) :
    ∃ a' b' : ℕ,
      (interval Λ.card a b).biUnion
        (fun x ↦ graphBall (lineDomainGraph Λ) x m) = interval Λ.card a' b' := by
  exact domainNeighborhood_eq_interval_of_ordConnected Λ (interval Λ.card a b)
    ⟨fun u hu v hv z hz ↦ mem_interval.mpr
      ⟨(mem_interval.mp hu).1.trans (show u.val ≤ z.val from hz.1),
        (show z.val ≤ v.val from hz.2).trans_lt (mem_interval.mp hv).2⟩⟩ m

section Toggle

open scoped symmDiff

variable {L : ℕ}

/-- Position membership in a region of the chain, for an in-range position. -/
theorem exists_mem_val_eq_iff {A : Finset (Fin L)} {r : ℕ} (hr : r < L) :
    (∃ i ∈ A, i.val = r) ↔ (⟨r, hr⟩ : Fin L) ∈ A := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro h
    exact ⟨_, h, rfl⟩

/-- **Flipping a prefix toggles one boundary edge.** Replacing the region `A` by its
symmetric difference with the prefix `[0, p + 1)` of the chain changes its set of boundary
edges exactly at the edge `p`. -/
theorem boundaryEdges_symmDiff_interval {A : Finset (Fin L)} {p : ℕ} (hp : p + 1 < L) :
    boundaryEdges L (A ∆ interval L 0 (p + 1)) = boundaryEdges L A ∆ {p} := by
  ext r
  rw [Finset.mem_symmDiff, mem_boundaryEdges, mem_boundaryEdges, Finset.mem_singleton]
  by_cases hr : r + 1 < L
  · rw [exists_mem_val_eq_iff (by omega), exists_mem_val_eq_iff hr,
      exists_mem_val_eq_iff (A := A) (by omega), exists_mem_val_eq_iff (A := A) hr]
    simp only [Finset.mem_symmDiff, mem_interval]
    rcases lt_trichotomy r p with h | h | h
    · have h1 : r < p + 1 := by omega
      have h2 : r + 1 < p + 1 := by omega
      simp only [zero_le, true_and, h1, h2, not_true_eq_false, and_false, false_or, hr,
        h.ne, not_false_eq_true]
      tauto
    · subst h
      simp only [zero_le, true_and, lt_add_iff_pos_right, Nat.lt_irrefl, not_true_eq_false,
        and_false, hr, not_false_eq_true, and_true, Nat.lt_add_one]
      tauto
    · have h1 : ¬ r < p + 1 := by omega
      have h2 : ¬ r + 1 < p + 1 := by omega
      simp only [zero_le, true_and, h1, h2, not_false_eq_true, and_true, or_false, hr,
        h.ne', false_and]
  · have : r ≠ p := by omega
    simp [hr, this]

end Toggle

/-- The edge boundary `∂_Λ A`: the edges `{x, x + 1} ⊆ Λ` with exactly one end in `A`, each
recorded by its left end `x`. TNLean note, `part0_preamble.tex`, the setting. -/
def domainBoundaryEdges (Λ A : Finset ℤ) : Finset ℤ :=
  Λ.filter fun x ↦ x + 1 ∈ Λ ∧ ¬ (x ∈ A ↔ x + 1 ∈ A)

/-- The sites of `Λ` whose positions lie in `A`. -/
noncomputable def domainRegion (Λ A : Finset ℤ) : Finset (Fin Λ.card) :=
  Finset.univ.filter fun i ↦ sitePos Λ i ∈ A

/-- The edge `p` of the chain of `|Λ|` sites joins sites at consecutive integers. -/
def IsDomainEdge (Λ : Finset ℤ) (p : ℕ) : Prop :=
  ∃ hp : p + 1 < Λ.card, sitePos Λ ⟨p + 1, hp⟩ = sitePos Λ ⟨p, by omega⟩ + 1

/-- The boundary edges of `A` in `Λ` correspond to the boundary edges of its sites on the
chain of `|Λ|` sites that join sites at consecutive integers. -/
theorem card_domainBoundaryEdges [DecidablePred (IsDomainEdge Λ)] (A : Finset ℤ) :
    ((boundaryEdges Λ.card (domainRegion Λ A)).filter (IsDomainEdge Λ)).card =
      (domainBoundaryEdges Λ A).card := by
  have hmem : ∀ {r : ℕ} (hr : r < Λ.card),
      (∃ i ∈ domainRegion Λ A, i.val = r) ↔ sitePos Λ ⟨r, hr⟩ ∈ A := fun hr ↦ by
    rw [exists_mem_val_eq_iff hr, domainRegion, Finset.mem_filter]
    simp
  refine Finset.card_bij (fun p hp ↦ sitePos Λ ⟨p, ?_⟩) ?_ ?_ ?_
  · have := (mem_boundaryEdges.mp (Finset.mem_filter.mp hp).1).1
    omega
  · intro p hp
    obtain ⟨hpb, hp1, hcons⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpL, hpA⟩ := mem_boundaryEdges.mp hpb
    rw [hmem (by omega), hmem hpL, hcons] at hpA
    rw [domainBoundaryEdges, Finset.mem_filter]
    refine ⟨sitePos_mem _, ?_, hpA⟩
    rw [← hcons]
    exact sitePos_mem _
  · intro p hp p' hp' h
    have := (sitePos Λ).injective h
    simpa using this
  · intro x hx
    rw [domainBoundaryEdges, Finset.mem_filter] at hx
    obtain ⟨hxΛ, hx1, hxA⟩ := hx
    obtain ⟨i, rfl⟩ := exists_sitePos_eq hxΛ
    obtain ⟨j, hj⟩ := exists_sitePos_eq hx1
    have hji := val_eq_add_one_of_sitePos_eq_add_one hj
    have hpL : i.val + 1 < Λ.card := hji ▸ j.2
    have hjeq : j = ⟨i.val + 1, hpL⟩ := Fin.ext hji
    subst hjeq
    refine ⟨i.val, Finset.mem_filter.mpr ⟨mem_boundaryEdges.mpr ⟨hpL, ?_⟩, hpL, hj⟩, rfl⟩
    rw [hmem (by omega), hmem hpL, hj]
    exact hxA

end ManyBody
