/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Chain
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Sort

/-!
# Finite domains of the integers

The sites of a finite set `Λ ⊂ ℤ` are labelled `0, …, |Λ| - 1` in increasing order, so site
`i : Fin Λ.card` sits at the integer `sitePos Λ i`. Two sites are adjacent in the induced path
graph when their positions are consecutive integers. A support of range `R` is a nonempty set
of sites of diameter at most `R` in this graph; it is a support of range `R` of the chain of
`|Λ|` sites, and it does not straddle a gap of `Λ`.

Moved from TNLean, `TNLean/MPS/AreaLaw/ComponentReduction.lean` (section `Domain`, up to
`IsDomainSupport.subset_or_disjoint_of_gap`) at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`. Changes: namespace `ManyBody`
in place of `TNLean.MPS.AreaLaw`; `domainGraph` is renamed `lineDomainGraph`, to distinguish it
from the induced graph `planeDomainGraph` of a domain of `ℤ × ℤ`.

## Main definitions

* `ManyBody.sitePos` — the increasing labelling of a finite set of integers.
* `ManyBody.lineDomainGraph` — the induced path graph on the sites.
* `ManyBody.IsDomainSupport`, `ManyBody.DomainSupport` — the supports of range `R`.

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

end ManyBody
