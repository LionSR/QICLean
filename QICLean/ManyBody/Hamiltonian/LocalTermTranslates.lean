/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Combinatorics.FinSum
import QICLean.ManyBody.Hamiltonian.FrustrationFree
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.Spectral.Gap.FiniteRangeKnabe

/-!
# Translates of one local matrix on the ring and on the open chain

For a matrix `h` on `R` consecutive sites, `ManyBody.Interaction.translationInvariant N h` has
the translates of `h` around the ring of `N` sites as its terms, and
`ManyBody.Interaction.chainTranslates R N h` the translates along the windows of the open chain
that do not cross its right end. This file collects their dependence on `h` (additivity,
homogeneity, order, positivity and continuity), the comparison of the two families, and the
geometric facts used by the finite-range Knabe argument: separated windows on the ring commute,
and consecutive terms on the ring add up to a translate of an open-chain Hamiltonian. It opens
with the kernel of the Hamiltonian of a restriction of a positive interaction to some of its
terms.

## Main results

* `ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_restrict_iff` — for positive
  semidefinite terms, the kernel of the Hamiltonian of a restriction is the common kernel of the
  operators of the retained terms.
* `ManyBody.Interaction.translationInvariant_term_add`, `translationInvariant_term_mono`,
  `hamiltonian_translationInvariant_mono`, `posSemidef_hamiltonian_translationInvariant`,
  `continuous_hamiltonian_translationInvariant` — the ring terms as functions of `h`.
* `ManyBody.Interaction.hamiltonian_chainTranslates_mono`,
  `posSemidef_hamiltonian_chainTranslates`, `continuous_hamiltonian_chainTranslates` — the
  open-chain Hamiltonian as a function of `h`.
* `ManyBody.Interaction.sum_hamiltonian_restrict_chainTranslates_le` — the counting bound of
  condition C1 of Nachtergaele's martingale method.
* `ManyBody.Interaction.chainTranslates_term_eq_translationInvariant_term`,
  `hamiltonian_chainTranslates_eq_sum_nonwrappingStart` — a window that does not wrap is the same
  term on the ring and on the open chain.
* `ManyBody.Interaction.translationInvariant_term_hamiltonian_chainTranslates`,
  `cyclicWindowSum_toEuclideanLin_translationInvariant_term` — consecutive ring terms form a
  translate of an open-chain Hamiltonian.
* `ManyBody.Interaction.commute_translationInvariant_term_add_of_le`,
  `toEuclideanLin_translationInvariant_term_commute_siteDiagonal` — commutation of ring terms with
  separated ring terms and with sitewise diagonal observables.

## References

* Nachtergaele, arXiv:cond-mat/9410110, condition C1, lines 1030–1041.
* Knabe, J. Stat. Phys. 52, 627 (1988).
* Cirac, Pérez-García, Schuch and Verstraete, arXiv:2011.12127, Section IV.C,
  lines 1995–2007, 2183–2187 and 2194–2197.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace ManyBody.Interaction

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Two matrices commute exactly when their Euclidean operators commute. -/
private theorem commute_toEuclideanLin_iff {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} : Commute (toEuclideanLin A) (toEuclideanLin B) ↔ Commute A B :=
  commute_map_iff (f := toLpLinAlgEquiv (R := ℂ) (n := n) 2) (toLpLinAlgEquiv 2).injective
    (x := A) (y := B)

section Restrict

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} [Fintype ι] {T : ι → Finset V}

/-- For positive semidefinite terms, the Hamiltonian of the restriction of an interaction to the
indices with a property annihilates a vector exactly when every term with the property does. -/
theorem mem_ker_toEuclideanLin_hamiltonian_restrict_iff {Φ : Interaction X T}
    (hΦ : ∀ i, (Φ.term i).PosSemidef) (p : ι → Prop) [DecidablePred p]
    {v : EuclideanSpace ℂ (Config X)} :
    v ∈ LinearMap.ker (toEuclideanLin (Φ.restrict p).hamiltonian) ↔
      ∀ i, p i → toEuclideanLin (Φ.term i) v = 0 := by
  rw [mem_ker_toEuclideanLin_hamiltonian_iff fun i ↦ forall_restrict_term PosSemidef.zero (hΦ i)]
  refine forall_congr' fun i ↦ ?_
  by_cases hi : p i <;> simp [hi]

end Restrict

/-! ### Translates on the ring -/

section Ring

open Fin.CommRing

variable {R N : ℕ} [NeZero N]

/-- The term of the translates on the ring is additive in the local matrix. -/
theorem translationInvariant_term_add (h k : Matrix (Fin R → α) (Fin R → α) ℂ) (i : Fin N) :
    (translationInvariant N (h + k)).term i =
      (translationInvariant N h).term i + (translationInvariant N k).term i := by
  by_cases hRN : R ≤ N
  · simp only [translationInvariant_term_of_le _ hRN, placeAlong_add]
  · simp only [translationInvariant_term_of_not_le _ hRN, add_zero]

/-- The term of the translates on the ring of a difference of local matrices. -/
theorem translationInvariant_term_sub (h k : Matrix (Fin R → α) (Fin R → α) ℂ) (i : Fin N) :
    (translationInvariant N (h - k)).term i =
      (translationInvariant N h).term i - (translationInvariant N k).term i := by
  by_cases hRN : R ≤ N
  · simp only [translationInvariant_term_of_le _ hRN, placeAlong_sub]
  · simp only [translationInvariant_term_of_not_le _ hRN, sub_zero]

/-- For `R ≤ N`, every term of the translates of the local identity is the identity. -/
theorem translationInvariant_term_one (hRN : R ≤ N) (i : Fin N) :
    (translationInvariant N (1 : Matrix (Fin R → α) (Fin R → α) ℂ)).term i = 1 := by
  rw [translationInvariant_term_of_le _ hRN, placeAlong_one]

/-- The term of the translates on the ring is monotone in the local matrix. -/
theorem translationInvariant_term_mono {h h' : Matrix (Fin R → α) (Fin R → α) ℂ} (hle : h ≤ h')
    (i : Fin N) : (translationInvariant N h).term i ≤ (translationInvariant N h').term i := by
  by_cases hRN : R ≤ N
  · rw [translationInvariant_term_of_le _ hRN, translationInvariant_term_of_le _ hRN]
    exact placeAlong_le_placeAlong _ hle
  · rw [translationInvariant_term_of_not_le _ hRN, translationInvariant_term_of_not_le _ hRN]

/-- For `R ≤ N`, the term with index `i` of the translates of a diagonal local matrix is the
diagonal matrix of its values on the window of `R` consecutive sites starting at `i`, including
a window crossing the periodic seam. -/
theorem translationInvariant_term_diagonal (hRN : R ≤ N) (f : (Fin R → α) → ℂ) (i : Fin N) :
    (translationInvariant N (diagonal f)).term i =
      diagonal fun σ : Fin N → α ↦ f fun j ↦ σ (i + Fin.castLE hRN j) := by
  rw [translationInvariant_term_of_le _ hRN, placeAlong_diagonal]
  rfl

/-- The Hamiltonian of the translates on the ring is monotone in the local matrix. -/
theorem hamiltonian_translationInvariant_mono {h h' : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hle : h ≤ h') :
    (translationInvariant N h).hamiltonian ≤ (translationInvariant N h').hamiltonian :=
  Finset.sum_le_sum fun i _ ↦ translationInvariant_term_mono hle i

/-- The Hamiltonian of the translates on the ring of a scalar multiple. -/
theorem hamiltonian_translationInvariant_smul (c : ℂ) (h : Matrix (Fin R → α) (Fin R → α) ℂ) :
    (translationInvariant N (c • h)).hamiltonian = c • (translationInvariant N h).hamiltonian := by
  by_cases hRN : R ≤ N
  · simp only [hamiltonian_translationInvariant_of_le _ hRN, placeAlong_smul, Finset.smul_sum]
  · rw [hamiltonian_translationInvariant_of_not_le _ hRN,
      hamiltonian_translationInvariant_of_not_le _ hRN, smul_zero]

/-- A positive semidefinite local matrix has a positive semidefinite Hamiltonian on the ring. -/
theorem posSemidef_hamiltonian_translationInvariant {h : Matrix (Fin R → α) (Fin R → α) ℂ}
    (hh : h.PosSemidef) : (translationInvariant N h).hamiltonian.PosSemidef :=
  posSemidef_hamiltonian fun i ↦
    nonneg_iff_posSemidef.mp (translationInvariant_term_nonneg hh.nonneg i)

variable (R N) in
/-- At a fixed volume, the Hamiltonian of the translates of a local matrix on the ring depends
continuously on the matrix. -/
theorem continuous_hamiltonian_translationInvariant :
    Continuous fun h : Matrix (Fin R → α) (Fin R → α) ℂ ↦
      (translationInvariant N h).hamiltonian := by
  by_cases hRN : R ≤ N
  · simp only [hamiltonian, translationInvariant_term_of_le _ hRN]
    refine continuous_finsetSum _ fun i _ ↦ ?_
    exact (placeAlongHom (X := fun _ : Fin N ↦ α) _).toAlgHom.toLinearMap
      |>.continuous_of_finiteDimensional
  · simp only [hamiltonian, translationInvariant_term_of_not_le _ hRN]
    exact continuous_const

/-- The operators of the terms of the translates on the ring, indexed by the cyclic group, add
up to the operator of the Hamiltonian. -/
theorem sum_toEuclideanLin_translationInvariant_term_finEquiv_symm
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) :
    ∑ s : ZMod N, toEuclideanLin ((translationInvariant N h).term ((ZMod.finEquiv N).symm s)) =
      toEuclideanLin (translationInvariant N h).hamiltonian := by
  rw [hamiltonian, map_sum]
  exact (ZMod.finEquiv N).symm.toEquiv.sum_comp fun i ↦
    toEuclideanLin ((translationInvariant N h).term i)

/-- **Separated windows.** Terms of translates on the ring whose windows of `R` consecutive
sites start `e` sites apart, with `R ≤ e` and `e + R ≤ N`, commute: the windows are
disjoint. -/
theorem commute_translationInvariant_term_add_of_le
    (h h' : Matrix (Fin R → α) (Fin R → α) ℂ) {e : ℕ} (hR : R ≤ e) (he : e + R ≤ N)
    (i : Fin N) :
    Commute ((translationInvariant N h).term i)
      ((translationInvariant N h').term (i + (e : Fin N))) := by
  have hRN : R ≤ N := by omega
  rw [translationInvariant_term_of_le _ hRN, translationInvariant_term_of_le _ hRN]
  refine commute_placeAlong_of_disjoint (X := fun _ ↦ α) _
    (Finset.disjoint_left.mpr fun k hki hkj ↦ ?_) _ _
  obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hki
  obtain ⟨b, -, hb⟩ := Finset.mem_map.mp hkj
  rw [ringWindow_apply, ringWindow_apply, add_assoc] at hb
  have hv := congrArg Fin.val (add_left_cancel hb)
  have ha := a.isLt
  have hbR := b.isLt
  rw [Fin.val_add, Fin.val_natCast, Fin.val_castLE, Fin.val_castLE,
    Nat.mod_eq_of_lt (show e < N by omega), Nat.mod_eq_of_lt (show e + b.val < N by omega)] at hv
  omega

/-- Separated terms commute, for sites indexed by the cyclic group. -/
theorem commute_translationInvariant_term_finEquiv_symm_add_of_le
    (h h' : Matrix (Fin R → α) (Fin R → α) ℂ) {e : ℕ} (hR : R ≤ e) (he : e + R ≤ N)
    (s : ZMod N) :
    Commute ((translationInvariant N h).term ((ZMod.finEquiv N).symm s))
      ((translationInvariant N h').term ((ZMod.finEquiv N).symm (s + (e : ZMod N)))) := by
  rw [map_add, map_natCast]
  exact commute_translationInvariant_term_add_of_le h h' hR he _

end Ring

/-- **Sitewise diagonal observables.** If a local matrix commutes with the diagonal observable
`ω ↦ f (ω r)` at every site `r` of its window, every term of its translates on the ring commutes
with the diagonal observable `σ ↦ f (σ k)` at every site `k` of the ring, inside the window of
the term or not. -/
theorem toEuclideanLin_translationInvariant_term_commute_siteDiagonal {R N : ℕ}
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) (hRN : R ≤ N) (f : α → ℂ)
    (hf : ∀ r : Fin R,
      Commute (toEuclideanLin (diagonal fun ω : Fin R → α ↦ f (ω r))) (toEuclideanLin h))
    (i k : Fin N) :
    haveI : NeZero N := NeZero.of_pos i.pos;
    Commute (toEuclideanLin (diagonal fun σ : Fin N → α ↦ f (σ k)))
      (toEuclideanLin ((translationInvariant N h).term i)) := by
  have : NeZero N := NeZero.of_pos i.pos
  rw [commute_toEuclideanLin_iff, translationInvariant_term_of_le _ hRN]
  by_cases hk : k ∈ Finset.univ.map (ringWindow hRN i)
  · obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp hk
    have hD : (diagonal fun σ : Fin N → α ↦ f (σ (ringWindow hRN i r))) =
        placeAlong (X := fun _ ↦ α) (ringWindow hRN i) (diagonal fun ω ↦ f (ω r)) := by
      rw [placeAlong_diagonal]
    rw [hD]
    exact (commute_toEuclideanLin_iff.mp (hf r)).map
      (placeAlongHom (X := fun _ : Fin N ↦ α) (ringWindow hRN i))
  · let e : Fin 1 ↪ Fin N := ⟨fun _ ↦ k, fun a b _ ↦ Subsingleton.elim a b⟩
    have hD : (diagonal fun σ : Fin N → α ↦ f (σ k)) =
        placeAlong (X := fun _ ↦ α) e (diagonal fun ω ↦ f (ω 0)) := by
      rw [placeAlong_diagonal]
      rfl
    rw [hD]
    refine commute_placeAlong_of_disjoint (X := fun _ ↦ α) _
      (Finset.disjoint_left.mpr fun v hv hv' ↦ hk ?_) _ _
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hv
    exact hv'

/-! ### Translates on the open chain -/

section Chain

variable {k : ℕ}

/-- The Hamiltonian of the open-chain translates is monotone in the local matrix. -/
theorem hamiltonian_chainTranslates_mono {h h' : Matrix (Fin k → α) (Fin k → α) ℂ} (hle : h ≤ h')
    (N : ℕ) : (chainTranslates k N h).hamiltonian ≤ (chainTranslates k N h').hamiltonian :=
  Finset.sum_le_sum fun _ _ ↦ placeAlong_le_placeAlong (X := fun _ ↦ α) _ hle

/-- The Hamiltonian of the open-chain translates of a scalar multiple of a local matrix is that
scalar multiple of the Hamiltonian. -/
theorem hamiltonian_chainTranslates_smul (c : ℂ) (h : Matrix (Fin k → α) (Fin k → α) ℂ)
    (N : ℕ) :
    (chainTranslates k N (c • h)).hamiltonian = c • (chainTranslates k N h).hamiltonian := by
  simp only [hamiltonian, ofPlaceAlong_term, placeAlong_smul, Finset.smul_sum]

/-- The open-chain translates of the zero matrix have zero Hamiltonian. -/
theorem hamiltonian_chainTranslates_zero (N : ℕ) :
    (chainTranslates k N (0 : Matrix (Fin k → α) (Fin k → α) ℂ)).hamiltonian = 0 := by
  simp [hamiltonian, ofPlaceAlong_term, placeAlong_zero]

/-- The open-chain translates of a positive semidefinite matrix have a positive semidefinite
Hamiltonian. -/
theorem posSemidef_hamiltonian_chainTranslates {h : Matrix (Fin k → α) (Fin k → α) ℂ}
    (hh : h.PosSemidef) (N : ℕ) : (chainTranslates k N h).hamiltonian.PosSemidef :=
  posSemidef_hamiltonian fun i ↦ nonneg_iff_posSemidef.mp
    (ofPlaceAlong_term_nonneg _ (fun _ ↦ nonneg_iff_posSemidef.mpr hh) i)

/-- At a fixed volume, the open-chain Hamiltonian of the translates of a local matrix depends
continuously on the matrix. -/
theorem continuous_hamiltonian_chainTranslates (R N : ℕ) :
    Continuous fun h : Matrix (Fin R → α) (Fin R → α) ℂ ↦
      (chainTranslates R N h).hamiltonian := by
  simp only [hamiltonian, chainTranslates, ofPlaceAlong_term]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact (placeAlongHom (X := fun _ : Fin N ↦ α) _).toAlgHom.toLinearMap
    |>.continuous_of_finiteDimensional

/-- For a local matrix on no sites, every term of the open-chain translates is the scalar entry
of the matrix times the identity. -/
theorem chainTranslates_fin_zero_term {N : ℕ} (K : Matrix (Fin 0 → α) (Fin 0 → α) ℂ)
    (i : Fin (N + 1 - 0)) : (chainTranslates 0 N K).term i = K default default • 1 := by
  have hK : K = K default default • 1 := by
    ext a b
    rw [Subsingleton.elim a default, Subsingleton.elim b default]
    simp
  rw [chainTranslates, ofPlaceAlong_term]
  conv_lhs => rw [hK]
  rw [placeAlong_smul, placeAlong_one]

/-- **The counting bound of condition C1.** On the open chain, each window of `R` sites lies in
at most `W - R + 1` of the intervals `[n - W, n)`, `W ≤ n ≤ N`; summing the Hamiltonians of the
restrictions of the translates of a positive matrix to the windows inside these intervals gives
at most `W - R + 1` times the Hamiltonian. Nachtergaele, arXiv:cond-mat/9410110, condition C1,
lines 1030–1041. -/
theorem sum_hamiltonian_restrict_chainTranslates_le {R W : ℕ} (hRW : R ≤ W)
    {h : Matrix (Fin R → α) (Fin R → α) ℂ} (hh : 0 ≤ h) (N : ℕ) :
    ∑ n ∈ Finset.Icc W N, ((chainTranslates R N h).restrict
        fun i ↦ n - W ≤ i.val ∧ i.val + R ≤ n).hamiltonian ≤
      ((W - R + 1 : ℕ) : ℂ) • (chainTranslates R N h).hamiltonian := by
  simp only [hamiltonian, restrict_term]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  refine nsmul_le_nsmul_left (ofPlaceAlong_term_nonneg _ (fun _ ↦ hh) i) ?_
  calc _ ≤ (Finset.Icc (i.val + R) (i.val + W)).card :=
        Finset.card_le_card fun n hn ↦ by
          simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
          omega
    _ = W - R + 1 := by
        rw [Nat.card_Icc]
        omega

end Chain

/-! ### Translates on the ring and on the open chain -/

section RingChain

open Fin.CommRing

variable {R N : ℕ} [NeZero N]

/-- **A window that does not wrap.** A term of the translates of `h` on the open chain is the
term of the translates of `h` on the ring at the same start. -/
theorem chainTranslates_term_eq_translationInvariant_term
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) (hR : 0 < R) (i : Fin (N + 1 - R)) :
    (chainTranslates R N h).term i =
      (translationInvariant N h).term ⟨i.val, by have := i.isLt; omega⟩ := by
  have hi := i.isLt
  rw [chainTranslates, ofPlaceAlong_term, translationInvariant_term_of_le _ (by omega : R ≤ N)]
  congr 1
  ext j
  simp only [val_chainWindow, ringWindow_apply, Fin.val_add, Fin.val_castLE]
  rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]

/-- For a positive range, the open-chain Hamiltonian of the translates of a local matrix is the
sum of the terms of its translates on the ring over the windows that do not cross the right
end of the chain. -/
theorem hamiltonian_chainTranslates_eq_sum_nonwrappingStart
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) (hR : 0 < R) :
    (chainTranslates R N h).hamiltonian =
      ∑ i : {i : Fin N // i.val + R ≤ N}, (translationInvariant N h).term i.1 := by
  rw [hamiltonian]
  refine Fintype.sum_equiv
    ⟨fun j ↦ ⟨⟨j.val, by have := j.isLt; omega⟩, by have := j.isLt; change j.val + R ≤ N; omega⟩,
      fun i ↦ ⟨i.1.val, by have := i.2; omega⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩ _ _ fun j ↦ ?_
  exact chainTranslates_term_eq_translationInvariant_term h hR j

/-- **A window of terms.** On the ring of `N` sites, the translate to the window of `W ≤ N`
consecutive sites starting at `i` of the open-chain Hamiltonian of `h` on `W` sites is the sum of
the terms of the translates of `h` on the ring at the starts `i, i + 1, …, i + (W - R)`: the
windows of `R` consecutive sites inside that window. -/
theorem translationInvariant_term_hamiltonian_chainTranslates
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) {W : ℕ} (hWN : W ≤ N) (i : Fin N) :
    (translationInvariant N (chainTranslates R W h).hamiltonian).term i =
      ∑ j : Fin (W + 1 - R), (translationInvariant N h).term (i + (j.val : Fin N)) := by
  rw [translationInvariant_term_of_le _ hWN, hamiltonian, placeAlong_sum]
  refine Fintype.sum_congr _ _ fun j ↦ ?_
  rw [ofPlaceAlong_term, translationInvariant_term_of_le _ (show R ≤ N by have := j.isLt; omega),
    placeAlong_placeAlong, chainWindow_trans_ringWindow]

/-- **A Knabe block.** For `1 ≤ R`, the sum of the operators of `m` consecutive terms of the
translates of `h` on the ring, starting at the site `s`, is the operator of the translate to the
window of `m + R - 1` consecutive sites starting at `s` of the open-chain Hamiltonian of `h` on
`m + R - 1` sites. The sites are indexed by the cyclic group, as in the finite-range Knabe
inequality. -/
theorem cyclicWindowSum_toEuclideanLin_translationInvariant_term
    (h : Matrix (Fin R → α) (Fin R → α) ℂ) {m : ℕ} (hR : 1 ≤ R) (hW : m + R - 1 ≤ N)
    (s : ZMod N) :
    ProjectionGeometry.cyclicWindowSum (fun s : ZMod N ↦
        toEuclideanLin ((translationInvariant N h).term ((ZMod.finEquiv N).symm s))) m s =
      toEuclideanLin ((translationInvariant N
        (chainTranslates R (m + R - 1) h).hamiltonian).term ((ZMod.finEquiv N).symm s)) := by
  rw [translationInvariant_term_hamiltonian_chainTranslates h hW, map_sum,
    ProjectionGeometry.cyclicWindowSum]
  refine Fin.sum_eq_sum_of_val_eq _ _ (fun k _ _ ↦ ?_) (fun i hi ↦ absurd i.isLt (by omega))
    (fun i hi ↦ absurd i.isLt (by omega))
  rw [map_add, map_natCast]

end RingChain

end ManyBody.Interaction
