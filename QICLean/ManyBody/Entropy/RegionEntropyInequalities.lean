/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.Conditional.ConditionalEntropy
import QICLean.ManyBody.Entropy.RegionStrongSubadditivity
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.ManyBody.Sites.RegionState
import QICLean.Entropy.VonNeumann.Entropy
import QICLean.ManyBody.Entropy.RegionEntropy

/-!
# Entropy inequalities for regions of a pure state

Consequences of subadditivity, strong subadditivity and purity for the regional entropies
`S(R)` of a unit vector on a finite tensor product: the Araki–Lieb inequality
`S(R) ≤ S(R ∪ T) + S(T)` for disjoint regions, the dimension bound
`S(R) ≤ log dim R`, and, on a region `P` of zero entropy, `S(P \ X) = S(X)` for `X ⊆ P`,
additivity `S(X ∪ Y) = S(X) + S(Y)` for `X ⊆ P` and `Y` disjoint from `P`, and
`S(A ∆ P) = S(A)`. No geometry of the sites enters.

Moved from TNLean, `TNLean/Lattice/RegionEntropyInequalities.lean` at commit `e41c3b63`,
restated for `ManyBody.regionEntropy` on an arbitrary family of local alphabets; the dimension
bound `|R| log q` there is the identical-site case of `ManyBody.regionEntropy_le_log_card`.

## Main results

* `ManyBody.regionEntropy_le_union_add` — the Araki–Lieb inequality.
* `ManyBody.regionEntropy_le_log_card` — the dimension bound.
* `ManyBody.regionEntropy_sdiff_eq_of_eq_zero`, `ManyBody.regionEntropy_union_eq_of_eq_zero`,
  `ManyBody.regionEntropy_symmDiff_eq_of_eq_zero` — regions of zero entropy.
* `ManyBody.regionEntropy_eq_zero_of_localDimension_one`: regional entropies with one local
  dimension.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 2 (`sec:prelim`), `01-preliminaries.tex`, lines 10–25, and the proof of
  Theorem 1.1, `10-geometry.tex`, lines 846–851.
* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, `part1_arealaw.tex`, Section 2 (`sec:setting`).
-/

section RegionEntropyInequalities

open scoped BigOperators symmDiff

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable {ψ : EuclideanSpace ℂ ((v : V) → β v)}

/-- **The Araki–Lieb inequality.** For disjoint regions `R` and `T` of a unit vector,
`S(R) ≤ S(R ∪ T) + S(T)`. Two-dimensional area law, `01-preliminaries.tex`, lines 10–25. -/
theorem regionEntropy_le_union_add (hψ : ‖ψ‖ = 1) {R T : Finset V} (hRT : Disjoint R T) :
    regionEntropy ψ R ≤ regionEntropy ψ (R ∪ T) + regionEntropy ψ T := by
  have hdisj : Disjoint (R ∪ T)ᶜ T := disjoint_compl_left_iff.mpr Finset.subset_union_right
  have hRc : Rᶜ = (R ∪ T)ᶜ ∪ T := by
    ext v
    have hv : v ∈ R → v ∉ T := fun hv ↦ Finset.disjoint_left.mp hRT hv
    simp only [Finset.mem_compl, Finset.mem_union, not_or]
    tauto
  calc regionEntropy ψ R
      = regionEntropy ψ ((R ∪ T)ᶜ ∪ T) := by
        rw [← regionEntropy_compl β ψ R, hRc]
    _ ≤ regionEntropy ψ (R ∪ T)ᶜ + regionEntropy ψ T :=
        regionEntropy_union_le β ψ hψ _ _ hdisj
    _ = regionEntropy ψ (R ∪ T) + regionEntropy ψ T := by
        rw [regionEntropy_compl]

/-- **The dimension bound.** The entropy of a region of a unit vector is at most the logarithm
of the dimension of its configuration space. -/
theorem regionEntropy_le_log_card (hψ : ‖ψ‖ = 1) (R : Finset V) :
    regionEntropy ψ R ≤ Real.log (Fintype.card (RegionConfig β R)) :=
  Entropy.vonNeumannEntropy_le_log_card (regionState_posSemidef R ψ)
    (trace_regionState_eq_one hψ (D := R))

/-- With `q` states at every site, a region `A` has entropy at most `|A| log q`: the identical-site
case of `ManyBody.regionEntropy_le_log_card`. -/
theorem regionEntropy_le_card_mul_log {q : ℕ} {Ω : EuclideanSpace ℂ (V → Fin q)} (hΩ : ‖Ω‖ = 1)
    (A : Finset V) : regionEntropy Ω A ≤ (A.card : ℝ) * Real.log q := by
  refine (regionEntropy_le_log_card _ hΩ A).trans (le_of_eq ?_)
  simp [RegionConfig, Fintype.card_pi, Real.log_pow]

/-- Inside a region `P` of zero entropy, complementary subregions have equal entropy:
`S(P \ X) = S(X)` for `X ⊆ P`. Two-dimensional area law, `10-geometry.tex`,
lines 846–851. -/
theorem regionEntropy_sdiff_eq_of_eq_zero (hψ : ‖ψ‖ = 1) {P X : Finset V}
    (hP : regionEntropy ψ P = 0) (hX : X ⊆ P) : regionEntropy ψ (P \ X)
        = regionEntropy ψ X := by
  have h1 := regionEntropy_le_union_add β hψ (Finset.disjoint_sdiff (s := X) (t := P))
  have h2 := regionEntropy_le_union_add β hψ (Finset.sdiff_disjoint (s := X) (t := P))
  rw [Finset.union_sdiff_of_subset hX, hP] at h1
  rw [Finset.sdiff_union_of_subset hX, hP] at h2
  linarith

/-- Across a region `P` of zero entropy the entropy is additive: `S(X ∪ Y) = S(X) + S(Y)` for
`X ⊆ P` and `Y` disjoint from `P`. Two-dimensional area law, `10-geometry.tex`,
lines 846–851. -/
theorem regionEntropy_union_eq_of_eq_zero (hψ : ‖ψ‖ = 1) {P X Y : Finset V}
    (hP : regionEntropy ψ P = 0) (hX : X ⊆ P) (hY : Disjoint Y P) :
    regionEntropy ψ (X ∪ Y) = regionEntropy ψ X + regionEntropy ψ Y := by
  have hXY : Disjoint X Y := (hY.mono_right hX).symm
  have hle := regionEntropy_union_le β ψ hψ X Y hXY
  have hsub := regionEntropy_submodular β ψ P (X ∪ Y)
  have hAL := regionEntropy_le_union_add β hψ hY
  have hi : P ∩ (X ∪ Y) = X := by
    ext v
    have hv : v ∈ Y → v ∉ P := fun h ↦ Finset.disjoint_left.mp hY h
    have hv' : v ∈ X → v ∈ P := fun h ↦ hX h
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hu : P ∪ (X ∪ Y) = Y ∪ P := by
    rw [← Finset.union_assoc, Finset.union_eq_left.mpr hX, Finset.union_comm]
  rw [hi, hu, hP] at hsub
  rw [hP] at hAL
  linarith

/-- **Flipping a region of zero entropy.** If `S(P) = 0`, then `S(A ∆ P) = S(A)` for every
region `A`. Two-dimensional area law, `10-geometry.tex`, lines 846–851. -/
theorem regionEntropy_symmDiff_eq_of_eq_zero (hψ : ‖ψ‖ = 1) {P : Finset V}
    (hP : regionEntropy ψ P = 0) (A : Finset V) : regionEntropy ψ (A ∆ P)
        = regionEntropy ψ A := by
  have hA : A = (A ∩ P) ∪ (A \ P) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hAP : A ∆ P = (P \ (A ∩ P)) ∪ (A \ P) := by
    ext v
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hd : Disjoint (A \ P) P := Finset.sdiff_disjoint
  rw [hAP, regionEntropy_union_eq_of_eq_zero β hψ hP Finset.sdiff_subset hd,
    regionEntropy_sdiff_eq_of_eq_zero β hψ hP Finset.inter_subset_right]
  conv_rhs => rw [hA]
  rw [regionEntropy_union_eq_of_eq_zero β hψ hP Finset.inter_subset_right hd]

end ManyBody

end RegionEntropyInequalities

section QuditRegionEntropy

/-!
## Regional entropies with one local dimension

A fact about a system of sites `V` with the same local dimension `q` at every site, which the
regional entropy inequalities of `QICLean.ManyBody.Entropy.RegionEntropyInequalities` do not
contain: for `q = 1` every region of a unit vector has zero entropy. The statement uses no
geometry of `V`.

Moved from TNLean, `TNLean/Lattice/RegionEntropyInequalities.lean`. Changes: namespace
`ManyBody` in place of `TNLean.Lattice`.

### Main results

* `ManyBody.regionEntropy_eq_zero_of_localDimension_one`.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 2 (`sec:prelim`), `01-preliminaries.tex`, line 116.
-/

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every region of a unit vector on one-dimensional local spaces has zero entropy: the
regional state has trace one on a one-dimensional configuration space, so its rank is at
most one. Area law, `01-preliminaries.tex`, line 116. -/
theorem regionEntropy_eq_zero_of_localDimension_one
    {Ω : EuclideanSpace ℂ (V → Fin 1)} (hΩ : ‖Ω‖ = 1) (A : Finset V) :
    regionEntropy (X := fun _ ↦ Fin 1) Ω A = 0 := by
  apply vonNeumannEntropy_eq_zero_of_rank_le_one (regionState_posSemidef A Ω)
    (trace_regionState_eq_one hΩ)
  exact (Matrix.rank_le_card_width _).trans_eq (by simp [RegionConfig])

end ManyBody

end QuditRegionEntropy

namespace ManyBody

/-- **Telescoping along an injective key.** For an injective key `κ` into a linear order,
`∑_{i ∈ s} (G {j ∈ s | κ j ≤ κ i} - G {j ∈ s | κ j < κ i}) = G s - G ∅`. -/
theorem sum_sub_filter_key_eq {ι β : Type*} [LinearOrder β] (κ : ι → β)
    (hκ : Function.Injective κ) (G : Finset ι → ℝ) (s : Finset ι) :
    ∑ i ∈ s, (G (s.filter fun j ↦ κ j ≤ κ i) - G (s.filter fun j ↦ κ j < κ i)) =
      G s - G ∅ := by
  classical
  induction s using Finset.induction_on_max_value κ with
  | empty => simp
  | insert a s ha hmax ih =>
    have hlt : ∀ x ∈ s, κ x < κ a := fun x hx ↦
      lt_of_le_of_ne (hmax x hx) fun h ↦ ha (hκ h ▸ hx)
    have h1 : (insert a s).filter (fun j ↦ κ j ≤ κ a) = insert a s :=
      Finset.filter_true_of_mem fun x hx ↦ by
        rcases Finset.mem_insert.mp hx with rfl | hx
        exacts [le_rfl, (hlt x hx).le]
    have h2 : (insert a s).filter (fun j ↦ κ j < κ a) = s := by
      rw [Finset.filter_insert, ite_eq_right (lt_irrefl _)]
      exact Finset.filter_true_of_mem hlt
    have h3 : ∀ i ∈ s, (insert a s).filter (fun j ↦ κ j ≤ κ i) =
        s.filter (fun j ↦ κ j ≤ κ i) := fun i hi ↦ by
      rw [Finset.filter_insert, ite_eq_right (not_le.mpr (hlt i hi))]
    have h4 : ∀ i ∈ s, (insert a s).filter (fun j ↦ κ j < κ i) =
        s.filter (fun j ↦ κ j < κ i) := fun i hi ↦ by
      rw [Finset.filter_insert, ite_eq_right (not_lt.mpr (hlt i hi).le)]
    rw [Finset.sum_insert ha, h1, h2,
      Finset.sum_congr rfl fun i hi ↦ by rw [h3 i hi, h4 i hi], ih]
    ring

variable {Λ : Finset (ℤ × ℤ)} {q : ℕ}

/-- **The chain rule averaged over rotated color orders.** Let `Ω` be a unit vector, `X_i`
pairwise disjoint regions, and `col i < N` colors. Suppose every `i ∈ good` has a buffer `T_i`
contained in the union of the regions of the other colors, with
`S(X_i | T_i) ≤ S(X_i)/2 + β`. Then
`S(⋃ X_i) ≤ ∑_i S(X_i) - (1/(2N)) ∑_{i ∈ good} S(X_i) + |good| β / N`.
Source: `02-initial.tex`, lines 625–646, the expected entropy chain rule. -/
theorem regionEntropy_biUnion_le_rotations (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) (hΩ : ‖Ω‖ = 1)
    {ι : Type*}
    [Fintype ι] (Xs : ι → Finset ↥Λ)
    (hdisj : Pairwise fun i j ↦ Disjoint (Xs i) (Xs j)) {N : ℕ} (col : ι → ℕ)
    (hcol : ∀ i, col i < N) (good : Finset ι) (T : ι → Finset ↥Λ) (β : ℝ)
    (hT : ∀ i ∈ good, T i ⊆ (Finset.univ.filter fun j ↦ col j ≠ col i).biUnion Xs)
    (hbuf : ∀ i ∈ good, ManyBody.regionEntropy Ω (Xs i ∪ T i) - ManyBody.regionEntropy Ω (T i) ≤
      ManyBody.regionEntropy Ω (Xs i) / 2 + β) :
    ManyBody.regionEntropy Ω (Finset.univ.biUnion Xs) ≤
      ∑ i, ManyBody.regionEntropy Ω (Xs i) -
        (∑ i ∈ good, ManyBody.regionEntropy Ω (Xs i)) / (2 * N) + good.card * β / N := by
  classical
  -- `N > 0` unless the index set is empty
  rcases isEmpty_or_nonempty ι with hι | hι
  · obtain rfl : good = ∅ := Finset.eq_empty_of_isEmpty good
    simp [Finset.univ_eq_empty, ManyBody.regionEntropy_empty _ Ω hΩ]
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) (hcol (Classical.arbitrary ι))
  set S : Finset ↥Λ → ℝ := ManyBody.regionEntropy Ω
  -- the key of the `k`-th rotation
  set e := Fintype.equivFin ι
  set κ : ℕ → ι → Lex (ℕ × ℕ) := fun k i ↦ toLex ((col i + k) % N, (e i : ℕ))
  have hκ : ∀ k, Function.Injective (κ k) := fun k i j h ↦ by
    have := congrArg (fun p : Lex (ℕ × ℕ) ↦ (ofLex p).2) h
    simp only [κ, ofLex_toLex] at this
    exact e.injective (Fin.ext this)
  set pre : ℕ → ι → Finset ↥Λ := fun k i ↦
    (Finset.univ.filter fun j ↦ κ k j < κ k i).biUnion Xs
  set term : ℕ → ι → ℝ := fun k i ↦ S (Xs i ∪ pre k i) - S (pre k i)
  -- the chain rule for each rotation
  have hchain : ∀ k, S (Finset.univ.biUnion Xs) = ∑ i, term k i := by
    intro k
    have h := sum_sub_filter_key_eq (κ k) (hκ k) (fun s ↦ S (s.biUnion Xs)) Finset.univ
    simp only [Finset.biUnion_empty] at h
    rw [show S ∅ = 0 from ManyBody.regionEntropy_empty _ Ω hΩ, sub_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hins : (Finset.univ.filter fun j ↦ κ k j ≤ κ k i) =
        insert i (Finset.univ.filter fun j ↦ κ k j < κ k i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        rcases hj.lt_or_eq with hj | hj
        · exact Or.inr hj
        · exact Or.inl (hκ k hj)
      · rintro (rfl | hj)
        exacts [le_rfl, hj.le]
    simp only [term, pre]
    rw [hins, Finset.biUnion_insert]
  -- disjointness from the predecessors
  have hpre : ∀ k i, Disjoint (Xs i) (pre k i) := fun k i ↦ by
    refine (Finset.disjoint_biUnion_right _ _ _).mpr fun j hj ↦ hdisj ?_
    rintro rfl
    simp at hj
  have hterm : ∀ k i, term k i ≤ S (Xs i) := fun k i ↦ by
    have := Entropy.regionEntropy_cond_anti (n := fun _ ↦ q) (hpre k i)
      (Finset.empty_subset (pre k i)) Ω
    simpa [term, S, ManyBody.regionEntropy_empty _ Ω hΩ] using this
  -- the good rotation of a good index
  have hgood : ∀ i ∈ good, term (N - 1 - col i) i ≤ S (Xs i) / 2 + β := by
    intro i hi
    set k := N - 1 - col i
    have hci := hcol i
    have hki : (col i + k) % N = N - 1 := by
      rw [show col i + k = N - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
    have hsub : T i ⊆ pre k i := by
      refine (hT i hi).trans (Finset.biUnion_subset_biUnion_of_subset_left _ ?_)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have hcj := hcol j
      have hne : (col j + k) % N ≠ N - 1 := by
        intro h
        have h1 : (col j + k) % N = (col i + k) % N := by rw [h, hki]
        have := Nat.ModEq.add_right_cancel' k h1
        exact hj (by rwa [Nat.ModEq, Nat.mod_eq_of_lt hcj, Nat.mod_eq_of_lt hci] at this)
      have hlt : (col j + k) % N < N - 1 := by
        have := Nat.mod_lt (col j + k) hN; omega
      simp only [κ]
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by rw [hki]; exact hlt))
    have hdisjT : Disjoint (Xs i) (pre k i) := hpre k i
    have := Entropy.regionEntropy_cond_anti (n := fun _ ↦ q) hdisjT hsub Ω
    exact this.trans (hbuf i hi)
  -- sum over the rotations
  have hsumk : (N : ℝ) * S (Finset.univ.biUnion Xs) =
      ∑ i, ∑ k ∈ Finset.range N, term k i := by
    calc (N : ℝ) * S (Finset.univ.biUnion Xs) =
          ∑ k ∈ Finset.range N, S (Finset.univ.biUnion Xs) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∑ k ∈ Finset.range N, ∑ i, term k i := Finset.sum_congr rfl fun k _ ↦ hchain k
      _ = _ := Finset.sum_comm
  have hbound : ∀ i, ∑ k ∈ Finset.range N, term k i ≤
      N * S (Xs i) - (if i ∈ good then S (Xs i) / 2 - β else 0) := by
    intro i
    by_cases hi : i ∈ good
    · rw [ite_eq_left hi]
      have hk : N - 1 - col i ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ hk]
      have hrest : ∑ k ∈ (Finset.range N).erase (N - 1 - col i), term k i ≤
          ((N : ℝ) - 1) * S (Xs i) := by
        refine (Finset.sum_le_sum fun k _ ↦ hterm k i).trans ?_
        rw [Finset.sum_const, Finset.card_erase_of_mem hk, Finset.card_range, nsmul_eq_mul,
          Nat.cast_sub (by omega), Nat.cast_one]
      have := hgood i hi
      linarith
    · rw [ite_eq_right hi, sub_zero]
      refine (Finset.sum_le_sum fun k _ ↦ hterm k i).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htot := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hbound i
  rw [← hsumk, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.sum_div] at htot
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have key : S (Finset.univ.biUnion Xs) ≤ (N * ∑ i, S (Xs i) -
      (∑ i ∈ good, S (Xs i)) / 2 + good.card * β) / N := by
    rw [le_div_iff₀ hNpos]; linarith
  refine key.trans (le_of_eq ?_)
  field_simp

end ManyBody
