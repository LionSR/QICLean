/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.Defs
import QICLean.ManyBody.Sites.ThreeRegion.Birth

/-!
# The basis of a party of a sheet, read on regions of sites

The basis of a party `p` of a sheet is the configurations of the sites owned by `p`. When these
sites are described by a predicate, or split into two disjoint regions, the basis is read as the
configurations of that region, or as the pairs of configurations of the two regions
(`Sheet.regionEquiv`, `Sheet.splitEquiv`); both are relabellings of sites and involve no cast.
These are the coordinates in which the births, deaths and exchange corrections of a sheet act
at their parties: the manuscript compares vectors in their canonical site coordinates while
specifying the owners of the registers separately.

Two sheets in which a party owns the same sites give that party the same basis up to such a
relabelling, and the identification of the two bases along the equality of the systems is that
relabelling (`Sheet.cast_system_eq_regionEquiv`).

## Main definitions

* `QuantumCircuit.Party.Sheet.regionEquiv`, `QuantumCircuit.Party.Sheet.splitEquiv`,
  `QuantumCircuit.Party.Sheet.complSplitEquiv`: a party's basis read on regions.
* `QuantumCircuit.Party.Sheet.birthEquivP`, `QuantumCircuit.Party.Sheet.birthEquivP'`,
  `QuantumCircuit.Party.Sheet.birthEquivQ`, `QuantumCircuit.Party.Sheet.birthEquivSelf`: the bases
  of `P∘` and `Q∘` around a birth.

## Main results

* `QuantumCircuit.Party.Sheet.configBirthOp_apply_changeOwner`,
  `QuantumCircuit.Party.Sheet.configBirthOp_apply_changeOwner_self`: the canonical map of a
  birth in the coordinates of the parties.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 13–18 (sheets) and
  94–96 (canonical site and sheet coordinates); the canonical map of a birth, Lemma 6.5,
  lines 413–426.
-/
open Matrix ManyBody

namespace QuantumCircuit.Party

namespace Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq P] (q : ℕ) (S : Sheet ι P)

/-- **The basis of a party read on a region.** If the sites owned by `p` are those satisfying
`a`, the basis of `p` is the configurations of these sites. -/
def regionEquiv (p : P) (a : ι → Prop) (h : ∀ x, S.owner x = p ↔ a x) :
    S.system q p ≃ ({x // a x} → Fin q) where
  toFun z v := z ⟨v.1, (mem_blockPreimage_singleton _).mpr ((h v.1).mpr v.2)⟩
  invFun c v := c ⟨v.1, (h v.1).mp ((mem_blockPreimage_singleton _).mp v.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The region coordinates of a basis element. -/
@[simp] theorem regionEquiv_apply (p : P) (a : ι → Prop) (h : ∀ x, S.owner x = p ↔ a x)
    (z : S.system q p) (v : {x // a x}) :
    S.regionEquiv q p a h z v = z ⟨v.1, (mem_blockPreimage_singleton _).mpr ((h v.1).mpr v.2)⟩ :=
  rfl

/-- The basis element of given region coordinates. -/
@[simp] theorem regionEquiv_symm_apply (p : P) (a : ι → Prop) (h : ∀ x, S.owner x = p ↔ a x)
    (c : {x // a x} → Fin q) (v : {x // x ∈ blockPreimage S.owner {p}}) :
    (S.regionEquiv q p a h).symm c v =
      c ⟨v.1, (h v.1).mp ((mem_blockPreimage_singleton _).mp v.2)⟩ :=
  rfl

/-- **The basis of a party read on two regions.** If the sites owned by `p` are those satisfying
`a` or `b`, never both, the basis of `p` is the pairs of configurations of the two regions. -/
def splitEquiv (p : P) (a b : ι → Prop) [DecidablePred a] (h : ∀ x, S.owner x = p ↔ a x ∨ b x)
    (hab : ∀ x, a x → ¬b x) : S.system q p ≃ ({x // a x} → Fin q) × ({x // b x} → Fin q) where
  toFun z := (fun v ↦ z ⟨v.1, (mem_blockPreimage_singleton _).mpr ((h v.1).mpr (Or.inl v.2))⟩,
    fun v ↦ z ⟨v.1, (mem_blockPreimage_singleton _).mpr ((h v.1).mpr (Or.inr v.2))⟩)
  invFun c v := if hv : a v.1 then c.1 ⟨v.1, hv⟩ else
    c.2 ⟨v.1, ((h v.1).mp ((mem_blockPreimage_singleton _).mp v.2)).resolve_left hv⟩
  left_inv z := by
    funext v
    by_cases hv : a v.1 <;> simp [hv]
  right_inv c := by
    refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
    · simp [v.2]
    · exact dite_eq_right fun h' ↦ hab v.1 h' v.2

/-- The coordinates on the first region. -/
@[simp] theorem splitEquiv_apply_fst (p : P) (a b : ι → Prop) [DecidablePred a]
    (h : ∀ x, S.owner x = p ↔ a x ∨ b x) (hab : ∀ x, a x → ¬b x) (z : S.system q p)
    (v : {x // a x}) :
    (S.splitEquiv q p a b h hab z).1 v =
      z ⟨v.1, (mem_blockPreimage_singleton _).mpr ((h v.1).mpr (Or.inl v.2))⟩ :=
  rfl

/-- The coordinates on the second region. -/
@[simp] theorem splitEquiv_apply_snd (p : P) (a b : ι → Prop) [DecidablePred a]
    (h : ∀ x, S.owner x = p ↔ a x ∨ b x) (hab : ∀ x, a x → ¬b x) (z : S.system q p)
    (v : {x // b x}) :
    (S.splitEquiv q p a b h hab z).2 v =
      z ⟨v.1, (mem_blockPreimage_singleton _).mpr ((h v.1).mpr (Or.inr v.2))⟩ :=
  rfl

variable {q}

/-- The equality of the bases of a party in two sheets in which it owns the same sites. -/
theorem system_eq_of_owner_iff {S' : Sheet ι P} {p : P} (h : ∀ x, S'.owner x = p ↔ S.owner x = p) :
    S'.system q p = S.system q p := by
  have hD : blockPreimage S'.owner {p} = blockPreimage S.owner {p} := by
    ext x
    simpa using h x
  simp only [system, blockSystem, hD]

/-- **The identification of equal bases is a relabelling of sites.** In two sheets in which a
party owns the same sites, reading a configuration of the first along the equality of the bases
is reading it site by site. -/
theorem cast_system_eq_regionEquiv {S' : Sheet ι P} {p : P}
    (h : ∀ x, S'.owner x = p ↔ S.owner x = p) (e : S'.system q p = S.system q p)
    (y : S'.system q p) :
    cast e y = (S.regionEquiv q p (S.owner · = p) fun _ ↦ Iff.rfl).symm
      (S'.regionEquiv q p (S.owner · = p) h y) := by
  have hD : blockPreimage S'.owner {p} = blockPreimage S.owner {p} := by
    ext x
    simpa using h x
  have key : ∀ (D D' : Finset ι) (hD : D' = D)
      (e : RegionConfig (fun _ : ι ↦ Fin q) D' = RegionConfig (fun _ : ι ↦ Fin q) D)
      (y : RegionConfig (fun _ : ι ↦ Fin q) D'), cast e y = fun v ↦ y ⟨v.1, hD ▸ v.2⟩ := by
    rintro D _ rfl e y
    rfl
  exact key _ _ hD e y

/-! ### Two sheets -/

section TwoSheets

variable (S₁ S₂ : Sheet ι P)

/-- The canonical coordinate of a site on the first of two sheets is read at its owner. -/
theorem twoConfigEquiv_fst_eq (y : Config fun p ↦ S₁.system q p × S₂.system q p) {x : ι} {p : P}
    (h : S₁.owner x = p) :
    (twoConfigEquiv q S₁ S₂ y).1 x = (y p).1 ⟨x, (mem_blockPreimage_singleton _).mpr h⟩ :=
  blockConfigEquiv_apply_of_eq S₁.owner (fun r ↦ (y r).1) h

/-- The canonical coordinate of a site on the second of two sheets is read at its owner. -/
theorem twoConfigEquiv_snd_eq (y : Config fun p ↦ S₁.system q p × S₂.system q p) {x : ι} {p : P}
    (h : S₂.owner x = p) :
    (twoConfigEquiv q S₁ S₂ y).2 x = (y p).2 ⟨x, (mem_blockPreimage_singleton _).mpr h⟩ :=
  blockConfigEquiv_apply_of_eq S₂.owner (fun r ↦ (y r).2) h

end TwoSheets

variable (q) in
/-- **The basis of a party owning every site outside `B`**, read on the sites of `B` it owns and
on the sites outside `B`. -/
def complSplitEquiv [DecidableEq ι] {B : Finset ι} {P₀ : P} (hU : ∀ x ∉ B, S.owner x = P₀) :
    S.system q P₀ ≃ ({x // x ∈ B ∧ S.owner x = P₀} → Fin q) × ComplConfig (fun _ : ι ↦ Fin q) B :=
  S.splitEquiv q P₀ (fun x ↦ x ∈ B ∧ S.owner x = P₀) (· ∉ B)
    (fun x ↦ ⟨fun h ↦ (em (x ∈ B)).imp (⟨·, h⟩) id, fun h ↦ h.elim And.right (hU x)⟩)
    fun _ h hB ↦ hB h.1

/-! ### The coordinates of a birth -/

section Birth

variable [DecidableEq ι] (S : Sheet ι P) {T : Finset ι} {P₀ Q : P}

/-- In a birth, the sites owned by `P∘` are those of `T` and of `U = (T ∪ E)ᶜ`. -/
theorem owner_eq_iff_of_birth (hTP : ∀ x ∈ T, S.owner x = P₀) (x : ι) :
    S.owner x = P₀ ↔ x ∈ T ∨ x ∉ T ∪ S.birthEnv P₀ := by
  by_cases hx : x ∈ T
  · simp [hx, hTP x hx]
  · simp [hx, mem_birthEnv]

/-- After a birth, the sites owned by `P∘` are those of `U = (T ∪ E)ᶜ`. -/
theorem changeOwner_owner_eq_self_iff (hQP : Q ≠ P₀) (x : ι) :
    (S.changeOwner T Q).owner x = P₀ ↔ x ∉ T ∪ S.birthEnv P₀ := by
  by_cases hx : x ∈ T
  · simp [changeOwner, hx, hQP]
  · simp [changeOwner, hx, mem_birthEnv]

omit [Fintype ι] [DecidableEq P] in
/-- After a birth, the sites owned by `Q∘` are those of `T` and those it owned before. -/
theorem changeOwner_owner_eq_iff (x : ι) :
    (S.changeOwner T Q).owner x = Q ↔ x ∈ T ∨ S.owner x = Q := by
  by_cases hx : x ∈ T <;> simp [changeOwner, hx]

omit [Fintype ι] [DecidableEq P] in
/-- In a birth, a party other than `P∘` and `Q∘` keeps its sites. -/
theorem changeOwner_owner_eq_iff_of_ne (hTP : ∀ x ∈ T, S.owner x = P₀) {r : P} (hrQ : r ≠ Q)
    (hrP : r ≠ P₀) (x : ι) : (S.changeOwner T Q).owner x = r ↔ S.owner x = r := by
  by_cases hx : x ∈ T
  · simp [changeOwner, hx, hTP x hx, Ne.symm hrQ, Ne.symm hrP]
  · simp [changeOwner, hx]

variable {S}

/-- The basis of `P∘` before a birth, read on `T` and `U`. -/
def birthEquivP (hTP : ∀ x ∈ T, S.owner x = P₀) :
    S.system q P₀ ≃ RegionConfig (fun _ : ι ↦ Fin q) T ×
      ComplConfig (fun _ : ι ↦ Fin q) (T ∪ S.birthEnv P₀) :=
  S.splitEquiv q P₀ (· ∈ T) (· ∉ T ∪ S.birthEnv P₀) (S.owner_eq_iff_of_birth hTP)
    fun _ hx hU ↦ hU (Finset.mem_union_left _ hx)

/-- The basis of `P∘` after a birth, read on `U`. -/
def birthEquivP' (hQP : Q ≠ P₀) :
    (S.changeOwner T Q).system q P₀ ≃ ComplConfig (fun _ : ι ↦ Fin q) (T ∪ S.birthEnv P₀) :=
  (S.changeOwner T Q).regionEquiv q P₀ (· ∉ T ∪ S.birthEnv P₀)
    (S.changeOwner_owner_eq_self_iff hQP)

/-- The basis of `Q∘` after a birth, read on `T` and on the sites it owned before. -/
def birthEquivQ (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀) :
    (S.changeOwner T Q).system q Q ≃ RegionConfig (fun _ : ι ↦ Fin q) T × S.system q Q :=
  ((S.changeOwner T Q).splitEquiv q Q (· ∈ T) (S.owner · = Q) S.changeOwner_owner_eq_iff
      fun x hx hQ ↦ hQP (hQ.symm.trans (hTP x hx))).trans
    (Equiv.prodCongr (Equiv.refl _) (S.regionEquiv q Q (S.owner · = Q) fun _ ↦ Iff.rfl).symm)

/-- In a birth, the configurations before and after agree at a party other than `P∘` and `Q∘`
when they agree on the sites it owns. -/
theorem cast_changeOwner_system_iff (hTP : ∀ x ∈ T, S.owner x = P₀) {r : P} (hrQ : r ≠ Q)
    (hrP : r ≠ P₀) (y : Config ((S.changeOwner T Q).system q)) (x : Config (S.system q))
    (e₁ : (S.changeOwner T Q).system q r = S.system q r) :
    cast e₁ (y r) = x r ↔ ∀ v, S.owner v = r →
      blockConfigEquiv (S.changeOwner T Q).owner (fun _ ↦ Fin q) y v =
        blockConfigEquiv S.owner (fun _ ↦ Fin q) x v := by
  have hown := S.changeOwner_owner_eq_iff_of_ne hTP hrQ hrP
  rw [cast_system_eq_regionEquiv S hown, Equiv.symm_apply_eq, funext_iff]
  refine ⟨fun h v hv ↦ ?_, fun h v ↦ ?_⟩
  · rw [blockConfigEquiv_apply_of_eq (S.changeOwner T Q).owner y ((hown v).mpr hv),
      blockConfigEquiv_apply_of_eq S.owner x hv]
    exact h ⟨v, hv⟩
  · have := h v.1 v.2
    rwa [blockConfigEquiv_apply_of_eq (S.changeOwner T Q).owner y ((hown v).mpr v.2),
      blockConfigEquiv_apply_of_eq S.owner x v.2] at this

/-- A site of `E ∖ T`, the middle region of the cut of a birth, is a site not owned by `P∘`. -/
theorem mem_sdiff_birthEnv_iff (hTP : ∀ x ∈ T, S.owner x = P₀) (v : ι) :
    v ∈ (T ∪ S.birthEnv P₀) \ T ↔ S.owner v ≠ P₀ := by
  constructor
  · intro hv
    obtain ⟨hvB, hvT⟩ := Finset.mem_sdiff.mp hv
    exact (S.mem_birthEnv).mp ((Finset.mem_union.mp hvB).resolve_left hvT)
  · intro hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ ((S.mem_birthEnv).mpr hv),
      fun hT ↦ hv (hTP v hT)⟩

/-- **The canonical map of a birth in the coordinates of the parties.** Its entry between a
configuration after the birth and one before is `Kᴴ K` between their parts on `T` and `U`, read
at `Q∘` and `P∘`, when the two configurations agree on the sites of the other parties and on the
sites `Q∘` owned before. Source: `05-frames.tex`, lines 413–426. -/
theorem configBirthOp_apply_changeOwner [Fintype P] (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀))
    (y : Config ((S.changeOwner T Q).system q)) (x : Config (S.system q)) :
    configBirthOp Finset.subset_union_left σ
        (blockConfigEquiv (S.changeOwner T Q).owner (fun _ ↦ Fin q) y)
        (blockConfigEquiv S.owner (fun _ ↦ Fin q) x) =
      (if (birthEquivQ hTP hQP (y Q)).2 = x Q ∧ ∀ r ∈ (Finset.univ.erase Q).erase P₀, ∀ v,
          S.owner v = r → blockConfigEquiv (S.changeOwner T Q).owner (fun _ ↦ Fin q) y v =
            blockConfigEquiv S.owner (fun _ ↦ Fin q) x v then 1 else 0) *
        ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)
          ((birthEquivQ hTP hQP (y Q)).1, birthEquivP' hQP (y P₀)) (birthEquivP hTP (x P₀)) := by
  set c' := blockConfigEquiv (S.changeOwner T Q).owner (fun _ ↦ Fin q) y
  set c := blockConfigEquiv S.owner (fun _ ↦ Fin q) x
  have hc' : ∀ v (r : P) (hv : (S.changeOwner T Q).owner v = r),
      c' v = y r ⟨v, (mem_blockPreimage_singleton _).mpr hv⟩ := fun v r hv ↦
    blockConfigEquiv_apply_of_eq (S.changeOwner T Q).owner y hv
  have hcx : ∀ v (r : P) (hv : S.owner v = r),
      c v = x r ⟨v, (mem_blockPreimage_singleton _).mpr hv⟩ :=
    fun v r hv ↦ blockConfigEquiv_apply_of_eq S.owner x hv
  rw [configBirthOp, submatrix_apply, birthOp_eq_submatrix, submatrix_apply, kroneckerMap_apply]
  congr 1
  · rw [one_apply]
    refine if_congr ?_ rfl rfl
    have hQx : (birthEquivQ hTP hQP (y Q)).2 = x Q ↔ ∀ v, S.owner v = Q → c' v = c v := by
      rw [birthEquivQ, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd,
        Equiv.symm_apply_eq, funext_iff]
      refine ⟨fun h v hv ↦ ?_, fun h v ↦ ?_⟩
      · rw [hc' v Q ((S.changeOwner_owner_eq_iff v).mpr (Or.inr hv)), hcx v Q hv]
        exact h ⟨v, hv⟩
      · have := h v.1 v.2
        rwa [hc' v Q ((S.changeOwner_owner_eq_iff v).mpr (Or.inr v.2)), hcx v Q v.2] at this
    have hmem := mem_sdiff_birthEnv_iff hTP (S := S)
    change (threeCutEquiv _ Finset.subset_union_left c').1.2 =
      (threeCutEquiv _ Finset.subset_union_left c).1.2 ↔ _
    rw [funext_iff, hQx]
    simp only [threeCutEquiv_apply_fst_snd]
    constructor
    · intro h
      refine ⟨fun v hv ↦ h ⟨v, (hmem v).mpr (hv ▸ hQP)⟩, fun r hr v hv ↦ ?_⟩
      exact h ⟨v, (hmem v).mpr (hv ▸ (Finset.mem_erase.mp hr).1)⟩
    · rintro ⟨h₁, h₂⟩ ⟨v, hv⟩
      by_cases hvQ : S.owner v = Q
      · exact h₁ v hvQ
      · exact h₂ (S.owner v) (Finset.mem_erase.mpr ⟨(hmem v).mp hv,
          Finset.mem_erase.mpr ⟨hvQ, Finset.mem_univ _⟩⟩) v rfl
  · have h₁ : (teuShuffle _ _ _ (threeCutEquiv (fun _ : ι ↦ Fin q)
        (Finset.subset_union_left (s₂ := S.birthEnv P₀)) c')).2 =
        ((birthEquivQ hTP hQP (y Q)).1, birthEquivP' hQP (y P₀)) := by
      refine Prod.ext ?_ ?_
      · funext v
        exact hc' v Q (by simp [changeOwner, v.2])
      · funext v
        exact hc' v P₀ ((S.changeOwner_owner_eq_self_iff hQP v).mpr v.2)
    have h₂ : (teuShuffle _ _ _ (threeCutEquiv (fun _ : ι ↦ Fin q)
        (Finset.subset_union_left (s₂ := S.birthEnv P₀)) c)).2 = birthEquivP hTP (x P₀) := by
      refine Prod.ext ?_ ?_
      · funext v
        exact hcx v P₀ (hTP v v.2)
      · funext v
        exact hcx v P₀ ((S.owner_eq_iff_of_birth hTP v).mpr (Or.inr v.2))
    rw [h₁, h₂]

/-- In a birth at the same party, the sites owned by `P∘` afterwards are those of `T` and of
`U = (T ∪ E)ᶜ`. -/
theorem changeOwner_self_owner_eq_iff (S : Sheet ι P) (x : ι) :
    (S.changeOwner T P₀).owner x = P₀ ↔ x ∈ T ∨ x ∉ T ∪ S.birthEnv P₀ := by
  by_cases hx : x ∈ T
  · simp [changeOwner, hx]
  · simp [changeOwner, hx, mem_birthEnv]

/-- The basis of `P∘` after a birth at the same party, read on `T` and `U`. -/
def birthEquivSelf (S : Sheet ι P) (T : Finset ι) (P₀ : P) :
    (S.changeOwner T P₀).system q P₀ ≃ RegionConfig (fun _ : ι ↦ Fin q) T ×
      ComplConfig (fun _ : ι ↦ Fin q) (T ∪ S.birthEnv P₀) :=
  (S.changeOwner T P₀).splitEquiv q P₀ (· ∈ T) (· ∉ T ∪ S.birthEnv P₀)
    S.changeOwner_self_owner_eq_iff fun _ hx hU ↦ hU (Finset.mem_union_left _ hx)

/-- **The canonical map of a birth at the same party in the coordinates of the parties**: `Kᴴ K`
between the parts on `T` and `U` read at `P∘`, when the two configurations agree on the sites of
the other parties. Source: `05-frames.tex`, lines 421–426 and 445–446. -/
theorem configBirthOp_apply_changeOwner_self [Fintype P] (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀))
    (y : Config ((S.changeOwner T P₀).system q)) (x : Config (S.system q)) :
    configBirthOp Finset.subset_union_left σ
        (blockConfigEquiv (S.changeOwner T P₀).owner (fun _ ↦ Fin q) y)
        (blockConfigEquiv S.owner (fun _ ↦ Fin q) x) =
      (if ∀ r ∈ Finset.univ.erase P₀, ∀ v, S.owner v = r →
          blockConfigEquiv (S.changeOwner T P₀).owner (fun _ ↦ Fin q) y v =
            blockConfigEquiv S.owner (fun _ ↦ Fin q) x v then 1 else 0) *
        ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s) (S.birthEquivSelf T P₀ (y P₀))
          (birthEquivP hTP (x P₀)) := by
  set c' := blockConfigEquiv (S.changeOwner T P₀).owner (fun _ ↦ Fin q) y
  set c := blockConfigEquiv S.owner (fun _ ↦ Fin q) x
  have hc' : ∀ v (r : P) (hv : (S.changeOwner T P₀).owner v = r),
      c' v = y r ⟨v, (mem_blockPreimage_singleton _).mpr hv⟩ := fun v r hv ↦
    blockConfigEquiv_apply_of_eq (S.changeOwner T P₀).owner y hv
  have hcx : ∀ v (r : P) (hv : S.owner v = r),
      c v = x r ⟨v, (mem_blockPreimage_singleton _).mpr hv⟩ :=
    fun v r hv ↦ blockConfigEquiv_apply_of_eq S.owner x hv
  rw [configBirthOp, submatrix_apply, birthOp_eq_submatrix, submatrix_apply, kroneckerMap_apply]
  congr 1
  · rw [one_apply]
    refine if_congr ?_ rfl rfl
    have hmem := mem_sdiff_birthEnv_iff hTP (S := S)
    change (threeCutEquiv _ Finset.subset_union_left c').1.2 =
      (threeCutEquiv _ Finset.subset_union_left c).1.2 ↔ _
    rw [funext_iff]
    simp only [threeCutEquiv_apply_fst_snd]
    constructor
    · intro h r hr v hv
      exact h ⟨v, (hmem v).mpr (hv ▸ (Finset.mem_erase.mp hr).1)⟩
    · intro h v
      exact h (S.owner v) (Finset.mem_erase.mpr ⟨(hmem v).mp v.2, Finset.mem_univ _⟩) v rfl
  · have h₁ : (teuShuffle _ _ _ (threeCutEquiv (fun _ : ι ↦ Fin q)
        (Finset.subset_union_left (s₂ := S.birthEnv P₀)) c')).2 = S.birthEquivSelf T P₀ (y P₀) := by
      refine Prod.ext ?_ ?_
      · funext v
        exact hc' v P₀ ((S.changeOwner_self_owner_eq_iff v).mpr (Or.inl v.2))
      · funext v
        exact hc' v P₀ ((S.changeOwner_self_owner_eq_iff v).mpr (Or.inr v.2))
    have h₂ : (teuShuffle _ _ _ (threeCutEquiv (fun _ : ι ↦ Fin q)
        (Finset.subset_union_left (s₂ := S.birthEnv P₀)) c)).2 = birthEquivP hTP (x P₀) := by
      refine Prod.ext ?_ ?_
      · funext v
        exact hcx v P₀ (hTP v v.2)
      · funext v
        exact hcx v P₀ ((S.owner_eq_iff_of_birth hTP v).mpr (Or.inr v.2))
    rw [h₁, h₂]

end Birth

end Sheet

end QuantumCircuit.Party
