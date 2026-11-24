/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.Environment
import QICLean.Circuit.Party.Sheet.BirthDeath

/-!
# A birth with a prescribed environment

The central party can keep sites of the environment among its own sites. The
same pair source implements the birth. The local matrix on the central
party acts as the identity on the basis of those environmental sites.

Source: polynomial-PEPS, Lemma 6.5, `05-frames.tex`, lines 396–437.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [DecidableEq P]
  {q : ℕ} {S : Sheet ι P} {T E : Finset ι} {P₀ Q : P}

local notation "A" => RegionConfig (fun _ : ι ↦ Fin q) T
local notation "U" => ComplConfig (fun _ : ι ↦ Fin q) (T ∪ E)
local notation "VEnv" => ({x // x ∈ E ∧ S.owner x = P₀} → Fin q)
local notation "S'" => S.changeOwner T Q

variable (hTE : Disjoint T E) (hTP : ∀ x ∈ T, S.owner x = P₀)
  (hU : ∀ x ∉ T ∪ E, S.owner x = P₀) (hQP : Q ≠ P₀)

local notation "Z" => addPair (S.system q) hQP A A

private def environmentBirthInputEquiv :
    Z P₀ ≃ VEnv × (A × (A × U)) :=
  (addPairRight hQP A A).trans
    ((Equiv.refl A).prodCongr (birthEnvironmentEquiv hTE hTP hU)) |>.trans
    ((Equiv.prodAssoc A VEnv (A × U)).symm.trans (teuShuffle A VEnv (A × U)))

include hTP in
private theorem environmentBirth_eq_outside {r : P} (hrQ : r ≠ Q) (hrP : r ≠ P₀) :
    (S').system q r = Z r :=
  (system_eq_of_owner_iff S (S.changeOwner_owner_eq_iff_of_ne hTP hrQ hrP)).trans
    (addPair_of_ne hQP _ _ hrQ hrP).symm

/-- The local matrices of a birth, with the central party's environmental basis
left untouched. -/
noncomputable def environmentBirthFamily
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) (r : P) :
    Matrix ((S').system q r) (Z r) ℂ :=
  if hrQ : r = Q then
    cast (congrArg (fun s ↦ Matrix ((S').system q s) (Z s) ℂ) hrQ.symm)
      ((birthEquivQ hTP hQP).trans (addPairLeft hQP A A).symm).toPEquiv.toMatrix
  else if hrP : r = P₀ then
    cast (congrArg (fun s ↦ Matrix ((S').system q s) (Z s) ℂ) hrP.symm)
      (reindex (birthEnvironmentEquivAfter hTE hQP hU).symm
        (environmentBirthInputEquiv hTE hTP hU hQP).symm
        ((1 : Matrix VEnv VEnv ℂ) ⊗ₖ birthPartyMatrix σ.V σ.s))
  else (Equiv.cast (environmentBirth_eq_outside hTP hQP hrQ hrP)).toPEquiv.toMatrix

/-- The birth word for distinct parties prepares one pair source and then
applies the local matrices. -/
noncomputable def environmentBirthWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    Word (S.system q) ((S').system q) :=
  (Word.sourceAt hQP A A (WithLp.toLp 2 σ.s) (S.system q)).comp
    (PartyCircuit.localOps (environmentBirthFamily hTE hTP hU hQP σ))

/-- The birth word is allowed when its pair source and local matrices are
given by splitting data. -/
theorem isAllowed_environmentBirthWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentBirthWord hTE hTP hU hQP σ).IsAllowed := by
  refine Word.IsAllowed.comp (Word.isAllowed_sourceAt hQP _ _
    (EuclideanSpace.norm_toLp_eq_one_of_star_dotProduct σ.star_s) _) fun r ↦ ?_
  by_cases hrQ : r = Q
  · subst r
    rw [environmentBirthFamily, dite_eq_left rfl, cast_eq]
    exact l2_opNorm_toMatrix_toPEquiv_le _
  by_cases hrP : r = P₀
  · subst r
    rw [environmentBirthFamily, dite_eq_right hrQ, dite_eq_left rfl, cast_eq]
    let : DecidableEq (VEnv × (A × (A × U))) := instDecidableEqProd
    exact (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_one_kronecker_le _).trans
      (norm_birthPartyMatrix_le_one σ.isIsometry σ.star_s))
  rw [environmentBirthFamily, dite_eq_right hrQ, dite_eq_right hrP]
  exact l2_opNorm_toMatrix_toPEquiv_le _

/-- The only parties acting in the word are the two parties of the birth. -/
theorem usesOnly_environmentBirthWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentBirthWord hTE hTP hU hQP σ).UsesOnly {P₀, Q} := by
  refine ⟨fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr ⊢
    tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hr
    refine ⟨environmentBirth_eq_outside hTP hQP hr.2 hr.1, fun y x ↦ ?_⟩
    rw [environmentBirthFamily, dite_eq_right hr.2, dite_eq_right hr.1]
    simp [PEquiv.toMatrix_apply]

/-- The word prepares a single pair source. -/
theorem sourceCount_environmentBirthWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentBirthWord hTE hTP hU hQP σ).sourceCount = 1 :=
  rfl

include hTE hTP hU hQP in
private theorem configBirthOp_apply_environment
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E))
    (y : Config ((S').system q)) (x : Config (S.system q)) :
    configBirthOp Finset.subset_union_left σ
        (blockConfigEquiv (S').owner (fun _ ↦ Fin q) y)
        (blockConfigEquiv S.owner (fun _ ↦ Fin q) x) =
      (if ∀ v ∈ E, blockConfigEquiv (S').owner (fun _ ↦ Fin q) y v =
          blockConfigEquiv S.owner (fun _ ↦ Fin q) x v then 1 else 0) *
        ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)
          ((birthEquivQ hTP hQP (y Q)).1,
            (birthEnvironmentEquivAfter hTE hQP hU (y P₀)).2)
          (birthEnvironmentEquiv hTE hTP hU (x P₀)).2 := by
  let c' := blockConfigEquiv (S').owner (fun _ ↦ Fin q) y
  let c := blockConfigEquiv S.owner (fun _ ↦ Fin q) x
  rw [configBirthOp, submatrix_apply, birthOp_eq_submatrix, submatrix_apply, kroneckerMap_apply]
  congr 1
  · rw [one_apply]
    refine if_congr ?_ rfl rfl
    change (threeCutEquiv _ Finset.subset_union_left c').1.2 =
      (threeCutEquiv _ Finset.subset_union_left c).1.2 ↔ _
    rw [funext_iff]
    simp only [threeCutEquiv_apply_fst_snd]
    constructor
    · intro h v hv
      exact h ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hv,
        fun ht ↦ Finset.disjoint_left.mp hTE ht hv⟩⟩
    · intro h v
      obtain ⟨hv, ht⟩ := Finset.mem_sdiff.mp v.2
      exact h v (Finset.mem_union.mp hv |>.resolve_left ht)
  · have hy : (teuShuffle _ _ _ (threeCutEquiv (fun _ : ι ↦ Fin q)
        (Finset.subset_union_left (s₂ := E)) c')).2 =
        ((birthEquivQ hTP hQP (y Q)).1,
          (birthEnvironmentEquivAfter hTE hQP hU (y P₀)).2) := by
      refine Prod.ext ?_ ?_
      · funext v
        exact blockConfigEquiv_apply_of_eq (S').owner y (by simp [changeOwner, v.2])
      · funext v
        exact blockConfigEquiv_apply_of_eq (S').owner y (by
          have ht : (v : ι) ∉ T := fun ht ↦ v.2 (Finset.mem_union_left _ ht)
          simpa [changeOwner, ht] using hU v v.2)
    have hx : (teuShuffle _ _ _ (threeCutEquiv (fun _ : ι ↦ Fin q)
        (Finset.subset_union_left (s₂ := E)) c)).2 =
        (birthEnvironmentEquiv hTE hTP hU (x P₀)).2 := by
      refine Prod.ext ?_ ?_
      · funext v
        exact blockConfigEquiv_apply_of_eq S.owner x (hTP v v.2)
      · funext v
        exact blockConfigEquiv_apply_of_eq S.owner x (hU v v.2)
    rw [hy, hx]

/-- In the party bases, the distinct-party birth word is the canonical birth
operator with the prescribed environment. Source: polynomial-PEPS, Lemma 6.5,
`05-frames.tex`, lines 420–426. -/
theorem op_environmentBirthWord [Fintype P]
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentBirthWord hTE hTP hU hQP σ).op =
      reindex (blockConfigEquiv (S').owner (fun _ ↦ Fin q)).symm
        (blockConfigEquiv S.owner (fun _ ↦ Fin q)).symm
        (configBirthOp Finset.subset_union_left σ) := by
  ext y x
  rw [environmentBirthWord, Word.op_comp, show
    Word.op (PartyCircuit.localOps (environmentBirthFamily hTE hTP hU hQP σ)) =
      piKronecker (environmentBirthFamily hTE hTP hU hQP σ) from PartyCircuit.op_localOps _ _,
    Word.op_sourceAt, reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.symm_symm,
    mul_apply, ← (addPairConfigEquiv hQP A A).symm.sum_comp, Fintype.sum_prod_type]
  simp only [prepMatrix_apply, Equiv.apply_symm_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, piKronecker_apply]
  rw [configBirthOp_apply_environment hTE hTP hU hQP σ y x]
  let c' := blockConfigEquiv (S').owner (fun _ ↦ Fin q) y
  let c := blockConfigEquiv S.owner (fun _ ↦ Fin q) x
  let e := addPairConfigEquiv (X := S.system q) hQP A A
  let u' := birthEnvironmentEquivAfter hTE hQP hU (y P₀)
  let u := birthEnvironmentEquiv hTE hTP hU (x P₀)
  let z := birthEquivQ hTP hQP (y Q)
  let f := environmentBirthFamily hTE hTP hU hQP σ
  have hQ (ab : A × A) :
      f Q (y Q) (e.symm (ab, x) Q) = if z = (ab.1, x Q) then 1 else 0 := by
    dsimp only [f, e]
    rw [environmentBirthFamily, dite_eq_left rfl, cast_eq, addPairConfigEquiv_symm_apply_left]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.trans_apply, ← Equiv.eq_symm_apply, Equiv.symm_symm, Equiv.apply_symm_apply, z]
  have hP (ab : A × A) :
      f P₀ (y P₀) (e.symm (ab, x) P₀) =
        (if u'.1 = u.1 then 1 else 0) * birthPartyMatrix σ.V σ.s u'.2 (ab.2, u.2) := by
    dsimp only [f, e]
    rw [environmentBirthFamily, dite_eq_right (Ne.symm hQP), dite_eq_left rfl, cast_eq,
      addPairConfigEquiv_symm_apply_right]
    simp [reindex_apply, submatrix_apply, kroneckerMap_apply, environmentBirthInputEquiv,
      u, u', Matrix.one_apply, teuShuffle]
  have hR (ab : A × A) (r : P) (hr : r ∈ (Finset.univ.erase Q).erase P₀) :
      f r (y r) (e.symm (ab, x) r) =
        if ∀ v, S.owner v = r → c' v = c v then 1 else 0 := by
    have hrP : r ≠ P₀ := (Finset.mem_erase.mp hr).1
    have hrQ : r ≠ Q := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    dsimp only [f, e]
    rw [environmentBirthFamily, dite_eq_right hrQ, dite_eq_right hrP,
      addPairConfigEquiv_symm_apply_of_ne _ _ _ _ hrQ hrP]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.cast_apply]
    have e₁ := system_eq_of_owner_iff (q := q) S (S.changeOwner_owner_eq_iff_of_ne hTP hrQ hrP)
    have hcast (h₁ : (S').system q r = Z r) (h₂ : S.system q r = Z r) :
        cast h₁ (y r) = cast h₂ (x r) ↔ cast e₁ (y r) = x r := by
      rw [show cast h₁ (y r) = cast h₂ (cast e₁ (y r)) from (cast_cast e₁ h₂ (y r)).symm,
        cast_inj]
    exact if_congr ((hcast _ _).trans (cast_changeOwner_system_iff hTP hrQ hrP y x e₁))
      rfl rfl
  let D := ∀ r ∈ (Finset.univ.erase Q).erase P₀, ∀ v, S.owner v = r → c' v = c v
  have hprod (ab : A × A) :
      (∏ k, f k (y k) (e.symm (ab, x) k)) =
        (if z = (ab.1, x Q) then 1 else 0) *
          ((if u'.1 = u.1 then 1 else 0) * birthPartyMatrix σ.V σ.s u'.2 (ab.2, u.2) *
            (if D then 1 else 0)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ Q),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hQP, Finset.mem_univ P₀⟩),
      hQ, hP, Finset.prod_congr rfl (hR ab), Finset.prod_boole]
    congr 2
    split_ifs <;> rfl
  change (∑ ab : A × A, (∏ k, f k (y k) (e.symm (ab, x) k)) * σ.s ab) = _
  simp only [hprod]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single z.1 fun t ht ↦
    Finset.sum_eq_zero fun b _ ↦ by rw [ite_eq_right fun h ↦ ht (congrArg Prod.fst h).symm]; ring]
  have hc : z = (z.1, x Q) ↔ z.2 = x Q := by simp [Prod.ext_iff]
  have hQx : z.2 = x Q ↔ ∀ v, S.owner v = Q → c' v = c v := by
    simp only [z, birthEquivQ, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_snd,
      Equiv.symm_apply_eq, funext_iff]
    constructor
    · intro h v hv
      dsimp only [c', c]
      rw [blockConfigEquiv_apply_of_eq (S').owner y
        ((S.changeOwner_owner_eq_iff v).mpr (Or.inr hv)),
        blockConfigEquiv_apply_of_eq S.owner x hv]
      exact h ⟨v, hv⟩
    · intro h v
      exact (blockConfigEquiv_apply_of_eq (S').owner y
        ((S.changeOwner_owner_eq_iff v).mpr (Or.inr v.2))).symm.trans
        ((h v v.2).trans (blockConfigEquiv_apply_of_eq S.owner x v.2))
  have hPx : u'.1 = u.1 ↔ ∀ v ∈ E, S.owner v = P₀ → c' v = c v := by
    have hy (v : ι) (hE : v ∈ E) (hv : S.owner v = P₀) :
        c' v = u'.1 ⟨v, hE, hv⟩ := by
      have ht : v ∉ T := fun ht ↦ Finset.disjoint_left.mp hTE ht hE
      exact blockConfigEquiv_apply_of_eq (S').owner y (by simpa [changeOwner, ht] using hv)
    have hx (v : ι) (hE : v ∈ E) (hv : S.owner v = P₀) :
        c v = u.1 ⟨v, hE, hv⟩ :=
      blockConfigEquiv_apply_of_eq S.owner x hv
    constructor
    · intro h v hE hv
      rw [hy v hE hv, hx v hE hv, h]
    · intro h
      funext v
      rw [← hy v v.2.1 v.2.2, ← hx v v.2.1 v.2.2]
      exact h v v.2.1 v.2.2
  have hE : (∀ v ∈ E, c' v = c v) ↔ z.2 = x Q ∧ u'.1 = u.1 ∧ D := by
    rw [hQx, hPx]
    have mem (v : ι) (hv : S.owner v ≠ P₀) : v ∈ E := by
      by_contra hn
      have ht : v ∉ T := fun ht ↦ hv (hTP v ht)
      exact hv (hU v (by simp [hn, ht]))
    constructor
    · intro h
      exact ⟨fun v hv ↦ h v (mem v (hv ▸ hQP)), fun v hv _ ↦ h v hv,
        fun r hr v hv ↦ h v (mem v (hv ▸ (Finset.mem_erase.mp hr).1))⟩
    · rintro ⟨h₁, h₂, h₃⟩ v hv
      by_cases hvQ : S.owner v = Q
      · exact h₁ v hvQ
      by_cases hvP : S.owner v = P₀
      · exact h₂ v hv hvP
      · exact h₃ (S.owner v) (by simp [hvQ, hvP]) v rfl
  rw [if_congr hE rfl rfl, ← sum_birthPartyMatrix_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [if_congr hc rfl rfl, ite_and, ite_and]
  by_cases ha : z.2 = x Q <;> by_cases hb : u'.1 = u.1 <;> by_cases hd : D <;>
    simp only [ha, hb, hd, ↓reduceIte] <;> ring

end QuantumCircuit.Party.Sheet
