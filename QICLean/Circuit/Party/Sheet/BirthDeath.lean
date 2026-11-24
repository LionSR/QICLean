/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.Placement
import QICLean.Circuit.Party.Syntax.Word
import QICLean.ManyBody.Sites.ThreeRegion.SwapCorrection

/-!
# Births and deaths of a sheet between two parties

Lemma 6.5 of the polynomial-PEPS manuscript asserts that a homogeneous birth is a bounded change
involving only `P∘` and `Q∘`. Let `T` be owned by `P∘`, `E` the sites not owned by `P∘` and
`U = Λ ∖ (T ∪ E)`, and let splitting data `σ` give an isometry `V` from `U` to `B_T B_E` and a
unit vector `s` on `T B_T`. The birth supplies the normalized pair state `s` on a fresh copy of
`T` held by `Q∘` and a fresh `B_T` held by `P∘`, and then applies at `P∘` the contraction
`Vᴴ (1_{B_T} ⊗ K)` with `K = ⟨s| (1_T ⊗ V)` from `B_T`, `T` and `U` to `U`; the copy of `T` held
by `P∘` before the birth leaves `P∘`. The manuscript applies the contraction `⟨s| (1_T ⊗ V)`
before the pair source; it acts on other factors than the source, so here it is applied with
`Vᴴ` after it. The operator of the word, read in the canonical coordinates of the two sheets, is
the canonical map `𝐁 = 1_E ⊗ Kᴴ K` of the splitting data (`Sheet.op_birthWord`).

The death runs the other way: at `Q∘` the copy of `T` leaves its sites, at `P∘` the contraction
`(1_{B_T} ⊗ Kᴴ) V` is applied, and the normalized pair effect `⟨s|` on the copy of `T` and on
`B_T` ends it; its operator is again `𝐁` (`Sheet.op_deathChain`). The case `Q∘ = P∘` is in
`Sheet/PrivateBirthDeath`.

## Main definitions

* `QuantumCircuit.Party.Sheet.birthWord`, `QuantumCircuit.Party.Sheet.deathChain`.

## Main results

* `QuantumCircuit.Party.Sheet.op_birthWord`, `QuantumCircuit.Party.Sheet.isAllowed_birthWord`,
  `QuantumCircuit.Party.Sheet.usesOnly_birthWord`,
  `QuantumCircuit.Party.Sheet.sourceCount_birthWord`.
* `QuantumCircuit.Party.Sheet.op_deathChain`, `QuantumCircuit.Party.Sheet.isAllowed_deathChain`,
  `QuantumCircuit.Party.Sheet.usesOnly_deathChain`,
  `QuantumCircuit.Party.Sheet.forallGate_isRight_deathChain`,
  `QuantumCircuit.Party.Sheet.numGates_deathChain`.
* `QuantumCircuit.Party.Sheet.norm_birthPartyMatrix_le_one`,
  `QuantumCircuit.Party.Sheet.sum_birthPartyMatrix_mul`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.5 `lem:birth`, `05-frames.tex`,
  lines 396–447; allowed monomials, `04-compression.tex`, lines 32–35.
* One-dimensional note, Lemma `lem:birth`, `part2b_mps_protocol.tex`, lines 70–94.
-/

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

namespace Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] {q : ℕ}

/-! ### The kernel of a birth -/

section Kernel

variable {T U BT BE : Type} [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U]
  [Fintype BT] [DecidableEq BT] [Fintype BE] [DecidableEq BE]

/-- The contraction applied at `P∘` in a birth after the pair source: `Vᴴ (1_{B_T} ⊗ K)`.
Source: `05-frames.tex`, lines 416–420. -/
noncomputable def birthPartyMatrix (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) :
    Matrix U (BT × (T × U)) ℂ :=
  Vᴴ * ((1 : Matrix BT BT ℂ) ⊗ₖ birthKernel V s)

omit [DecidableEq BE] in
/-- The contraction of a birth at `P∘` is a contraction. -/
theorem norm_birthPartyMatrix_le_one {V : Matrix (BT × BE) U ℂ} (hV : V.IsIsometry)
    {s : T × BT → ℂ} (hs : star s ⬝ᵥ s = 1) : ‖birthPartyMatrix V s‖ ≤ 1 := by
  classical
  exact l2_opNorm_mul_le_one _ _ ((l2_opNorm_conjTranspose V).trans_le hV.l2_opNorm_le_one)
    ((l2_opNorm_one_kronecker_le _).trans (norm_birthKernel_le_one hV hs))

omit [Fintype T] [DecidableEq T] [Fintype U] [DecidableEq U] [DecidableEq BE] in
/-- **Preparing `s` and applying the contraction gives `Kᴴ K`.** Summed against the prepared
vector `s` at the first copy `t'` of `T`, the contraction at `P∘` is `Kᴴ K`. -/
theorem sum_birthPartyMatrix_mul (V : Matrix (BT × BE) U ℂ) (s : T × BT → ℂ) (t' : T) (u : U)
    (tu : T × U) :
    ∑ b, birthPartyMatrix V s u (b, tu) * s (t', b) =
      ((birthKernel V s)ᴴ * birthKernel V s) (t', u) tu := by
  have hl : ∀ b, birthPartyMatrix V s u (b, tu) =
      ∑ be, star (V (b, be) u) * birthKernel V s be tu := fun b ↦ by
    simp only [birthPartyMatrix, mul_apply, conjTranspose_apply, kroneckerMap_apply,
      Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single b fun b' hb ↦ by simp [one_apply_ne hb]]
    simp
  simp only [hl, mul_apply, conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun be _ ↦ ?_
  simp only [birthKernel, of_apply, star_sum, star_mul, star_star, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

end Kernel

/-! ### The birth -/

section Birth

variable {S : Sheet ι P} {T : Finset ι} {P₀ Q : P}

omit [Fintype P] in
/-- In a birth, a party other than `P∘` and `Q∘` has after the birth the basis it has in the
system with a fresh pair of factors added at `Q∘` and `P∘`. -/
private theorem birth_system_eq (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀) {r : P}
    (hrQ : r ≠ Q) (hrP : r ≠ P₀) :
    (S.changeOwner T Q).system q r =
      addPair (S.system q) hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T) r :=
  (system_eq_of_owner_iff S (S.changeOwner_owner_eq_iff_of_ne hTP hrQ hrP)).trans
    (addPair_of_ne hQP _ _ hrQ hrP).symm

/-- **The local operations of a birth after the pair source**: at `Q∘` the new copy of `T`
joins its sites, at `P∘` the contraction `Vᴴ (1_{B_T} ⊗ K)`, and the identity elsewhere. -/
noncomputable def birthFamily (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) (s : P) :
    Matrix ((S.changeOwner T Q).system q s)
      (addPair (S.system q) hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T) s) ℂ :=
  if hs : s = Q then cast (congrArg (fun r ↦ Matrix ((S.changeOwner T Q).system q r)
      (addPair (S.system q) hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T) r) ℂ) hs.symm) ((birthEquivQ hTP hQP).trans
    (addPairLeft hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
      (RegionConfig (fun _ : ι ↦ Fin q) T)).symm).toPEquiv.toMatrix
  else if hs' : s = P₀ then cast (congrArg (fun r ↦ Matrix ((S.changeOwner T Q).system q r)
      (addPair (S.system q) hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T) r) ℂ) hs'.symm)
    (reindex (birthEquivP' hQP).symm ((addPairRight hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T)).trans
          ((Equiv.refl _).prodCongr (birthEquivP hTP))).symm (birthPartyMatrix σ.V σ.s))
  else (Equiv.cast (birth_system_eq hTP hQP hs hs')).toPEquiv.toMatrix

/-- **The birth as a word** (Lemma 6.5, `Q∘ ≠ P∘`): the normalized pair source `s` on a fresh
copy of `T` at `Q∘` and a fresh `B_T` at `P∘`, then the local operations `birthFamily`.
Source: proof of Lemma 6.5, `05-frames.tex`, lines 414–420. -/
noncomputable def birthWord (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    Word (S.system q) ((S.changeOwner T Q).system q) :=
  PartyCircuit.comp (Word.sourceAt hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
      (RegionConfig (fun _ : ι ↦ Fin q) T) (WithLp.toLp 2 σ.s) (S.system q))
    (PartyCircuit.localOps (birthFamily hTP hQP σ))

/-- **The birth word in canonical coordinates** is the canonical map `𝐁` of the splitting
data. Source: `05-frames.tex`, lines 420–426. -/
theorem op_birthWord (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (birthWord hTP hQP σ).op =
      reindex (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
        (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) := by
  ext y x
  rw [birthWord, Word.op_comp, show Word.op (PartyCircuit.localOps (birthFamily hTP hQP σ)) =
      piKronecker (birthFamily hTP hQP σ) from PartyCircuit.op_localOps _ _, Word.op_sourceAt,
    reindex_apply,
    submatrix_apply, Equiv.symm_symm, Equiv.symm_symm, mul_apply,
    ← (addPairConfigEquiv hQP _ _).symm.sum_comp, Fintype.sum_prod_type]
  simp only [prepMatrix_apply, Equiv.apply_symm_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, piKronecker_apply]
  rw [configBirthOp_apply_changeOwner hTP hQP σ y x]
  set c' := blockConfigEquiv (S.changeOwner T Q).owner (fun _ ↦ Fin q) y
  set c := blockConfigEquiv S.owner (fun _ ↦ Fin q) x
  set e := addPairConfigEquiv (X := S.system q) hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
    (RegionConfig (fun _ : ι ↦ Fin q) T)
  -- the factor at `Q`
  have hQ : ∀ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
      birthFamily hTP hQP σ Q (y Q) (e.symm (ab, x) Q) =
        if birthEquivQ hTP hQP (y Q) = (ab.1, x Q) then 1 else 0 := fun ab ↦ by
    rw [birthFamily, dite_eq_left rfl, cast_eq, addPairConfigEquiv_symm_apply_left]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.trans_apply, ← Equiv.eq_symm_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  -- the factor at `P∘`
  have hP : ∀ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
      birthFamily hTP hQP σ P₀ (y P₀) (e.symm (ab, x) P₀) =
        birthPartyMatrix σ.V σ.s (birthEquivP' hQP (y P₀)) (ab.2, birthEquivP hTP (x P₀)) :=
    fun ab ↦ by
    rw [birthFamily, dite_eq_right (Ne.symm hQP), dite_eq_left rfl, cast_eq,
      addPairConfigEquiv_symm_apply_right]
    simp
  -- the factors elsewhere
  have hR : ∀ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
      ∀ r ∈ (Finset.univ.erase Q).erase P₀,
        birthFamily hTP hQP σ r (y r) (e.symm (ab, x) r) =
          if ∀ v, S.owner v = r → c' v = c v then 1 else 0 := fun ab r hr ↦ by
    have hrP : r ≠ P₀ := (Finset.mem_erase.mp hr).1
    have hrQ : r ≠ Q := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    rw [birthFamily, dite_eq_right hrQ, dite_eq_right hrP,
      addPairConfigEquiv_symm_apply_of_ne _ _ _ _ hrQ hrP]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.cast_apply]
    have e₁ := system_eq_of_owner_iff (q := q) S (S.changeOwner_owner_eq_iff_of_ne hTP hrQ hrP)
    have key : ∀ (h₁ : (S.changeOwner T Q).system q r = addPair (S.system q) hQP
        (RegionConfig (fun _ : ι ↦ Fin q) T) (RegionConfig (fun _ : ι ↦ Fin q) T) r)
        (h₂ : S.system q r = addPair (S.system q) hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
          (RegionConfig (fun _ : ι ↦ Fin q) T) r),
        cast h₁ (y r) = cast h₂ (x r) ↔ cast e₁ (y r) = x r := fun h₁ h₂ ↦ by
      rw [show cast h₁ (y r) = cast h₂ (cast e₁ (y r)) from (cast_cast e₁ h₂ (y r)).symm, cast_inj]
    exact if_congr ((key _ _).trans (cast_changeOwner_system_iff hTP hrQ hrP y x e₁)) rfl rfl
  -- the product over the parties
  have hprod : ∀ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
      ∏ k, birthFamily hTP hQP σ k (y k) (e.symm (ab, x) k) =
        (if birthEquivQ hTP hQP (y Q) = (ab.1, x Q) then 1 else 0) *
          (birthPartyMatrix σ.V σ.s (birthEquivP' hQP (y P₀)) (ab.2, birthEquivP hTP (x P₀)) *
            if ∀ r ∈ (Finset.univ.erase Q).erase P₀, ∀ v, S.owner v = r → c' v = c v then 1
            else 0) := fun ab ↦ by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ Q),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hQP, Finset.mem_univ P₀⟩),
      hQ, hP, Finset.prod_congr rfl (hR ab), Finset.prod_boole]
    congr 2
    split_ifs <;> rfl
  simp only [hprod]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single (birthEquivQ hTP hQP (y Q)).1 fun t ht ↦
    Finset.sum_eq_zero fun b _ ↦ by rw [ite_eq_right fun h ↦ ht (congrArg Prod.fst h).symm]; ring]
  have hc : birthEquivQ hTP hQP (y Q) = ((birthEquivQ hTP hQP (y Q)).1, x Q) ↔
      (birthEquivQ hTP hQP (y Q)).2 = x Q := by
    simp [Prod.ext_iff]
  rw [← sum_birthPartyMatrix_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [if_congr hc rfl rfl, ite_and]
  by_cases hA : (birthEquivQ hTP hQP (y Q)).2 = x Q <;>
    by_cases hB : ∀ r ∈ (Finset.univ.erase Q).erase P₀, ∀ v, S.owner v = r → c' v = c v <;>
    simp only [hA, hB, ↓reduceIte] <;> ring

omit [Fintype P] in
/-- The birth word is allowed: the pair source is normalized and the local operations are
contractions. -/
theorem isAllowed_birthWord (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (birthWord hTP hQP σ).IsAllowed := by
  refine Word.IsAllowed.comp (Word.isAllowed_sourceAt hQP _ _
    (EuclideanSpace.norm_toLp_eq_one_of_star_dotProduct σ.star_s) _) fun r ↦ ?_
  by_cases hrQ : r = Q
  · subst hrQ
    rw [birthFamily, dite_eq_left rfl, cast_eq]
    exact l2_opNorm_toMatrix_toPEquiv_le _
  by_cases hrP : r = P₀
  · subst hrP
    rw [birthFamily, dite_eq_right hrQ, dite_eq_left rfl, cast_eq]
    exact (l2_opNorm_reindex_le _ _ _).trans
      (norm_birthPartyMatrix_le_one σ.isIsometry σ.star_s)
  rw [birthFamily, dite_eq_right hrQ, dite_eq_right hrP]
  exact l2_opNorm_toMatrix_toPEquiv_le _

omit [Fintype P] in
/-- The birth word uses only `P∘` and `Q∘`. -/
theorem usesOnly_birthWord (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (birthWord hTP hQP σ).UsesOnly {P₀, Q} := by
  refine ⟨fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr ⊢
    tauto
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hr
    refine ⟨birth_system_eq hTP hQP hr.2 hr.1, fun y x ↦ ?_⟩
    rw [birthFamily, dite_eq_right hr.2, dite_eq_right hr.1]
    simp [PEquiv.toMatrix_apply]

omit [Fintype P] in
/-- The birth word has one pair source. -/
theorem sourceCount_birthWord (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (birthWord hTP hQP σ).sourceCount = 1 :=
  rfl

/-! ### The death -/

/-- **The local operations of a death before the pair effect**: at `Q∘` the copy of `T` leaves
its sites, at `P∘` the contraction `(1_{B_T} ⊗ Kᴴ) V`, and the identity elsewhere. -/
noncomputable def deathFamily (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) (s : P) :
    Matrix (addPair (S.system q) hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T) s) ((S.changeOwner T Q).system q s) ℂ :=
  if hs : s = Q then cast (congrArg (fun r ↦ Matrix (addPair (S.system q) hQP
      (RegionConfig (fun _ : ι ↦ Fin q) T) (RegionConfig (fun _ : ι ↦ Fin q) T) r)
        ((S.changeOwner T Q).system q r) ℂ) hs.symm) ((birthEquivQ hTP hQP).trans
    (addPairLeft hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
      (RegionConfig (fun _ : ι ↦ Fin q) T)).symm).symm.toPEquiv.toMatrix
  else if hs' : s = P₀ then cast (congrArg (fun r ↦ Matrix (addPair (S.system q) hQP
      (RegionConfig (fun _ : ι ↦ Fin q) T) (RegionConfig (fun _ : ι ↦ Fin q) T) r)
        ((S.changeOwner T Q).system q r) ℂ) hs'.symm)
    (reindex ((addPairRight hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T)).trans
          ((Equiv.refl _).prodCongr (birthEquivP hTP))).symm (birthEquivP' hQP).symm
      (birthPartyMatrix σ.V σ.s)ᴴ)
  else (Equiv.cast (birth_system_eq hTP hQP hs hs').symm).toPEquiv.toMatrix

/-- **The death as a circuit of local operations and one pair effect** (Lemma 6.5,
`Q∘ ≠ P∘`): from the sheet in which `T` is owned by `Q∘` to the sheet in which it is owned by
`P∘`, the local operations `deathFamily`, then the normalized pair effect `⟨s|` on the copy of
`T` at `Q∘` and on `B_T` at `P∘`. The contraction `Kᴴ` acts on other factors than the pair
effect, so it is applied before it. Source: proof of Lemma 6.5, `05-frames.tex`,
lines 439–444. -/
noncomputable def deathChain (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    PartyCircuit (ChainGate (P := P)) ((S.changeOwner T Q).system q) (S.system q) :=
  PartyCircuit.comp (PartyCircuit.localOps (deathFamily hTP hQP σ))
    (PartyCircuit.gate {Q, P₀} (PairEffectGate.ofAddPair hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T) (WithLp.toLp 2 σ.s) (S.system q)).outside
      (.inr (PairEffectGate.ofAddPair hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
        (RegionConfig (fun _ : ι ↦ Fin q) T) (WithLp.toLp 2 σ.s) (S.system q))))

/-- **The death chain in canonical coordinates** is the canonical map `𝐁` of the splitting
data. Source: `05-frames.tex`, lines 442–443. -/
theorem op_deathChain (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (deathChain hTP hQP σ).op chainEv =
      reindex (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) := by
  ext x y
  have hce : (PairEffectGate.ofAddPair hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
      (RegionConfig (fun _ : ι ↦ Fin q) T) (WithLp.toLp 2 σ.s) (S.system q)).configEquiv =
      addPairConfigEquiv hQP _ _ :=
    SourceGate.configEquiv_ofAddPair hQP _ _ _ _
  rw [deathChain, PartyCircuit.op_comp (P := P) (G := ChainGate), ChainGate.op_gate_inr,
    PartyCircuit.op_localOps, reindex_apply, submatrix_apply, Equiv.symm_symm,
    Equiv.symm_symm, mul_apply,
    ← (PairEffectGate.ofAddPair hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
      (RegionConfig (fun _ : ι ↦ Fin q) T) (WithLp.toLp 2 σ.s)
        (S.system q)).configEquiv.symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [submatrix_apply, id, effectMatrix_apply, Equiv.apply_symm_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, piKronecker_apply]
  rw [hce]
  rw [← (configBirthOp_isHermitian Finset.subset_union_left σ).apply,
    configBirthOp_apply_changeOwner hTP hQP σ y x]
  set c' := blockConfigEquiv (S.changeOwner T Q).owner (fun _ ↦ Fin q) y
  set c := blockConfigEquiv S.owner (fun _ ↦ Fin q) x
  set e := addPairConfigEquiv (X := S.system q) hQP (RegionConfig (fun _ : ι ↦ Fin q) T)
    (RegionConfig (fun _ : ι ↦ Fin q) T)
  have hQ : ∀ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
      deathFamily hTP hQP σ Q (e.symm (ab, x) Q) (y Q) =
        if birthEquivQ hTP hQP (y Q) = (ab.1, x Q) then 1 else 0 := fun ab ↦ by
    rw [deathFamily, dite_eq_left rfl, cast_eq, addPairConfigEquiv_symm_apply_left]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact if_congr ⟨fun h ↦ h ▸ (Equiv.apply_symm_apply _ _), fun h ↦ h ▸
      (Equiv.symm_apply_apply _ _)⟩ rfl rfl
  have hP : ∀ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
      deathFamily hTP hQP σ P₀ (e.symm (ab, x) P₀) (y P₀) =
        star (birthPartyMatrix σ.V σ.s (birthEquivP' hQP (y P₀)) (ab.2, birthEquivP hTP (x P₀))) :=
    fun ab ↦ by
    rw [deathFamily, dite_eq_right (Ne.symm hQP), dite_eq_left rfl, cast_eq,
      addPairConfigEquiv_symm_apply_right]
    simp
  have hR : ∀ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
      ∀ r ∈ (Finset.univ.erase Q).erase P₀,
        deathFamily hTP hQP σ r (e.symm (ab, x) r) (y r) =
          if ∀ v, S.owner v = r → c' v = c v then 1 else 0 := fun ab r hr ↦ by
    have hrP : r ≠ P₀ := (Finset.mem_erase.mp hr).1
    have hrQ : r ≠ Q := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    rw [deathFamily, dite_eq_right hrQ, dite_eq_right hrP,
      addPairConfigEquiv_symm_apply_of_ne _ _ _ _ hrQ hrP]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.cast_apply]
    have e₁ := system_eq_of_owner_iff (q := q) S (S.changeOwner_owner_eq_iff_of_ne hTP hrQ hrP)
    refine if_congr (Iff.trans ?_ (cast_changeOwner_system_iff hTP hrQ hrP y x e₁)) rfl rfl
    rw [cast_cast]
    constructor
    · intro h
      rw [← h, cast_cast, cast_eq]
    · intro h
      rw [← h, cast_cast, cast_eq]
  have hprod : ∀ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
      ∏ k, deathFamily hTP hQP σ k (e.symm (ab, x) k) (y k) =
        (if birthEquivQ hTP hQP (y Q) = (ab.1, x Q) then 1 else 0) *
          (star (birthPartyMatrix σ.V σ.s (birthEquivP' hQP (y P₀))
            (ab.2, birthEquivP hTP (x P₀))) *
            if ∀ r ∈ (Finset.univ.erase Q).erase P₀, ∀ v, S.owner v = r → c' v = c v then 1
            else 0) := fun ab ↦ by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ Q),
      ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hQP, Finset.mem_univ P₀⟩),
      hQ, hP, Finset.prod_congr rfl (hR ab), Finset.prod_boole]
    congr 2
    split_ifs <;> rfl
  change ∑ ab : RegionConfig (fun _ : ι ↦ Fin q) T × RegionConfig (fun _ : ι ↦ Fin q) T,
    star (σ.s ab) * _ = _
  refine (Finset.sum_congr rfl fun ab _ ↦ congrArg (star (σ.s ab) * ·) (hprod ab)).trans ?_
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single (birthEquivQ hTP hQP (y Q)).1 fun t ht ↦
    Finset.sum_eq_zero fun b _ ↦ by rw [ite_eq_right fun h ↦ ht (congrArg Prod.fst h).symm]; ring]
  have hc : birthEquivQ hTP hQP (y Q) = ((birthEquivQ hTP hQP (y Q)).1, x Q) ↔
      (birthEquivQ hTP hQP (y Q)).2 = x Q := by
    simp [Prod.ext_iff]
  rw [star_mul', ← sum_birthPartyMatrix_mul, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [if_congr hc rfl rfl, ite_and, star_mul']
  split_ifs <;> simp only [star_one, star_zero, mul_one, mul_zero, zero_mul, one_mul]
  ring

omit [Fintype P] in
/-- The death chain is allowed: the pair effect is normalized and the local operations are
contractions. -/
theorem isAllowed_deathChain (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (deathChain hTP hQP σ).IsAllowed chainEv ChainGate.IsAllowed := by
  have hη : ‖(WithLp.toLp 2 σ.s : EuclideanSpace ℂ (RegionConfig (fun _ : ι ↦ Fin q) T ×
      RegionConfig (fun _ : ι ↦ Fin q) T))‖ = 1 :=
    EuclideanSpace.norm_toLp_eq_one_of_star_dotProduct σ.star_s
  refine ⟨fun r ↦ ?_, (PairEffectGate.norm_ev_le _ ()).trans hη.le, hη⟩
  by_cases hrQ : r = Q
  · subst hrQ
    rw [deathFamily, dite_eq_left rfl, cast_eq]
    exact l2_opNorm_toMatrix_toPEquiv_le _
  by_cases hrP : r = P₀
  · subst hrP
    rw [deathFamily, dite_eq_right hrQ, dite_eq_left rfl, cast_eq]
    exact (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_conjTranspose _).trans_le
      (norm_birthPartyMatrix_le_one σ.isIsometry σ.star_s))
  rw [deathFamily, dite_eq_right hrQ, dite_eq_right hrP]
  exact l2_opNorm_toMatrix_toPEquiv_le _

omit [Fintype P] in
/-- The death chain uses only `P∘` and `Q∘`. -/
theorem usesOnly_deathChain (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (deathChain hTP hQP σ).UsesOnly {P₀, Q} := by
  refine ⟨fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hr
    refine ⟨(birth_system_eq hTP hQP hr.2 hr.1).symm, fun y x ↦ ?_⟩
    rw [deathFamily, dite_eq_right hr.2, dite_eq_right hr.1]
    simp [PEquiv.toMatrix_apply]
  · simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hr ⊢
    tauto

omit [Fintype P] in
/-- The only gate of the death chain is a pair effect. -/
theorem forallGate_isRight_deathChain (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (deathChain hTP hQP σ).ForallGate fun _ _ _ g ↦ Sum.isRight g :=
  ⟨trivial, rfl⟩

omit [Fintype P] in
/-- The death chain has one gate. -/
theorem numGates_deathChain (hTP : ∀ x ∈ T, S.owner x = P₀) (hQP : Q ≠ P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (deathChain hTP hQP σ).numGates = 1 :=
  rfl

end Birth

end Sheet

end QuantumCircuit.Party
