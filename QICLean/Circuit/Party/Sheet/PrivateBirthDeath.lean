/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.BirthDeath

/-!
# Births and deaths of a sheet at one party

In Lemma 6.5 of the polynomial-PEPS manuscript the party `Q∘` receiving the sites `T` may be
the party `P∘` that owns them. Then the birth needs no pair source: it is the private
contraction `Kᴴ K` at `P∘`, with `K = ⟨s| (1_T ⊗ V)` the kernel of the splitting data `σ`
(`Sheet.privateBirthWord`), and its operator in the canonical coordinates of the two sheets is
again the canonical map `𝐁` of the splitting data (`Sheet.op_privateBirthWord`). The death is
the chain of the adjoint local operations, without gates (`Sheet.privateDeathChain`); since `𝐁`
is self-adjoint its operator is `𝐁` as well (`Sheet.op_privateDeathChain`).

## Main definitions

* `QuantumCircuit.Party.Sheet.privateBirthWord`, `QuantumCircuit.Party.Sheet.privateDeathChain`.

## Main results

* `QuantumCircuit.Party.Sheet.op_privateBirthWord`,
  `QuantumCircuit.Party.Sheet.isAllowed_privateBirthWord`,
  `QuantumCircuit.Party.Sheet.usesOnly_privateBirthWord`,
  `QuantumCircuit.Party.Sheet.sourceCount_privateBirthWord`.
* `QuantumCircuit.Party.Sheet.op_privateDeathChain`,
  `QuantumCircuit.Party.Sheet.isAllowed_privateDeathChain`,
  `QuantumCircuit.Party.Sheet.usesOnly_privateDeathChain`,
  `QuantumCircuit.Party.Sheet.numGates_privateDeathChain`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.5 `lem:birth`,
  `05-frames.tex`, lines 420–426 (the canonical map) and 445–446 (the two owners agree).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

namespace Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] {q : ℕ}

section Private

variable {S : Sheet ι P} {T : Finset ι} {P₀ : P}

/-- **The local operations of a private birth** (`Q∘ = P∘`): the contraction `Kᴴ K` at `P∘`,
the identity elsewhere. Source: `05-frames.tex`, lines 445–446. -/
noncomputable def privateBirthFamily (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) (s : P) :
    Matrix ((S.changeOwner T P₀).system q s) (S.system q s) ℂ :=
  if hs : s = P₀ then cast (congrArg (fun r ↦ Matrix ((S.changeOwner T P₀).system q r)
      (S.system q r) ℂ) hs.symm)
    (reindex (S.birthEquivSelf T P₀).symm (birthEquivP hTP).symm
      ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s))
  else (Equiv.cast (system_eq_of_owner_iff S
    (S.changeOwner_owner_eq_iff_of_ne hTP hs hs))).toPEquiv.toMatrix

/-- **The birth and the death when the two owners agree** (`Q∘ = P∘`): the private contraction
`Kᴴ K` at `P∘`. Source: proof of Lemma 6.5, `05-frames.tex`, lines 445–446. -/
noncomputable def privateBirthWord (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    Word (S.system q) ((S.changeOwner T P₀).system q) :=
  PartyCircuit.localOps (privateBirthFamily hTP σ)

/-- **The private birth word in canonical coordinates** is the canonical map `𝐁` of the
splitting data. -/
theorem op_privateBirthWord (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (privateBirthWord hTP σ).op =
      reindex (blockConfigEquiv (S.changeOwner T P₀).owner fun _ ↦ Fin q).symm
        (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) := by
  ext y x
  rw [privateBirthWord, show Word.op (PartyCircuit.localOps (privateBirthFamily hTP σ)) =
      piKronecker (privateBirthFamily hTP σ) from PartyCircuit.op_localOps _ _, reindex_apply,
    submatrix_apply, Equiv.symm_symm, Equiv.symm_symm, configBirthOp_apply_changeOwner_self hTP,
    piKronecker_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ P₀)]
  have hP : privateBirthFamily hTP σ P₀ (y P₀) (x P₀) =
      ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s) (S.birthEquivSelf T P₀ (y P₀))
        (birthEquivP hTP (x P₀)) := by
    rw [privateBirthFamily, dite_eq_left rfl, cast_eq, reindex_apply, submatrix_apply,
      Equiv.symm_symm, Equiv.symm_symm]
  have hR : ∀ r ∈ Finset.univ.erase P₀, privateBirthFamily hTP σ r (y r) (x r) =
      if ∀ v, S.owner v = r → blockConfigEquiv (S.changeOwner T P₀).owner (fun _ ↦ Fin q) y v =
        blockConfigEquiv S.owner (fun _ ↦ Fin q) x v then 1 else 0 := fun r hr ↦ by
    have hrP : r ≠ P₀ := (Finset.mem_erase.mp hr).1
    rw [privateBirthFamily, dite_eq_right hrP]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
      Equiv.cast_apply]
    exact if_congr (cast_changeOwner_system_iff hTP hrP hrP y x _) rfl rfl
  rw [hP, Finset.prod_congr rfl hR, Finset.prod_boole, mul_comm]
  congr 1
  split_ifs <;> rfl

omit [Fintype P] in
/-- The private birth word is allowed. -/
theorem isAllowed_privateBirthWord (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (privateBirthWord hTP σ).IsAllowed := by
  intro r
  by_cases hrP : r = P₀
  · subst hrP
    rw [privateBirthFamily, dite_eq_left rfl, cast_eq]
    have h := norm_birthKernel_le_one σ.isIsometry σ.star_s
    exact (l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_mul_le_one _ _
      ((l2_opNorm_conjTranspose _).trans_le h) h)
  rw [privateBirthFamily, dite_eq_right hrP]
  exact l2_opNorm_toMatrix_toPEquiv_le _

omit [Fintype P] in
/-- The private birth word uses only `P∘`. -/
theorem usesOnly_privateBirthWord (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (privateBirthWord hTP σ).UsesOnly {P₀} := by
  intro r hr
  have hrP : r ≠ P₀ := hr
  refine ⟨system_eq_of_owner_iff S (S.changeOwner_owner_eq_iff_of_ne hTP hrP hrP), fun y x ↦ ?_⟩
  rw [privateBirthFamily, dite_eq_right hrP]
  simp [PEquiv.toMatrix_apply]

omit [Fintype P] in
/-- The private birth word has no pair source. -/
theorem sourceCount_privateBirthWord (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (privateBirthWord hTP σ).sourceCount = 0 :=
  rfl

/-- **The death when the two owners agree** (`Q∘ = P∘`): the private contraction `Kᴴ K` at
`P∘`, as a chain without gates; its local operations are the adjoints of those of the private
birth. Source: proof of Lemma 6.5, `05-frames.tex`, lines 442–446. -/
noncomputable def privateDeathChain (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    PartyCircuit (ChainGate (P := P)) ((S.changeOwner T P₀).system q) (S.system q) :=
  PartyCircuit.localOps fun r ↦ (privateBirthFamily hTP σ r)ᴴ

/-- **The private death chain in canonical coordinates** is the canonical map `𝐁` of the
splitting data, which is self-adjoint. -/
theorem op_privateDeathChain (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (privateDeathChain hTP σ).op chainEv =
      reindex (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
        (blockConfigEquiv (S.changeOwner T P₀).owner fun _ ↦ Fin q).symm
        (configBirthOp Finset.subset_union_left σ) := by
  rw [privateDeathChain, PartyCircuit.op_localOps, ← conjTranspose_piKronecker,
    ← show Word.op (PartyCircuit.localOps (privateBirthFamily hTP σ)) =
      piKronecker (privateBirthFamily hTP σ) from PartyCircuit.op_localOps _ _,
    ← privateBirthWord, op_privateBirthWord, conjTranspose_reindex,
    (configBirthOp_isHermitian Finset.subset_union_left σ).eq]

omit [Fintype P] in
/-- The private death chain is allowed. -/
theorem isAllowed_privateDeathChain (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (privateDeathChain hTP σ).IsAllowed chainEv ChainGate.IsAllowed := fun r ↦
  (l2_opNorm_conjTranspose _).trans_le (isAllowed_privateBirthWord hTP σ r)

omit [Fintype P] in
/-- The private death chain uses only `P∘`. -/
theorem usesOnly_privateDeathChain (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (privateDeathChain hTP σ).UsesOnly {P₀} := by
  intro r hr
  have hrP : r ≠ P₀ := hr
  have e := system_eq_of_owner_iff (q := q) S (S.changeOwner_owner_eq_iff_of_ne hTP hrP hrP)
  refine ⟨e.symm, fun x y ↦ ?_⟩
  change (privateBirthFamily hTP σ r)ᴴ x y = _
  rw [conjTranspose_apply, privateBirthFamily, dite_eq_right hrP]
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Equiv.cast_apply]
  by_cases h : x = cast e y
  · subst h
    simp
  · have h₁ : ¬cast e y = x := fun h' ↦ h h'.symm
    have h₂ : ¬cast e.symm x = y := fun h' ↦ h (by rw [← h', cast_cast, cast_eq])
    simp only [h₁, h₂, ↓reduceIte, star_zero]

omit [Fintype P] in
/-- The private death chain has no gate. -/
theorem numGates_privateDeathChain (hTP : ∀ x ∈ T, S.owner x = P₀)
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀)) :
    (privateDeathChain hTP σ).numGates = 0 :=
  rfl

end Private

end Sheet

end QuantumCircuit.Party
