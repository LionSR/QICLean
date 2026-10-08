/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchurLabelEstimates

/-!
# Transporting labels between subsystems and tensor powers

The label projectors of the copy permutations of a subsystem `Q` of
`V = ⨂_{f ∈ F} ℂ^{ι f}` are those of the copy permutations of `Q^{⊗k}`, tensored with the
identity on the other factors. This file proves the transport along equivalences of
permutation actions and along a trivial second factor, and deduces that a label occurring
on a subsystem of dimension `d_Q` has at most `d_Q` rows (`05-replicas.tex`, lines 51–64:
`(ℂ^q)^{⊗k} = ⨁_{ℓ(λ) ≤ q} [λ] ⊗ V_λ^{(q)}`, applied to `Q^{⊗k}`).

## Main declarations

* `PermutationRepresentation.groupAlgebraRep_of_intertwine`,
  `PermutationRepresentation.labelProj_of_intertwine` — transport along `e : X ≃ Y`.
* `PermutationRepresentation.prodLeft`, `PermutationRepresentation.labelProj_prodLeft` —
  an action on the first factor of `X × Z`.
* `TensorPower.labelProj_subsystemPerm_eq` — `π^λ_{Q,k}` is `π^λ` of `Q^{⊗k}` tensored with
  the identity.
* `TensorPower.labelPart_eq_zero_of_subsystemPerm` — at most `d_Q` rows.
-/

open Matrix
open scoped Kronecker

namespace PermutationRepresentation

variable {G X Y Z : Type*} [Group G] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

/-- Permutation operators of intertwined actions agree up to reindexing. -/
theorem permOp_of_intertwine (e : X ≃ Y) {φ : G →* Equiv.Perm X} {ψ : G →* Equiv.Perm Y}
    (h : ∀ g x, ψ g (e x) = e (φ g x)) (g : G) :
    permOp ψ g = reindex e e (permOp φ g) := by
  ext y y'
  simp only [permOp_apply_apply, reindex_apply, submatrix_apply]
  have hy := h g (e.symm y')
  rw [Equiv.apply_symm_apply] at hy
  rw [hy]
  congr 1
  exact propext ⟨fun h' => by rw [← h', Equiv.symm_apply_apply], fun h' => by
    rw [h', Equiv.apply_symm_apply]⟩

/-- The group-algebra images of intertwined actions agree up to reindexing. -/
theorem groupAlgebraRep_of_intertwine (e : X ≃ Y) {φ : G →* Equiv.Perm X}
    {ψ : G →* Equiv.Perm Y} (h : ∀ g x, ψ g (e x) = e (φ g x)) (a : MonoidAlgebra ℂ G) :
    groupAlgebraRep ψ a = reindex e e (groupAlgebraRep φ a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    ext; simp
  | single g c =>
    rw [groupAlgebraRep_single, groupAlgebraRep_single, permOp_of_intertwine e h]
    ext; simp

/-- The label projectors of intertwined actions agree up to reindexing. -/
theorem labelProj_of_intertwine [Fintype G] (e : X ≃ Y) {φ : G →* Equiv.Perm X}
    {ψ : G →* Equiv.Perm Y} (h : ∀ g x, ψ g (e x) = e (φ g x)) (l : IrrepLabel G) :
    labelProj ψ l = reindex e e (labelProj φ l) :=
  groupAlgebraRep_of_intertwine e h _

variable (Z) in
/-- An action on the first factor of `X × Z`, trivial on the second. -/
def prodLeft (φ : G →* Equiv.Perm X) : G →* Equiv.Perm (X × Z) where
  toFun g := Equiv.prodCongr (φ g) (Equiv.refl Z)
  map_one' := by ext <;> simp
  map_mul' g h := by ext <;> simp [Equiv.Perm.mul_apply]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
@[simp]
theorem prodLeft_apply (φ : G →* Equiv.Perm X) (g : G) (p : X × Z) :
    prodLeft Z φ g p = (φ g p.1, p.2) := rfl

theorem permOp_prodLeft (φ : G →* Equiv.Perm X) (g : G) :
    permOp (prodLeft Z φ) g = permOp φ g ⊗ₖ (1 : Matrix Z Z ℂ) := by
  ext ⟨x, z⟩ ⟨x', z'⟩
  simp only [permOp_apply_apply, prodLeft_apply, kroneckerMap_apply, one_apply, Prod.mk.injEq,
    eq_comm (a := z)]
  by_cases h1 : φ g x' = x <;> by_cases h2 : z' = z <;> simp [h1, h2]

theorem groupAlgebraRep_prodLeft (φ : G →* Equiv.Perm X) (a : MonoidAlgebra ℂ G) :
    groupAlgebraRep (prodLeft Z φ) a = groupAlgebraRep φ a ⊗ₖ (1 : Matrix Z Z ℂ) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_kronecker]
  | single g c =>
    rw [groupAlgebraRep_single, groupAlgebraRep_single, permOp_prodLeft, smul_kronecker]

theorem labelProj_prodLeft [Fintype G] (φ : G →* Equiv.Perm X) (l : IrrepLabel G) :
    labelProj (prodLeft Z φ) l = labelProj φ l ⊗ₖ (1 : Matrix Z Z ℂ) :=
  groupAlgebraRep_prodLeft φ _

end PermutationRepresentation

namespace TensorPower

open PermutationRepresentation

variable {F : Type*} [DecidableEq F] [Fintype F] (ι : F → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] (k : ℕ)

/-- The one-copy configurations of a subsystem `Q`. -/
abbrev SubConfig (Q : Finset F) := (f : {f // f ∈ Q}) → ι f

/-- The one-copy configurations of the complement of `Q`. -/
abbrev ComplConfig (Q : Finset F) := (f : {f // f ∉ Q}) → ι f

/-- `V^{⊗k} ≅ Q^{⊗k} ⊗ (Qᶜ)^{⊗k}` on basis configurations. -/
def splitEquiv (Q : Finset F) :
    Config k ι ≃ (Fin k → SubConfig ι Q) × (Fin k → ComplConfig ι Q) where
  toFun x := (fun j f => x j f, fun j f => x j f)
  invFun p := fun j f => if h : f ∈ Q then p.1 j ⟨f, h⟩ else p.2 j ⟨f, h⟩
  left_inv x := by
    ext j f
    by_cases h : f ∈ Q <;> simp [h]
  right_inv p := by
    ext j f
    · simp [f.2]
    · simp [f.2]

omit [Fintype F] [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
/-- Under `splitEquiv`, the copy permutations of `Q` act on the first factor only. -/
theorem splitEquiv_subsystemPerm (Q : Finset F) (σ : Equiv.Perm (Fin k)) (x : Config k ι) :
    prodLeft (Fin k → ComplConfig ι Q) (copyPerm (SubConfig ι Q) k) σ (splitEquiv ι k Q x) =
      splitEquiv ι k Q (subsystemPerm k ι Q σ x) := by
  ext j f
  · simp [splitEquiv]
  · simp [splitEquiv, f.2]

/-- **Labels of a subsystem**: `π^λ_{Q,k}` is the label projector of `Q^{⊗k}` tensored with the
identity on the complement, after `splitEquiv`. -/
theorem labelProj_subsystemPerm_eq (Q : Finset F) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    reindex (splitEquiv ι k Q) (splitEquiv ι k Q) (labelProj (subsystemPerm k ι Q) l) =
      labelProj (copyPerm (SubConfig ι Q) k) l ⊗ₖ (1 : Matrix (Fin k → ComplConfig ι Q)
        (Fin k → ComplConfig ι Q) ℂ) := by
  rw [← labelProj_prodLeft, labelProj_of_intertwine (splitEquiv ι k Q)
    (fun σ x => splitEquiv_subsystemPerm ι k Q σ x)]

/-- Copy permutations of `Ω^{⊗k}` and of `(Fin q)^{⊗k}` are intertwined by `Ω ≃ Fin q`. -/
theorem labelProj_copyPerm_equiv {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {q : ℕ}
    (e : Ω ≃ Fin q) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    labelProj (copyPerm (Fin q) k) l =
      reindex (Equiv.arrowCongr (Equiv.refl (Fin k)) e)
        (Equiv.arrowCongr (Equiv.refl (Fin k)) e) (labelProj (copyPerm Ω k) l) :=
  labelProj_of_intertwine _ (fun σ y => by ext j; simp [Equiv.arrowCongr_apply]) l

omit [Fintype F] in
private theorem eq_zero_of_reindex_eq_zero {m n : Type*} (e : m ≃ n) {A : Matrix m m ℂ}
    (h : reindex e e A = 0) : A = 0 := by
  have := congrArg (reindex e e).symm h
  simpa using this

/-- A label occurring on a subsystem occurs on the tensor power of its one-copy space. -/
theorem labelProj_copyPerm_ne_zero_of_subsystemPerm (Q : Finset F)
    {l : IrrepLabel (Equiv.Perm (Fin k))} (h : labelProj (subsystemPerm k ι Q) l ≠ 0) :
    labelProj (copyPerm (Fin (Fintype.card (SubConfig ι Q))) k) l ≠ 0 := by
  intro h0
  rw [labelProj_copyPerm_equiv k (Fintype.equivFin (SubConfig ι Q))] at h0
  have h1 := eq_zero_of_reindex_eq_zero _ h0
  apply h
  refine eq_zero_of_reindex_eq_zero (splitEquiv ι k Q) ?_
  rw [labelProj_subsystemPerm_eq, h1, zero_kronecker]

/-- **Rows of a subsystem label** (`05-replicas.tex`, lines 51–64): a label occurring on a
subsystem `Q` has at most `d_Q` rows. -/
theorem labelPart_eq_zero_of_subsystemPerm (Q : Finset F)
    {l : IrrepLabel (Equiv.Perm (Fin k))} (h : labelProj (subsystemPerm k ι Q) l ≠ 0) :
    ∀ a, Fintype.card (SubConfig ι Q) ≤ a → labelPart l a = 0 :=
  labelPart_eq_zero_of_labelProj_ne_zero (labelProj_copyPerm_ne_zero_of_subsystemPerm ι k Q h)

omit [∀ f, DecidableEq (ι f)] in
/-- With nonempty factors, a subsystem has dimension at most that of the whole system. -/
theorem card_subConfig_le [∀ f, Nonempty (ι f)] (Q : Finset F) :
    Fintype.card (SubConfig ι Q) ≤ Fintype.card ((f : F) → ι f) := by
  classical
  refine Fintype.card_le_of_injective
    (fun y f => if h : f ∈ Q then y ⟨f, h⟩ else Classical.arbitrary _) fun y y' hy => ?_
  funext f
  have := congrFun hy f
  simpa [f.2] using this

end TensorPower
