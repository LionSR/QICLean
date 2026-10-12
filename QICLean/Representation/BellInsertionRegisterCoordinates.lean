/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellInsertionCoordinates

/-!
# Changes of coordinates in the inserted register

Changing the coordinate values at each site commutes with every subsystem
copy permutation. For Bell insertion, an equivalence of the inserted register
changes only the rows of the insertion matrix; the physical complement and
the retained auxiliary register are fixed.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `05-replicas.tex`, lines 24–27, and
  `07-comparators.tex`, lines 283–308, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u v w

namespace TensorPower

/-- Changing coordinate values at fixed sites commutes with each subsystem
copy permutation. No finiteness or nonemptiness of the coordinate types is
needed for this identity. Source: area-law manuscript, `05-replicas.tex`,
lines 24--27, and `07-comparators.tex`, lines 283--308. -/
theorem subsystemPerm_piCongrRight
    {F : Type u} [DecidableEq F] (ι : F → Type v) (κ : F → Type w)
    (c : ∀ f, κ f ≃ ι f) (k : ℕ) (Q : Finset F)
    (σ : Equiv.Perm (Fin k)) (x : Config k κ) :
    let e := Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight c
    e (subsystemPerm k κ Q σ x) = subsystemPerm k ι Q σ (e x) := by
  intro e
  funext j f
  done

/-- Enumerating C changes only the rows of the actual Bell insertion. The
exterior columns and the original R register remain fixed. Source:
area-law manuscript, `07-comparators.tex`, lines 283--308. -/
theorem bellInsertion_submatrix_C_equiv
    {V : Type u} [Fintype V] [DecidableEq V]
    (β : V → Type u) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (X : Finset V) (C D R : Type u)
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    [Fintype R] [DecidableEq R]
    (c : D ≃ C) (k : ℕ) (b : FiniteProduct.Configuration β X × C → ℂ) :
    let ιC := addedSiteSpace (addedSiteSpace β C) R
    let ιD := addedSiteSpace (addedSiteSpace β D) R
    let changeSite : ∀ o : Option (Option V), ιD o ≃ ιC o := fun o ↦
      match o with
      | none => Equiv.refl R
      | some none => c
      | some (some v) => Equiv.refl (β v)
    let e := Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight changeSite
    let exterior := FiniteProduct.compressedSiteSpace β X R
    let JC := (addedSiteInsertion exterior (FiniteProduct.Configuration β X × C) k b).submatrix
      (bellInsertionCopyEquiv β X C R k) id
    let JD := (addedSiteInsertion exterior (FiniteProduct.Configuration β X × D) k
      (fun x ↦ b (x.1, c x.2))).submatrix (bellInsertionCopyEquiv β X D R k) id
    JD = JC.submatrix e id := by
  intro ιC ιD changeSite e exterior JC JD
  ext x y
  dsimp only [JD, JC, Matrix.submatrix_apply, addedSiteInsertion]
  simp only [bellInsertionCopyEquiv, Equiv.piCongrRight_apply, Pi.map_apply,
    bellInsertionSiteEquiv, Equiv.coe_fn_mk, e, changeSite, Equiv.refl_apply, id_eq]
  dsimp only [Equiv.piCongrRight, Equiv.refl, Pi.map]
  simp only [Equiv.coe_fn_mk, Pi.map_apply, id_eq]
  congr 1
  congr 2
  exact funext fun j ↦ funext fun
    | none => rfl
    | some v => rfl

end TensorPower
