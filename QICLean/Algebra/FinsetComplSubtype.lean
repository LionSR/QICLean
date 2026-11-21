/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Logic.Equiv.Basic

/-!
# The elements outside a finite set

The elements of a finite type that lie outside a finite set `s` are the elements of its
complement `sᶜ`. The two subtypes are different types, since membership in `sᶜ` is
equivalent, but not definitionally equal, to non-membership in `s`.
-/

namespace Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (s : Finset α) in
/-- The elements outside `s` are the elements of the complement `sᶜ`. -/
def complSubtypeEquiv : {a // a ∉ s} ≃ {a // a ∈ sᶜ} :=
  Equiv.subtypeEquivRight fun _ ↦ mem_compl.symm

variable {s : Finset α}

@[simp] theorem coe_complSubtypeEquiv (a : {a // a ∉ s}) : (complSubtypeEquiv s a : α) = a :=
  rfl

@[simp] theorem coe_complSubtypeEquiv_symm (a : {a // a ∈ sᶜ}) :
    ((complSubtypeEquiv s).symm a : α) = a :=
  rfl

end Finset
