/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausCPTP
import QICLean.Kraus.MapIterate

/-!
# Composition, iteration and operator trace of rectangular Kraus maps

Three generic facts about `Matrix.rectangularKrausMap`, the map
`X ↦ ∑ i, A i * X * (A i)ᴴ` of a finite rectangular Kraus family:

* `Matrix.rectangularKrausMap_comp`: the composite of two rectangular Kraus
  maps is the rectangular Kraus map of the family of all products;
* `Matrix.rectangularKrausMap_evalWord_ofFn`: the rectangular Kraus map of all
  words of length `n` of a square family is the `n`-th power of its Kraus map;
* `Matrix.linearMap_trace_rectangularKrausMap`: the operator trace of a square
  rectangular Kraus map is `∑ i, |tr (A i)|²`.

These are the channel-generic steps of a norm calculation along a chain of
Kraus words, such as the domain-wall overlap of a trial state against an
open-boundary tensor (arXiv:1210.6613, proof of Lemma lowenergystates).
-/

open scoped Matrix BigOperators

namespace Matrix

/-- The composite of two rectangular Kraus maps is the rectangular Kraus map of
the family of all products `C i * E j`. -/
theorem rectangularKrausMap_comp
    {ι κ α β γ : Type*} [Fintype ι] [Fintype κ] [Fintype β] [Fintype γ]
    (C : ι → Matrix α β ℂ) (E : κ → Matrix β γ ℂ) :
    (rectangularKrausMap C).comp (rectangularKrausMap E) =
      rectangularKrausMap (fun z : ι × κ ↦ C z.1 * E z.2) := by
  apply LinearMap.ext
  intro X
  change (∑ i, C i * (∑ j, E j * X * (E j)ᴴ) * (C i)ᴴ) =
    ∑ z : ι × κ, (C z.1 * E z.2) * X * (C z.1 * E z.2)ᴴ
  simp only [Matrix.mul_sum, Matrix.sum_mul, Fintype.sum_prod_type,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The rectangular Kraus map of all words of length `n` of a square Kraus
family is the `n`-th power of its Kraus map. -/
theorem rectangularKrausMap_evalWord_ofFn {d D : ℕ}
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    rectangularKrausMap (fun σ : Fin n → Fin d ↦ Kraus.evalWord K (List.ofFn σ)) =
      Kraus.mapLM K ^ n := by
  apply LinearMap.ext
  intro X
  exact (Kraus.mapLM_pow_apply K n X).symm

/-- The operator trace of the Kraus map of a square family is the sum of the
squared moduli of the traces of its members. -/
theorem linearMap_trace_rectangularKrausMap {a : ℕ} {ι : Type*} [Fintype ι]
    (C : ι → Matrix (Fin a) (Fin a) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin a) (Fin a) ℂ) (rectangularKrausMap C) =
      ∑ z, Matrix.trace (C z) * star (Matrix.trace (C z)) := by
  classical
  rw [Matrix.linearMap_trace_eq_sum_apply_single]
  simp only [Matrix.rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, Matrix.entry_mul_single_mul]
  rw [Finset.sum_comm_cycle]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.conjTranspose_apply,
    star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

end Matrix
