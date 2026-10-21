/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.CharZero.Infinite

/-!
# Finite monomial interpolation

Evaluation at finitely many complex points recovers the coefficients of any
polynomial with a prescribed finite monomial support. The points and scalar
recovery coefficients depend only on that support. The same witnesses therefore
recover coefficients in any complex vector space, including dependent families
of operators.

**Local fix (interpolation):** The evaluated operator families in the source
need only span the coefficient-operator space. They need not form a basis when
the coefficient operators are dependent. The scalar recovery identities below
supply the required spanning assertion without an independence hypothesis; see
`docs/paper-gaps/aklv13_interpolation_and_word_count.tex`.

This is the interpolation argument in AKLV, arXiv:1301.1162v1,
Lemma l:agsp, lines 626–644. It does not assert the subsequent locality or
operator-Schmidt-rank estimates.
-/

open scoped BigOperators Classical

namespace MvPolynomial

private theorem evaluation_monomials_linearIndependent {σ : Type*}
    (S : Finset (σ →₀ ℕ)) :
    LinearIndependent ℂ (fun (β : S) (z : σ → ℂ) =>
      eval z (monomial (β : σ →₀ ℕ) (1 : ℂ))) := by
  let E : MvPolynomial σ ℂ →ₗ[ℂ] ((σ → ℂ) → ℂ) :=
    LinearMap.pi fun z => (aeval z).toLinearMap
  have hinj : Function.Injective E := fun p q h => funext (congrFun h)
  exact ((basisMonomials σ ℂ).linearIndependent.comp
    (fun β : S => (β : σ →₀ ℕ)) Subtype.val_injective).map' E
      (LinearMap.ker_eq_bot.mpr hinj)

/-- Finite monomial interpolation, AKLV arXiv:1301.1162v1,
Lemma l:agsp, lines 626–644. The evaluations recover coefficients without
requiring the coefficient operators to be linearly independent. -/
theorem exists_monomial_evaluation_recovery
    {σ : Type*} (S : Finset (σ →₀ ℕ)) :
    ∃ z : Fin S.card → (σ → ℂ),
      ∃ c : S → Fin S.card → ℂ,
        ∀ α β : S,
          (∑ r : Fin S.card,
            c α r * eval (z r) (monomial (β : σ →₀ ℕ) (1 : ℂ))) =
            if α = β then 1 else 0 := by
  have hspan : Submodule.span ℂ (Set.range (fun (z : σ → ℂ) (β : S) =>
      eval z (monomial (β : σ →₀ ℕ) (1 : ℂ)))) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr (evaluation_monomials_linearIndependent S)
  have hcard : Module.finrank ℂ (Submodule.span ℂ
      (Set.range (fun (z : σ → ℂ) (β : S) =>
        eval z (monomial (β : σ →₀ ℕ) (1 : ℂ))))) = S.card := by
    simpa only [finrank_top, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe] using
      congrArg (fun U : Submodule ℂ (S → ℂ) => Module.finrank ℂ U) hspan
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℂ
    (Set.range (fun (z : σ → ℂ) (β : S) =>
      eval z (monomial (β : σ →₀ ℕ) (1 : ℂ))))
  rw [hcard, hspan] at hex
  obtain ⟨v, hv, hvspan, _⟩ := hex
  choose z hz using hv
  have hc : ∀ α : S, ∃ c : Fin S.card → ℂ,
      ∑ r, c r • v r = Pi.single α (1 : ℂ) :=
    fun α => (Submodule.mem_span_range_iff_exists_fun ℂ).mp
      (hvspan.symm ▸ Submodule.mem_top)
  choose c hc using hc
  refine ⟨z, c, fun α β => ?_⟩
  simpa [← hz, Pi.single_apply, eq_comm] using congrFun (hc α) β

/-- The same scalar interpolation witnesses recover coefficients in any
complex vector space. AKLV arXiv:1301.1162v1, Lemma l:agsp, lines 626–644. -/
theorem monomial_evaluation_recovery_smul
    {σ V : Type*} [AddCommGroup V] [Module ℂ V]
    (S : Finset (σ →₀ ℕ))
    (z : Fin S.card → (σ → ℂ)) (c : S → Fin S.card → ℂ)
    (h : ∀ α β : S,
      (∑ r : Fin S.card,
        c α r * eval (z r) (monomial (β : σ →₀ ℕ) (1 : ℂ))) =
        if α = β then 1 else 0)
    (f : S → V) (α : S) :
    (∑ r : Fin S.card, c α r •
      (∑ β : S, eval (z r) (monomial (β : σ →₀ ℕ) (1 : ℂ)) • f β)) = f α := by
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h]
  simp [ite_smul]

end MvPolynomial
