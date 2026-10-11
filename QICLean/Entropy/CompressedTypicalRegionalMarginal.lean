/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FiniteProductTypicalState
import QICLean.Entropy.TypicalPureCompression

/-!
# Regional marginals of the compressed selected vector

Let a spectral selection be made on one physical region. Replacing the
selected spectral subspace by its coordinate space preserves the density
matrix on every disjoint physical region. The coordinates discarded below
are the selected spectral index and the physical complement of both regions.

The statement concerns the literal compressed vector, with the selected
indices identified with `Fin E.card`. No normalization or positive selected
mass is needed for the equality.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–247 and 332–354,
  `comparator:post-marginal` and `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped BigOperators Matrix

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The actual compressed selected vector has the same marginal on every
disjoint physical region as the selected vector in the original physical
space. The discarded coordinates are placed first, so the statement can be
used directly in a left-partial-trace formula for tensor powers.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–354. -/
theorem partialTraceLeft_compressedTypicalPureState_region
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X B : Finset V)
    (hXB : Disjoint X B) (E : Finset (Configuration β X)) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let χ : Fin E.card × Configuration β Xᶜ → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    let τ : (Fin E.card × Configuration β (X ∪ B)ᶜ) × Configuration β B → ℂ :=
      fun x ↦ χ (x.1.1, (complementUnionEquiv β X B hXB).symm (x.2, x.1.2))
    Matrix.partialTraceLeft (Matrix.vecMulVec τ (star τ)) =
      reducedPure β (typicalPureState β Ω X E) B := by
  intro ΩX χ τ
  let Ψ := typicalPureState β Ω X E
  have hselected (a : Configuration β X) (u : Configuration β Xᶜ) :
      Matrix.typicalPureState ΩX E (a, u) = Ψ ((splitEquiv β X).symm (a, u)) := by
    exact (congrArg (fun v ↦ v (a, u)) (split_typicalPureState β Ω X E)).symm
  have hcomplement (u v : Configuration β Xᶜ) :
      (∑ r : Fin E.card, χ (r, u) * star (χ (r, v))) =
        ∑ a : Configuration β X,
          Ψ ((splitEquiv β X).symm (a, u)) *
            star (Ψ ((splitEquiv β X).symm (a, v))) := by
    calc
      _ = ∑ i : E, Matrix.compressedTypicalPureState ΩX E (i, u) *
          star (Matrix.compressedTypicalPureState ΩX E (i, v)) :=
        (Finset.equivFin E).symm.sum_comp (fun i : E ↦
          Matrix.compressedTypicalPureState ΩX E (i, u) *
            star (Matrix.compressedTypicalPureState ΩX E (i, v)))
      _ = _ := by
        have hm := congrArg (fun M ↦ M u v)
          (Matrix.partialTraceLeft_compressedTypicalPureState ΩX E)
        simpa only [Matrix.partialTraceLeft_apply, Matrix.vecMulVec_apply,
          Pi.star_apply, hselected] using hm
  change Matrix.partialTraceLeft (Matrix.vecMulVec τ (star τ)) = reducedPure β Ψ B
  rw [reducedPure, ← partialTraceLeft_reducedMatrix_union β
    (Matrix.vecMulVec (WithLp.ofLp Ψ) (star (WithLp.ofLp Ψ))) X B hXB]
  ext b b'
  change (∑ rc : Fin E.card × Configuration β (X ∪ B)ᶜ,
      χ (rc.1, (complementUnionEquiv β X B hXB).symm (b, rc.2)) *
        star (χ (rc.1, (complementUnionEquiv β X B hXB).symm (b', rc.2)))) =
    ∑ a : Configuration β X, ∑ c : Configuration β (X ∪ B)ᶜ,
      Ψ ((splitEquiv β (X ∪ B)).symm ((unionEquiv β X B hXB).symm (a, b), c)) *
        star (Ψ ((splitEquiv β (X ∪ B)).symm
          ((unionEquiv β X B hXB).symm (a, b'), c)))
  simp_rw [split_union_symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hcomplement]
  exact Finset.sum_comm

end FiniteProduct
