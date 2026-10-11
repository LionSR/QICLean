/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RegionalFiveFactorCoordinates

/-!
# The physical vector under regional grouping

Restriction to two disjoint regions and the complement of their union
identifies the original product basis with the three grouped factors.
This identification preserves the norm of every physical vector.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 421--456, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section

namespace FiniteProduct

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The literal regional regrouping preserves the norm of the original
physical vector. Source: `07-comparators.tex`, lines 421--456. -/
theorem norm_regionalPhysicalVector (β : V → Type u)
    [∀ v, Fintype (β v)] (Ω : ((v : V) → β v) → ℂ)
    (Q Y : Finset V) (hQY : Disjoint Q Y) :
    ‖WithLp.toLp 2 (Ω ∘ (regionalPhysicalEquiv β Q Y hQY).symm)‖ =
      ‖WithLp.toLp 2 Ω‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (regionalPhysicalEquiv β Q Y hQY)).norm_map (WithLp.toLp 2 Ω)


end FiniteProduct
