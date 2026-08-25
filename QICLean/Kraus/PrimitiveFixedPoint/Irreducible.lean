/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Kraus.PrimitiveFixedPoint.Basic
import QICLean.Channel.KrausMap
import QICLean.Channel.Irreducible.FixedPoint
import QICLean.Channel.Irreducible.FromSpectral
import QICLean.Kraus.InvariantProjection

/-!
# Irreducibility and primitive fixed points of finite Kraus families

This module relates the distinguished fixed point in a complementary-gap witness to
irreducibility. For a finite Kraus map with complementary fixed-point gap, map
irreducibility upgrades the bundled nonzero positive-semidefinite fixed point to a
positive-definite one. Conversely, positive definiteness and uniqueness of the fixed-point
space imply map irreducibility. The same equivalence is then exposed for irreducibility of
the Kraus family itself.

## Main declarations

* `Kraus.HasComplementaryFixedPointGap.posDef_of_isIrreducibleMap`
* `Kraus.HasComplementaryFixedPointGap.isIrreducibleMap_of_posDef`
* `Kraus.HasComplementaryFixedPointGap.posDef_of_isIrreducibleFamily`
* `Kraus.HasComplementaryFixedPointGap.isIrreducibleFamily_of_posDef`

All statements use `Kraus.mapLM` directly. The family-level corollaries use the direct
family/map irreducibility equivalence and do not pass through a transfer-map compatibility
layer.
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators
open Matrix

namespace Kraus

variable {d D : ℕ} [NeZero D]
variable {K : Fin d → Matrix (Fin D) (Fin D) ℂ}
variable {ρ : Matrix (Fin D) (Fin D) ℂ}

/-- If the finite Kraus map is irreducible, the nonzero positive-semidefinite fixed point
in complementary-gap data is positive definite. -/
theorem HasComplementaryFixedPointGap.posDef_of_isIrreducibleMap
    (hP : HasComplementaryFixedPointGap K ρ)
    (hIrr : IsIrreducibleMap (mapLM K)) :
    ρ.PosDef :=
  posDef_of_posSemidef_fixedPoint_irreducible_cp
    (mapLM K) (isCPMap_mapLM K) hIrr ρ hP.fixedPoint_psd hP.fixedPoint_ne_zero
    hP.fixedPoint_is_fixed

/-- If the distinguished fixed point in complementary-gap data is positive definite,
then the finite Kraus map is irreducible.

The complementary gap gives uniqueness of every fixed point, while the channel-level
fixed-point criterion turns positive definiteness and uniqueness into irreducibility. -/
theorem HasComplementaryFixedPointGap.isIrreducibleMap_of_posDef
    (hP : HasComplementaryFixedPointGap K ρ) (hρ_pd : ρ.PosDef) :
    IsIrreducibleMap (mapLM K) := by
  have huniq : ∀ σ : Matrix (Fin D) (Fin D) ℂ,
      σ.PosSemidef → mapLM K σ = σ → ∃ c : ℂ, σ = c • ρ := by
    intro σ _ hσ
    exact ⟨trace σ / trace ρ, hP.fixedPoint_unique σ hσ⟩
  exact isIrreducibleMap_of_channel_posDef_fixedPoint_unique
    (mapLM K) (isChannel_mapLM K hP.norm) ρ hρ_pd hP.fixedPoint_is_fixed huniq

/-- If the Kraus family is irreducible, the fixed point in complementary-gap data is
positive definite. -/
theorem HasComplementaryFixedPointGap.posDef_of_isIrreducibleFamily
    (hP : HasComplementaryFixedPointGap K ρ) (hIrr : IsIrreducibleFamily K) :
    ρ.PosDef :=
  hP.posDef_of_isIrreducibleMap
    (isIrreducibleMap_mapLM_of_isIrreducibleFamily K hIrr)

/-- If the distinguished fixed point in complementary-gap data is positive definite,
then the Kraus family is irreducible. -/
theorem HasComplementaryFixedPointGap.isIrreducibleFamily_of_posDef
    (hP : HasComplementaryFixedPointGap K ρ) (hρ_pd : ρ.PosDef) :
    IsIrreducibleFamily K :=
  isIrreducibleFamily_of_isIrreducibleMap_mapLM K
    (hP.isIrreducibleMap_of_posDef hρ_pd)

end Kraus
