/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Effect.Resources
import QICLean.Circuit.Party.Effect.Error
import QICLean.Circuit.Party.Syntax.Local

/-!
# Source-only reduction of the physical density of an original circuit

For an original circuit with `M` nonprivate gates, the gate budget `δ = ε / (8 M)`
(`sourceGateBudget`, with `M` replaced by `1` when there is no gate) makes the physical density
of the source-only replacement differ from that of the circuit by at most `ε / 2` in trace norm
(`rectangularTraceNorm_sourceOnly_density_sub_le_half`), for every input of norm at most one,
in particular for a product of unit vectors of the parties (the source's input, lines 137–139),
and for the regional readout of one physical register of dimension `d p` at every party
(`regionalReadout`).

## Main definitions

* `QuantumCircuit.Party.sourceGateBudget`.
* `QuantumCircuit.Party.physicalSystem`, `physicalReadout`, `regionalReadoutEquiv`,
  `regionalReadout` — one physical register `Fin (d p)` in front of a private register `V p` at
  every party, read on the whole system or on a region.

## Main results

* `QuantumCircuit.Party.sourceGateBudget_pos`, `sourceGateBudget_spec`,
  `sourceGateBudget_eq_of_pos`.
* `QuantumCircuit.Party.OriginalCircuit.rectangularTraceNorm_sourceOnly_density_sub_le` and its
  forms `_half`, `_half_of_count_le`, `_wholeParty_…`, `_regional_…`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 137–152 and 199–231.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

/-! ### The gate budget -/

/-- A positive gate budget, the case without nonprivate gate included; for a positive gate count it
is the manuscript's `ε / (8 M)`. Source: `04-compression.tex`, lines 200–202 and 225–227. -/
def sourceGateBudget (ε : ℝ) (M : ℕ) : ℝ := ε / (8 * (max 1 M : ℕ))

/-- The gate budget is positive for a positive error. -/
theorem sourceGateBudget_pos {ε : ℝ} (hε : 0 < ε) (M : ℕ) : 0 < sourceGateBudget ε M := by
  have hM : (0 : ℝ) < (max 1 M : ℕ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 M)
  exact div_pos hε (mul_pos (by norm_num) hM)

/-- The physical gate errors add up to at most half the error. -/
theorem sourceGateBudget_spec {ε : ℝ} (hε : 0 ≤ ε) (M : ℕ) :
    4 * sourceGateBudget ε M * M ≤ ε / 2 := by
  have hM : (0 : ℝ) < (max 1 M : ℕ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 M)
  have hle : (M : ℝ) ≤ (max 1 M : ℕ) := by exact_mod_cast Nat.le_max_right 1 M
  change 4 * (ε / (8 * (max 1 M : ℕ))) * M ≤ ε / 2
  calc
    _ = (ε / 2) * ((M : ℝ) / (max 1 M : ℕ)) := by field_simp; ring
    _ ≤ (ε / 2) * 1 := mul_le_mul_of_nonneg_left
      ((div_le_one hM).mpr hle) (div_nonneg hε (by norm_num))
    _ = ε / 2 := mul_one _

/-- At a positive gate count the budget is the manuscript's choice. Source: `04-compression.tex`,
lines 200–202. -/
theorem sourceGateBudget_eq_of_pos (ε : ℝ) {M : ℕ} (hM : 0 < M) :
    sourceGateBudget ε M = ε / (8 * (M : ℝ)) := by
  simp only [sourceGateBudget, max_eq_right (Nat.succ_le_of_lt hM)]

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ### Physical registers and regional readouts -/

section Readout

variable (d : P → ℕ) (V : P → Type) [∀ p, Fintype (V p)] [∀ p, DecidableEq (V p)]

omit [Fintype P] [DecidableEq P] [∀ p, Fintype (V p)] [∀ p, DecidableEq (V p)] in
/-- One physical register of dimension `d p` in front of the private register `V p` at every party.
Source: `04-compression.tex`, lines 148–150. -/
abbrev physicalSystem : P → Type := fun p ↦ Fin (d p) × V p

/-- The coordinates of the physical system, regrouped into the physical configuration of the region
`A`, and the physical configuration outside `A` with the private registers. -/
def regionalReadoutEquiv (A : Finset P) :
    Config (physicalSystem d V) ≃
      RegionConfig (fun p ↦ Fin (d p)) A × (ComplConfig (fun p ↦ Fin (d p)) A × Config V) :=
  (Equiv.arrowProdEquivProdArrow P _ _).trans
    (((cutEquiv (fun p ↦ Fin (d p)) A).prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))

/-- The whole readout: the coordinates of the physical system read as a physical configuration and a
configuration of the private registers, the second being the discarded factor. Source:
`04-compression.tex`, lines 148–150. -/
def physicalReadout :
    Matrix (Config (fun p ↦ Fin (d p)) × Config V) (Config (physicalSystem d V)) ℂ :=
  (Equiv.arrowProdEquivProdArrow P (fun p ↦ Fin (d p)) V).symm.toPEquiv.toMatrix

/-- The whole readout is a contraction. -/
theorem norm_physicalReadout_le_one : ‖physicalReadout d V‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- The whole readout splits the configuration of every party. -/
theorem toEuclideanLin_physicalReadout_apply
    (x : EuclideanSpace ℂ (Config (physicalSystem d V))) (s : Config fun p ↦ Fin (d p))
    (i : Config V) :
    Matrix.toEuclideanLin (physicalReadout d V) x (s, i) =
      x ((Equiv.arrowProdEquivProdArrow P (fun p ↦ Fin (d p)) V).symm (s, i)) := by
  simp [physicalReadout, Matrix.ofLp_toLpLin, mulVec, dotProduct, PEquiv.toMatrix_apply]

/-- The regional readout: the coordinates read along `regionalReadoutEquiv`, the exterior physical
coordinates and the private registers grouped into the discarded factor. Source:
`04-compression.tex`, lines 148–150, 223–227 and 357–363. -/
def regionalReadout (A : Finset P) :
    Matrix (RegionConfig (fun p ↦ Fin (d p)) A × (ComplConfig (fun p ↦ Fin (d p)) A × Config V))
      (Config (physicalSystem d V)) ℂ :=
  (regionalReadoutEquiv d V A).symm.toPEquiv.toMatrix

/-- The regional readout is a contraction. -/
theorem norm_regionalReadout_le_one (A : Finset P) : ‖regionalReadout d V A‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

/-- The regional coordinates split the configuration of every party. -/
theorem toEuclideanLin_regionalReadout_apply (A : Finset P)
    (x : EuclideanSpace ℂ (Config (physicalSystem d V)))
    (s : RegionConfig (fun p ↦ Fin (d p)) A) (t : ComplConfig (fun p ↦ Fin (d p)) A)
    (i : Config V) :
    Matrix.toEuclideanLin (regionalReadout d V A) x (s, t, i) =
      x ((regionalReadoutEquiv d V A).symm (s, t, i)) := by
  simp [regionalReadout, Matrix.ofLp_toLpLin, mulVec, dotProduct, PEquiv.toMatrix_apply]

omit [Fintype P] in
/-- The physical configurations of a region. Source: `04-compression.tex`, lines 148–150. -/
theorem card_regionConfig_fin (A : Finset P) :
    Fintype.card (RegionConfig (fun p ↦ Fin (d p)) A) = ∏ p ∈ A, d p := by
  simp only [RegionConfig, Fintype.card_pi, Fintype.card_fin, Finset.prod_coe_sort]

omit [Fintype P] in
/-- A uniform bound on the physical dimensions. -/
theorem card_regionConfig_fin_le (A : Finset P) {D : ℕ} (hD : ∀ p ∈ A, d p ≤ D) :
    Fintype.card (RegionConfig (fun p ↦ Fin (d p)) A) ≤ D ^ A.card := by
  rw [card_regionConfig_fin d A]
  simpa only [Finset.prod_const] using Finset.prod_le_prod hD

end Readout

/-! ### The product input -/

/-- A product of unit vectors is a unit vector, from `QuantumCircuit.norm_toLp_productVector`.
Source: `04-compression.tex`, lines 137–139. -/
theorem norm_toLp_productVector_eq_one {X : P → Type} [∀ p, Fintype (X p)]
    (φ : ∀ p, EuclideanSpace ℂ (X p)) (hφ : ∀ p, ‖φ p‖ = 1) :
    ‖(WithLp.toLp 2 (productVector fun p x ↦ φ p x) : EuclideanSpace ℂ (Config X))‖ = 1 :=
  (norm_toLp_productVector φ).trans (Finset.prod_eq_one fun p _ ↦ hφ p)

/-! ### Source-only density reduction -/

namespace OriginalCircuit

variable {Phys Env : Type*} [Fintype Phys] [Fintype Env] {X Y : P → Type}
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The physical density of an original circuit on the input `x`. -/
abbrev physicalDensity (w : OriginalCircuit X Y) (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x : EuclideanSpace ℂ (Config X)) : Matrix Phys Phys ℂ :=
  w.toEffectCircuit.originalPhysicalDensity K x

omit [Fintype Phys] in
/-- The physical density of an original circuit is that of `K` applied to its output. -/
theorem physicalDensity_eq (w : OriginalCircuit X Y) (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x : EuclideanSpace ℂ (Config X)) :
    w.physicalDensity K x =
      partialTraceRight
        (euclideanOuterProduct (Matrix.toEuclideanLin K (Matrix.toEuclideanLin w.op x))
          (Matrix.toEuclideanLin K (Matrix.toEuclideanLin w.op x))) := by
  rw [physicalDensity, EffectCircuit.originalPhysicalDensity, w.op_toEffectCircuit]

/-- The physical density of the source-only replacement of an original circuit. -/
abbrev replacementPhysicalDensity {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (w : OriginalCircuit X Y)
    (hb : w.IsExpansionBounded r S) (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x : EuclideanSpace ℂ (Config X)) : Matrix Phys Phys ℂ :=
  w.toEffectCircuit.replacementPhysicalDensity hδ w.isAllowed_toEffectCircuit hb K x

/-- **Physical density error for the number of nonprivate gates**. Source: `04-compression.tex`,
lines 199–229. -/
theorem rectangularTraceNorm_sourceOnly_density_sub_le [DecidableEq Phys] {r : ℕ} {S δ : ℝ}
    (hδ : 0 < δ) (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1) (x : EuclideanSpace ℂ (Config X))
    (hx : ‖x‖ ≤ 1) :
    rectangularTraceNorm (w.replacementPhysicalDensity hδ hb K x - w.physicalDensity K x) ≤
      4 * δ * w.nonprivateCount := by
  have he := w.toEffectCircuit.rectangularTraceNorm_replacement_density_sub_le hδ
    w.isAllowed_toEffectCircuit hb K hK x hx
  rwa [w.numGates_toEffectCircuit] at he

/-- **The source-only replacement uses at most half the error**, circuits without nonprivate gates
included. Source: `04-compression.tex`, lines 199–229. -/
theorem rectangularTraceNorm_sourceOnly_density_sub_le_half [DecidableEq Phys] {r : ℕ}
    {S ε : ℝ} (hε : 0 < ε) (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1) (x : EuclideanSpace ℂ (Config X))
    (hx : ‖x‖ ≤ 1) :
    rectangularTraceNorm (w.replacementPhysicalDensity
        (sourceGateBudget_pos hε w.nonprivateCount) hb K x - w.physicalDensity K x) ≤ ε / 2 :=
  (w.rectangularTraceNorm_sourceOnly_density_sub_le (sourceGateBudget_pos hε w.nonprivateCount)
    hb K hK x hx).trans (sourceGateBudget_spec hε.le w.nonprivateCount)

/-- Any upper bound on the number of nonprivate gates suffices for the budget, the case without gate
included. Source: `04-compression.tex`, lines 199–227. -/
theorem rectangularTraceNorm_sourceOnly_density_sub_le_half_of_count_le [DecidableEq Phys]
    {r M : ℕ} {S ε : ℝ} (hε : 0 < ε) (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S)
    (hcount : w.nonprivateCount ≤ M) (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1)
    (x : EuclideanSpace ℂ (Config X)) (hx : ‖x‖ ≤ 1) :
    rectangularTraceNorm (w.replacementPhysicalDensity (sourceGateBudget_pos hε M) hb K x -
      w.physicalDensity K x) ≤ ε / 2 := by
  have he := w.rectangularTraceNorm_sourceOnly_density_sub_le (sourceGateBudget_pos hε M) hb
    K hK x hx
  have hc : (w.nonprivateCount : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcount
  exact he.trans ((mul_le_mul_of_nonneg_left hc
    (mul_nonneg (by norm_num) (sourceGateBudget_pos hε M).le)).trans
      (sourceGateBudget_spec hε.le M))

/-- **The source-only reduction on the source's product input**: every party holds an arbitrary unit
vector `φ p` of its whole private memory. Source: `04-compression.tex`, lines 137–139 and 199–229.
-/
theorem rectangularTraceNorm_sourceOnly_wholeParty_density_sub_le_half [DecidableEq Phys]
    {r : ℕ} {S ε : ℝ} (hε : 0 < ε) (φ : ∀ p, EuclideanSpace ℂ (X p)) (hφ : ∀ p, ‖φ p‖ = 1)
    (w : OriginalCircuit X Y) (hb : w.IsExpansionBounded r S)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1) :
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    rectangularTraceNorm (w.replacementPhysicalDensity
        (sourceGateBudget_pos hε w.nonprivateCount) hb K ψ - w.physicalDensity K ψ) ≤ ε / 2 :=
  w.rectangularTraceNorm_sourceOnly_density_sub_le_half hε hb K hK _
    (norm_toLp_productVector_eq_one φ hφ).le

/-- **The source-only reduction with the regional readout**: one physical register of dimension `d
p` at every party, the exterior physical registers and the private registers discarded; no bound on
the private dimensions. Source: `04-compression.tex`, lines 137–152, 199–231 and 357–363. -/
theorem rectangularTraceNorm_sourceOnly_regional_density_sub_le_half {r M : ℕ} {S ε : ℝ}
    (hε : 0 < ε) (φ : ∀ p, EuclideanSpace ℂ (X p)) (hφ : ∀ p, ‖φ p‖ = 1) (d : P → ℕ)
    (V : P → Type) [∀ p, Fintype (V p)] [∀ p, DecidableEq (V p)]
    (w : OriginalCircuit X (physicalSystem d V)) (hb : w.IsExpansionBounded r S)
    (hcount : w.nonprivateCount ≤ M) (A : Finset P) :
    let ψ : EuclideanSpace ℂ (Config X) := WithLp.toLp 2 (productVector fun p x ↦ φ p x)
    rectangularTraceNorm (w.replacementPhysicalDensity (sourceGateBudget_pos hε M) hb
        (regionalReadout d V A) ψ - w.physicalDensity (regionalReadout d V A) ψ) ≤ ε / 2 :=
  w.rectangularTraceNorm_sourceOnly_density_sub_le_half_of_count_le hε hb hcount _
    (norm_regionalReadout_le_one d V A) _ (norm_toLp_productVector_eq_one φ hφ).le

end OriginalCircuit

end QuantumCircuit.Party
