/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Approximation
import QICLean.Circuit.Party.Original.Density

/-!
# Physical density error of approximate gate expansions

The circuit of the gate maps (`EffectCircuit.evalWithGateMaps`) is compared with the original
circuit obtained by rescaling the approximate gate expansions (`EffectCircuit.rescaledOriginal`).
Both are read by the same readout `K`, any matrix of operator norm at most one, which keeps the
discarded registers; then the discarded part is traced out. The trace-norm error of the
physical densities is at most four times the gate error budget times the number of gates
(`rectangularTraceNorm_rescaledOriginal_density_sub_le`). The densities are subnormalized and no
output norm is divided out.

The remaining results choose the gate error budget. An accuracy `L^(-(n+p+1))` absorbs a gate
count `N ≤ C L^n` once `L ≥ max 1 (16 C)`; for a real target exponent the fixed integer accuracy
exponent `n + ⌈p⌉ + ⌈16 C⌉` works for every `L ≥ 2`, and it lies below the gate budget
`sourceGateBudget (L^(-p) / 2) M`.

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.physicalDensityWithGateMaps`.

## Main results

* `QuantumCircuit.Party.EffectCircuit.rectangularTraceNorm_rescaledOriginal_density_sub_le` and
  its forms `_budget`, `_inv_pow`, `_real_pow`.
* `QuantumCircuit.Party.gateApproximation_error_inv_pow_le`,
  `gateApproximation_error_real_pow_le`, `inversePower_le_sourceGateBudget_half`.
* `QuantumCircuit.Party.EffectCircuit.IsGateApproximation.mono`,
  `isGateApproximation_budget_of_power_bound`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 137–175 and 590–598, and the absolute-error convention after the proof.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

/-! ### Arithmetic of the gate error budget -/

/-- One more inverse power absorbs the coefficient of a polynomial bound on the number of gates,
with an explicit threshold independent of the private dimensions. Source: Theorem 5.2,
`04-compression.tex`, lines 590–598. -/
theorem gateApproximation_error_inv_pow_le (L C : ℝ) (N n p : ℕ) (hL : 1 ≤ L)
    (hC : 16 * C ≤ L) (hN : (N : ℝ) ≤ C * L ^ n) :
    4 * (L ^ (n + p + 1))⁻¹ * N ≤ (L ^ p)⁻¹ / 4 := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  calc
    _ ≤ 4 * (L ^ (n + p + 1))⁻¹ * (C * L ^ n) := mul_le_mul_of_nonneg_left hN (by positivity)
    _ = (16 * C / L) * ((L ^ p)⁻¹ / 4) := by
      rw [pow_succ, pow_add]
      field_simp
      ring
    _ ≤ 1 * ((L ^ p)⁻¹ / 4) :=
      mul_le_mul_of_nonneg_right ((div_le_one hLp).mpr hC) (by positivity)
    _ = (L ^ p)⁻¹ / 4 := one_mul _

/-- For a real target exponent, a fixed integer accuracy exponent absorbs a polynomial number of
gates at every size at least two. Source: Theorem 5.2, `04-compression.tex`, lines 137–175 and
590–598. -/
theorem gateApproximation_error_real_pow_le (L C p : ℝ) (N n : ℕ) (hL : 2 ≤ L)
    (hN : (N : ℝ) ≤ C * L ^ n) :
    4 * (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ * N ≤ L ^ (-p) / 4 := by
  have hLone : 1 ≤ L := le_trans (by norm_num) hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hC : 16 * C ≤ L ^ ⌈16 * C⌉₊ := by
    calc
      _ ≤ (⌈16 * C⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (2 : ℝ) ^ ⌈16 * C⌉₊ := by
        exact_mod_cast (Nat.lt_pow_self (by decide : 1 < 2) (n := ⌈16 * C⌉₊)).le
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hL _
  have hsmall : (L ^ ⌈p⌉₊)⁻¹ ≤ L ^ (-p) := by
    calc
      _ = L ^ (-(⌈p⌉₊ : ℝ)) := by rw [Real.rpow_neg hLpos.le, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hLone (neg_le_neg (Nat.le_ceil p))
  calc
    _ ≤ 4 * (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ * (C * L ^ n) :=
      mul_le_mul_of_nonneg_left hN (by positivity)
    _ = (16 * C / L ^ ⌈16 * C⌉₊) * ((L ^ ⌈p⌉₊)⁻¹ / 4) := by
      rw [pow_add, pow_add]
      field_simp
      ring
    _ ≤ 1 * ((L ^ ⌈p⌉₊)⁻¹ / 4) :=
      mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).mpr hC) (by positivity)
    _ ≤ L ^ (-p) / 4 := by
      rw [one_mul]
      exact div_le_div_of_nonneg_right hsmall (by norm_num)

/-- A fixed inverse-power gate error is below the gate budget that reserves a quarter of the
target physical error for the approximate gates. Source: Theorem 5.2, `04-compression.tex`,
lines 137–175 and 590–598. -/
theorem inversePower_le_sourceGateBudget_half (L C p : ℝ) (M n : ℕ) (hL : 2 ≤ L)
    (hC : 1 ≤ C) (hM : (M : ℝ) ≤ C * L ^ n) :
    (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ ≤ sourceGateBudget (L ^ (-p) / 2) M := by
  have hLone : 1 ≤ L := le_trans (by norm_num) hL
  have hmax : ((max 1 M : ℕ) : ℝ) ≤ C * L ^ n := by
    rw [Nat.cast_max, Nat.cast_one]
    exact max_le (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hLone)) hM
  have he := gateApproximation_error_real_pow_le L C p (max 1 M) n hL hmax
  unfold sourceGateBudget
  apply (le_div_iff₀ (by positivity)).mpr
  linarith

variable {P : Type} [DecidableEq P]

namespace EffectCircuit

/-! ### Monotonicity of the gate approximation -/

/-- A larger gate error budget keeps the same gate maps and the same expansions. Source:
Theorem 5.2, `04-compression.tex`, lines 590–598. -/
theorem IsGateApproximation.mono {δ δ' : ℝ} : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → {c : EffectCircuit X Y} → {G : c.GateMaps} →
      c.IsGateApproximation δ G → δ ≤ δ' → c.IsGateApproximation δ' G
  | _, _, _, _, PartyCircuit.done _, _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, _, h, hδ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans hδ⟩
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, h, _ => h
  | _, _, _, _, PartyCircuit.localOps _, _, h, _ => h
  | _, _, _, _, PartyCircuit.comp _ _, _, h, hδ => ⟨h.1.mono hδ, h.2.mono hδ⟩

/-- Expansions at one fixed inverse-power accuracy satisfy the gate budget of the requested real
physical accuracy; the exponent depends on the uniform count bound only, not on private
dimensions. Source: Theorem 5.2, `04-compression.tex`, lines 137–175 and 590–598. -/
theorem isGateApproximation_budget_of_power_bound {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] (w : EffectCircuit X Y) (G : w.GateMaps) (L C p : ℝ) (M n : ℕ)
    (hL : 2 ≤ L) (hC : 1 ≤ C) (hM : (M : ℝ) ≤ C * L ^ n)
    (h : w.IsGateApproximation (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ G) :
    w.IsGateApproximation (sourceGateBudget (L ^ (-p) / 2) M) G :=
  h.mono (inversePower_le_sourceGateBudget_half L C p M n hL hC hM)

/-! ### The physical density of the gate maps -/

variable [Fintype P] {Phys Env : Type*} [Fintype Phys] [Fintype Env] {X Y : P → Type}
  [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The physical density of the circuit of the gate maps on the input `x`, read by `K`, the
environment traced out and the subnormalization kept. Source: Theorem 5.2, `04-compression.tex`,
lines 150–153 and 590–598. -/
def physicalDensityWithGateMaps (w : EffectCircuit X Y) (G : w.GateMaps)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (x : EuclideanSpace ℂ (Config X)) :
    Matrix Phys Phys ℂ :=
  let y := Matrix.toEuclideanLin K (Matrix.toEuclideanLin (w.evalWithGateMaps G) x)
  partialTraceRight (euclideanOuterProduct y y)

/-- **The physical density error of the rescaled original circuit** is at most `4 δ N` in trace
norm, `N` the number of gates, for every readout `K` of norm at most one; there is no factor of
the discarded dimension. Source: Theorem 5.2, `04-compression.tex`, lines 590–598. -/
theorem rectangularTraceNorm_rescaledOriginal_density_sub_le [DecidableEq Phys] {δ : ℝ}
    (hδ : 0 ≤ δ) (w : EffectCircuit X Y) (G : w.GateMaps) (h : w.IsGateApproximation δ G)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1) (x : EuclideanSpace ℂ (Config X))
    (hx : ‖x‖ ≤ 1) :
    rectangularTraceNorm ((w.rescaledOriginal hδ G h).physicalDensity K x -
      w.physicalDensityWithGateMaps G K x) ≤ 4 * δ * w.numGates := by
  set R := (w.rescaledOriginal hδ G h).op
  set E := w.evalWithGateMaps G
  have h₁ : ‖Matrix.toEuclideanLin K (Matrix.toEuclideanLin R x)‖ ≤ 1 :=
    ((Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one hK _).trans
      (Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one (OriginalCircuit.norm_op_le_one _)
        x)).trans hx
  have h₂ : ‖Matrix.toEuclideanLin K (Matrix.toEuclideanLin E x)‖ ≤ 1 :=
    ((Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one hK _).trans
      (Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one (w.norm_evalWithGateMaps_le_one G h)
        x)).trans hx
  have hd : ‖Matrix.toEuclideanLin K (Matrix.toEuclideanLin R x) -
      Matrix.toEuclideanLin K (Matrix.toEuclideanLin E x)‖ ≤ 2 * δ * w.numGates := by
    rw [← map_sub, ← LinearMap.sub_apply, ← map_sub]
    refine (Matrix.norm_toEuclideanLin_apply_le_of_norm_le_one hK _).trans
      ((Matrix.l2_opNorm_mulVec _ x).trans ?_)
    exact (mul_le_of_le_one_right (norm_nonneg _) hx).trans
      (w.norm_rescaledOriginal_sub_evalWithGateMaps_le hδ G h)
  rw [OriginalCircuit.physicalDensity_eq]
  exact (rectangularTraceNorm_partialTraceRight_pure_density_sub_le_two _ _ h₁ h₂).trans
    ((mul_le_mul_of_nonneg_left hd (by norm_num)).trans_eq (by ring))

/-- A gate budget chosen from any upper bound `M` on the number of gates uses at most half of the
supplied physical error. Source: Theorem 5.2, `04-compression.tex`, lines 590–598. -/
theorem rectangularTraceNorm_rescaledOriginal_density_sub_le_budget [DecidableEq Phys]
    (w : EffectCircuit X Y) (G : w.GateMaps) {ε : ℝ} (hε : 0 < ε) {M : ℕ}
    (hM : w.numGates ≤ M) (h : w.IsGateApproximation (sourceGateBudget ε M) G)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1) (x : EuclideanSpace ℂ (Config X))
    (hx : ‖x‖ ≤ 1) :
    rectangularTraceNorm ((w.rescaledOriginal (sourceGateBudget_pos hε M).le G h).physicalDensity
      K x - w.physicalDensityWithGateMaps G K x) ≤ ε / 2 := by
  have hc : (w.numGates : ℝ) ≤ M := by exact_mod_cast hM
  exact (w.rectangularTraceNorm_rescaledOriginal_density_sub_le (sourceGateBudget_pos hε M).le
    G h K hK x hx).trans ((mul_le_mul_of_nonneg_left hc
      (mul_nonneg (by norm_num) (sourceGateBudget_pos hε M).le)).trans
        (sourceGateBudget_spec hε.le M))

/-- Gate expansions at a fixed higher inverse-power accuracy give a rescaled original circuit
within a quarter of the requested physical error, compared with the gate maps themselves. Source:
Theorem 5.2, `04-compression.tex`, lines 590–598. -/
theorem rectangularTraceNorm_rescaledOriginal_density_sub_le_inv_pow [DecidableEq Phys]
    (w : EffectCircuit X Y) (G : w.GateMaps) (L C : ℝ) (n p : ℕ) (hL : 1 ≤ L)
    (hC : 16 * C ≤ L) (hN : (w.numGates : ℝ) ≤ C * L ^ n)
    (h : w.IsGateApproximation (L ^ (n + p + 1))⁻¹ G) (K : Matrix (Phys × Env) (Config Y) ℂ)
    (hK : ‖K‖ ≤ 1) (x : EuclideanSpace ℂ (Config X)) (hx : ‖x‖ ≤ 1) :
    let hδ : 0 ≤ (L ^ (n + p + 1))⁻¹ := by positivity
    rectangularTraceNorm ((w.rescaledOriginal hδ G h).physicalDensity K x -
      w.physicalDensityWithGateMaps G K x) ≤ (L ^ p)⁻¹ / 4 := by
  intro hδ
  exact (w.rectangularTraceNorm_rescaledOriginal_density_sub_le hδ G h K hK x hx).trans
    (gateApproximation_error_inv_pow_le L C _ n p hL hC hN)

/-- Gate expansions at one fixed integer accuracy exponent give a quarter of the requested real
inverse-power error, uniformly for all `L ≥ 2` and independently of private dimensions. Source:
Theorem 5.2, `04-compression.tex`, lines 137–175 and 590–598. -/
theorem rectangularTraceNorm_rescaledOriginal_density_sub_le_real_pow [DecidableEq Phys]
    (w : EffectCircuit X Y) (G : w.GateMaps) (L C p : ℝ) (n : ℕ) (hL : 2 ≤ L)
    (hN : (w.numGates : ℝ) ≤ C * L ^ n) (h : w.IsGateApproximation (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ G)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1) (x : EuclideanSpace ℂ (Config X))
    (hx : ‖x‖ ≤ 1) :
    let hδ : 0 ≤ (L ^ (n + ⌈p⌉₊ + ⌈16 * C⌉₊))⁻¹ := by positivity
    rectangularTraceNorm ((w.rescaledOriginal hδ G h).physicalDensity K x -
      w.physicalDensityWithGateMaps G K x) ≤ L ^ (-p) / 4 := by
  intro hδ
  exact (w.rectangularTraceNorm_rescaledOriginal_density_sub_le hδ G h K hK x hx).trans
    (gateApproximation_error_real_pow_le L C p _ n hL hN)

end EffectCircuit

end QuantumCircuit.Party
