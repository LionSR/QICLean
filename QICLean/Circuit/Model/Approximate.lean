/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra
import QICLean.Channel.Dilation.KrausFamilyTraceNorm
import QICLean.Circuit.Model.Protocol

/-!
# Approximate and asymptotic conversions

A matrix `ρ` is converted into `σ` in depth `T` with error `ε` when a protocol of depth at most
`T` maps `ρ` to within trace norm `ε` of `σ`. A protocol contracts the trace norm of every
matrix, so composing two such conversions adds their depths and their errors. For families
indexed by a size `N`, on a family of geometries, a conversion is asymptotic when its errors tend
to `0` at depths eventually bounded by `C (1 + log (N + 1))^k`; conversion in both directions
is an equivalence relation.

**Scope restriction (enlarged sites, no classical feedforward):** the protocols are those of
`QuantumCircuit.IsProtocol`: unbranched circuits of trace-preserving plain gates, whose onsite
families may enlarge the local bases, with every layer of cells of positive cost counted once
whatever the size of the bases, and with no classical feedforward. The source's intersite gates
act on fixed physical qudits and its protocols allow classical communication; no simulation or
inclusion between the two relations is established. Documented in
`docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

## Main definitions

* `QuantumCircuit.IsApproxConversion` — conversion in depth `T` with trace-norm error `ε`.
* `QuantumCircuit.IsAsymptoticConversion` — vanishing error at polylogarithmic depth.
* `QuantumCircuit.IsPhaseEquivalent` — asymptotic conversion in both directions.

## Main results

* `QuantumCircuit.IsProtocol.rectangularTraceNorm_map_le` — a protocol contracts the trace norm.
* `QuantumCircuit.IsApproxConversion.trans` — composition adds depths and errors.
* `QuantumCircuit.isApproxConversion_zero_iff` — conversion with error `0` is exact.
* `QuantumCircuit.IsApproxConversion.norm_trace_mul_mul_sub_le` — correlations between regions
  with disjoint light cones factorize up to `ε ‖A‖ ‖B‖ (1 + 2‖⊗ₛ σ₀ s‖₁ + ε)`.
* `QuantumCircuit.IsAsymptoticConversion.trans`, `QuantumCircuit.isPhaseEquivalent_equivalence`.

The declarations restate `TNLean/Circuit/Channel/ApproximateConversion.lean` and
`TNLean/Circuit/Channel/AsymptoticConversion.lean` at commit
`75fc22288234ef66239cb4c2fa0b22914cfa5c6b` (Apache-2.0). The changes: the protocols are those of
any geometry instead of a chain, and the families those of any family of geometries; the trace
norm is `rectangularTraceNorm` on the configurations instead of `chainTraceNorm`; the contraction
of the trace norm holds for every input, so composition and the equivalence need no Hermitian
inputs.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, paragraph "Phases of matter".
-/

open Matrix Filter Topology ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S]

section Approximate

variable (Γ : Geometry S) {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

/-- `ρ` is converted into `σ` in depth at most `T` with trace-norm error at most `ε`: some map
realised by a protocol of depth at most `T` sends `ρ` to within trace norm `ε` of `σ`
(arXiv:2103.13367, paragraph "Phases of matter", in the model of the module docstring). -/
def IsApproxConversion (T : ℕ) (ε : ℝ) (ρ : Matrix (Config X) (Config X) ℂ)
    (σ : Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ Φ, IsProtocol Γ T Φ ∧ rectangularTraceNorm (Φ ρ - σ) ≤ ε

variable {Γ}

/-- A protocol contracts the trace norm of every matrix. -/
theorem IsProtocol.rectangularTraceNorm_map_le {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) (A : Matrix (Config X) (Config X) ℂ) :
    rectangularTraceNorm (Φ A) ≤ rectangularTraceNorm A := by
  obtain ⟨c, hc, -, rfl, -⟩ := h
  exact (c.isTP_krausFamily KrausGate.ev hc).rectangularTraceNorm_map_le A

/-- An exact conversion is a conversion with error `0`. -/
theorem IsConversion.isApproxConversion {T : ℕ} {ρ : Matrix (Config X) (Config X) ℂ}
    {σ : Matrix (Config Z) (Config Z) ℂ} (h : IsConversion Γ T ρ σ) :
    IsApproxConversion Γ T 0 ρ σ := by
  obtain ⟨Φ, hΦ, rfl⟩ := h
  exact ⟨Φ, hΦ, by simp [rectangularTraceNorm_zero]⟩

/-- Every matrix is converted into itself in depth `0` with error `0`. -/
theorem IsApproxConversion.refl (ρ : Matrix (Config X) (Config X) ℂ) :
    IsApproxConversion Γ 0 0 ρ ρ :=
  ⟨LinearMap.id, .id, by simp [rectangularTraceNorm_zero]⟩

/-- Larger bounds on the depth and the error keep a conversion. -/
theorem IsApproxConversion.mono {T T' : ℕ} {ε ε' : ℝ} {ρ : Matrix (Config X) (Config X) ℂ}
    {σ : Matrix (Config Z) (Config Z) ℂ} (h : IsApproxConversion Γ T ε ρ σ) (hT : T ≤ T')
    (hε : ε ≤ ε') : IsApproxConversion Γ T' ε' ρ σ :=
  let ⟨Φ, hΦ, herr⟩ := h
  ⟨Φ, hΦ.mono hT, herr.trans hε⟩

/-- Conversions compose, adding their depths and their errors: the second protocol contracts
the first error, and the triangle inequality adds the second. -/
theorem IsApproxConversion.trans {T₁ T₂ : ℕ} {ε₁ ε₂ : ℝ} {ρ : Matrix (Config X) (Config X) ℂ}
    {σ : Matrix (Config Y) (Config Y) ℂ} {τ : Matrix (Config Z) (Config Z) ℂ}
    (h₁ : IsApproxConversion Γ T₁ ε₁ ρ σ) (h₂ : IsApproxConversion Γ T₂ ε₂ σ τ) :
    IsApproxConversion Γ (T₁ + T₂) (ε₁ + ε₂) ρ τ := by
  obtain ⟨Φ₁, hΦ₁, herr₁⟩ := h₁
  obtain ⟨Φ₂, hΦ₂, herr₂⟩ := h₂
  refine ⟨Φ₂ ∘ₗ Φ₁, hΦ₁.comp hΦ₂, ?_⟩
  have h : Φ₂ (Φ₁ ρ) - τ = Φ₂ (Φ₁ ρ - σ) + (Φ₂ σ - τ) := by
    rw [map_sub]
    abel
  rw [LinearMap.comp_apply, h]
  exact (rectangularTraceNorm_add_le _ _).trans
    (add_le_add ((hΦ₂.rectangularTraceNorm_map_le _).trans herr₁) herr₂)

/-- A conversion with error `0` is exact. -/
theorem isApproxConversion_zero_iff {T : ℕ} {ρ : Matrix (Config X) (Config X) ℂ}
    {σ : Matrix (Config Z) (Config Z) ℂ} :
    IsApproxConversion Γ T 0 ρ σ ↔ IsConversion Γ T ρ σ := by
  refine ⟨fun ⟨Φ, hΦ, herr⟩ ↦ ⟨Φ, hΦ, sub_eq_zero.mp ?_⟩, IsConversion.isApproxConversion⟩
  exact (rectangularTraceNorm_eq_zero_iff _).mp
    (le_antisymm herr (rectangularTraceNorm_nonneg _))

omit [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] in
/-- **Approximate factorization of correlations.** On a geometry whose cells have positive
cost, let `σ` be converted in depth `T` with error `ε` from a product `⊗ₛ σ₀ s` of unit-trace
factors, and let `c = ‖⊗ₛ σ₀ s‖₁`. For operators `A`, `B` on regions with disjoint `T`-fold
neighbourhoods,
`|tr(σ AB) - tr(σ A) tr(σ B)| ≤ ε ‖A‖ ‖B‖ (1 + 2c + ε)`; for states `c = 1`.

The exact output `σ'` of the protocol factorizes (`IsConversion.trace_mul_mul_eq`), and each
expectation in `σ` differs from the one in `σ'` by `|tr((σ - σ') X)| ≤ ε ‖X‖`. An input `ρ`
within trace norm `δ` of the product is covered by composing with the identity protocol,
which converts the product into `ρ` in depth `0` with error `δ` (`IsApproxConversion.trans`).

Source: arXiv:2103.13367, main text, Proposition `propQCA2`, eq. `eq:necessary_condition`, whose
exact factorization is made approximate in the trace-norm error of the paragraph "Phases of
matter"; here for product inputs and local channels with ancillas and discarding. -/
theorem IsApproxConversion.norm_trace_mul_mul_sub_le [Fintype Γ.Cell]
    (hpos : ∀ b, 0 < Γ.cost b) {T : ℕ} {ε : ℝ}
    {σ₀ : (s : S) → Matrix (X s) (X s) ℂ} (hσ₀ : ∀ s, (σ₀ s).trace = 1)
    {σ : Matrix (Config Z) (Config Z) ℂ} (h : IsApproxConversion Γ T ε (piKronecker σ₀) σ)
    {R R' : Finset S} (hRR' : Disjoint (Γ.neighbourhood^[T] R) (Γ.neighbourhood^[T] R'))
    {A B : Matrix (Config Z) (Config Z) ℂ} (hA : A ∈ supportedOperators Z R)
    (hB : B ∈ supportedOperators Z R') :
    ‖(σ * (A * B)).trace - (σ * A).trace * (σ * B).trace‖ ≤
      ε * ‖A‖ * ‖B‖ * (1 + 2 * rectangularTraceNorm (piKronecker σ₀) + ε) := by
  obtain ⟨Φ, hΦ, herr⟩ := h
  set σ' := Φ (piKronecker σ₀)
  set c := rectangularTraceNorm (piKronecker σ₀)
  have hexact : (σ' * (A * B)).trace = (σ' * A).trace * (σ' * B).trace :=
    IsConversion.trace_mul_mul_eq hpos hσ₀ ⟨Φ, hΦ, rfl⟩ hRR' hA hB
  set D := σ - σ'
  have hD : rectangularTraceNorm D ≤ ε := by
    have hneg : D = (-1 : ℂ) • (σ' - σ) := by simp [D]
    rw [hneg, rectangularTraceNorm_smul, norm_neg, norm_one, one_mul]
    exact herr
  have hε : 0 ≤ ε := (rectangularTraceNorm_nonneg _).trans hD
  have hσ' : rectangularTraceNorm σ' ≤ c := hΦ.rectangularTraceNorm_map_le _
  have hc : 0 ≤ c := rectangularTraceNorm_nonneg _
  have hsplit (M : Matrix (Config Z) (Config Z) ℂ) :
      (σ * M).trace = (σ' * M).trace + (D * M).trace := by
    rw [← trace_add, ← Matrix.add_mul, add_sub_cancel]
  have hbound (Y M : Matrix (Config Z) (Config Z) ℂ) {r : ℝ} (hY : rectangularTraceNorm Y ≤ r) :
      ‖(Y * M).trace‖ ≤ ‖M‖ * r :=
    (norm_trace_mul_le_l2_opNorm_mul_rectangularTraceNorm Y M).trans
      (mul_le_mul_of_nonneg_left hY (norm_nonneg M))
  have hid : (σ * (A * B)).trace - (σ * A).trace * (σ * B).trace =
      (D * (A * B)).trace - (σ' * A).trace * (D * B).trace -
        (D * A).trace * (σ' * B).trace - (D * A).trace * (D * B).trace := by
    rw [hsplit, hsplit A, hsplit B, hexact]
    ring
  have hAB : ‖A * B‖ ≤ ‖A‖ * ‖B‖ := norm_mul_le A B
  have h₁ := hbound D (A * B) hD
  have h₂ := hbound σ' A hσ'
  have h₃ := hbound D B hD
  have h₄ := hbound D A hD
  have h₅ := hbound σ' B hσ'
  rw [hid]
  calc
    _ ≤ ‖(D * (A * B)).trace‖ + ‖(σ' * A).trace‖ * ‖(D * B).trace‖ +
          ‖(D * A).trace‖ * ‖(σ' * B).trace‖ + ‖(D * A).trace‖ * ‖(D * B).trace‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl (norm_mul _ _).le))
          (norm_mul _ _).le)) (norm_mul _ _).le)
    _ ≤ ‖A‖ * ‖B‖ * ε + (‖A‖ * c) * (‖B‖ * ε) + (‖A‖ * ε) * (‖B‖ * c) +
          (‖A‖ * ε) * (‖B‖ * ε) := by
      gcongr
      exact h₁.trans (mul_le_mul_of_nonneg_right hAB hε)
    _ = _ := by ring

end Approximate

section Asymptotic

variable {V : ℕ → Type} [∀ N, Fintype (V N)] [∀ N, DecidableEq (V N)] (G : ∀ N, Geometry (V N))
  {X Y Z : ∀ N, V N → Type} [∀ N s, Fintype (X N s)] [∀ N s, DecidableEq (X N s)]
  [∀ N s, Fintype (Y N s)] [∀ N s, DecidableEq (Y N s)] [∀ N s, Fintype (Z N s)]
  [∀ N s, DecidableEq (Z N s)]

/-- The family `ρ` is asymptotically converted into `σ` on the family of geometries `G`: the
errors tend to `0` at depths eventually at most `C (1 + log (N + 1))^k`, for constants `C ≥ 0`
and `k` (arXiv:2103.13367, paragraph "Phases of matter", in the model of the module
docstring). -/
def IsAsymptoticConversion (ρ : ∀ N, Matrix (Config (X N)) (Config (X N)) ℂ)
    (σ : ∀ N, Matrix (Config (Z N)) (Config (Z N)) ℂ) : Prop :=
  ∃ (k : ℕ) (C : ℝ) (ε : ℕ → ℝ), 0 ≤ C ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ᶠ N : ℕ in atTop, ∃ T : ℕ, (T : ℝ) ≤ C * (1 + Real.log ((N : ℝ) + 1)) ^ k ∧
      IsApproxConversion (G N) T (ε N) (ρ N) (σ N)

/-- Asymptotic conversion in both directions. -/
def IsPhaseEquivalent (ρ : ∀ N, Matrix (Config (X N)) (Config (X N)) ℂ)
    (σ : ∀ N, Matrix (Config (Z N)) (Config (Z N)) ℂ) : Prop :=
  IsAsymptoticConversion G ρ σ ∧ IsAsymptoticConversion G σ ρ

variable {G}

/-- Every family is asymptotically converted into itself. -/
theorem IsAsymptoticConversion.refl (ρ : ∀ N, Matrix (Config (X N)) (Config (X N)) ℂ) :
    IsAsymptoticConversion G ρ ρ :=
  ⟨0, 0, fun _ ↦ 0, le_rfl, tendsto_const_nhds,
    Eventually.of_forall fun N ↦ ⟨0, by simp, IsApproxConversion.refl (ρ N)⟩⟩

/-- Asymptotic conversions compose: the errors add, and the sum of two polylogarithmic depth
bounds is polylogarithmic. -/
theorem IsAsymptoticConversion.trans {ρ : ∀ N, Matrix (Config (X N)) (Config (X N)) ℂ}
    {σ : ∀ N, Matrix (Config (Y N)) (Config (Y N)) ℂ}
    {τ : ∀ N, Matrix (Config (Z N)) (Config (Z N)) ℂ}
    (h₁ : IsAsymptoticConversion G ρ σ) (h₂ : IsAsymptoticConversion G σ τ) :
    IsAsymptoticConversion G ρ τ := by
  obtain ⟨k₁, C₁, ε₁, hC₁, hε₁, hN₁⟩ := h₁
  obtain ⟨k₂, C₂, ε₂, hC₂, hε₂, hN₂⟩ := h₂
  refine ⟨max k₁ k₂, C₁ + C₂, ε₁ + ε₂, add_nonneg hC₁ hC₂,
    by rw [← add_zero (0 : ℝ)]; exact hε₁.add hε₂, ?_⟩
  filter_upwards [hN₁, hN₂] with N ⟨T₁, hT₁, h₁⟩ ⟨T₂, hT₂, h₂⟩
  refine ⟨T₁ + T₂, ?_, h₁.trans h₂⟩
  have hL : 1 ≤ 1 + Real.log ((N : ℝ) + 1) :=
    le_add_of_nonneg_right (Real.log_nonneg (by linarith [N.cast_nonneg (α := ℝ)]))
  have hk₁ := pow_le_pow_right₀ hL (le_max_left k₁ k₂)
  have hk₂ := pow_le_pow_right₀ hL (le_max_right k₁ k₂)
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hk₁ hC₁, mul_le_mul_of_nonneg_left hk₂ hC₂]

/-- Every family is phase equivalent to itself. -/
theorem IsPhaseEquivalent.refl (ρ : ∀ N, Matrix (Config (X N)) (Config (X N)) ℂ) :
    IsPhaseEquivalent G ρ ρ :=
  ⟨.refl ρ, .refl ρ⟩

/-- Phase equivalence is symmetric. -/
theorem IsPhaseEquivalent.symm {ρ : ∀ N, Matrix (Config (X N)) (Config (X N)) ℂ}
    {σ : ∀ N, Matrix (Config (Z N)) (Config (Z N)) ℂ} (h : IsPhaseEquivalent G ρ σ) :
    IsPhaseEquivalent G σ ρ :=
  ⟨h.2, h.1⟩

/-- Phase equivalence is transitive. -/
theorem IsPhaseEquivalent.trans {ρ : ∀ N, Matrix (Config (X N)) (Config (X N)) ℂ}
    {σ : ∀ N, Matrix (Config (Y N)) (Config (Y N)) ℂ}
    {τ : ∀ N, Matrix (Config (Z N)) (Config (Z N)) ℂ}
    (h₁ : IsPhaseEquivalent G ρ σ) (h₂ : IsPhaseEquivalent G σ τ) : IsPhaseEquivalent G ρ τ :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

variable (G X) in
/-- Phase equivalence is an equivalence relation on the families of matrices on `X`. -/
theorem isPhaseEquivalent_equivalence :
    Equivalence (IsPhaseEquivalent G (X := X) (Z := X)) :=
  ⟨.refl, .symm, .trans⟩

end Asymptotic

end QuantumCircuit
