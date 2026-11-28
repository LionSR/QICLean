/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.BipartiteCopies
import QICLean.Channel.Entanglement.MaxEntangledOverlap
import QICLean.Circuit.Model.LOCC

/-!
# Operational entanglement distillation rates and uniform Bell-overlap obstruction

This module defines operational entanglement distillation rates and distillable entanglement
`E_D^P(ρ)` parameterized by a bipartite protocol class `P` acting on actual bipartite matrix
states and linear superoperators, together with a general uniform two-qubit Bell-overlap-cap
zero-distillation criterion.

## Modeling conventions

* **Input and target states:** `n` copies of `ρ : Matrix (A × B) (A × B) ℂ` are represented
  in the party-major basis `(Fin n → A) × (Fin n → B)` via `QuantumInfo.bipartiteCopies n ρ`.
  The target of `k` Bell pairs (ebits) is
  `QuantumInfo.bellPairTarget k = bipartiteCopies k (omegaProj 2)` on
  `(Fin k → Fin 2) × (Fin k → Fin 2)`.
* **Achievable rates:** a nonnegative rate `r : NNReal` is achievable under `P` if there
  exists a sequence of actual bipartite linear superoperators `Λ n` (eventually in `P`)
  mapping `n` party-major copies of `ρ` to `⌊r * n⌋₊` party-major Bell pairs with full
  `Matrix.rectangularTraceNorm` error tending to `0`.
* **Extended-nonnegative values:** `distillableEntanglement P ρ` is defined as a supremum in
  `ENNReal` (avoiding real-valued `sSup` unboundedness defaults), and the finite-blocklength
  minimal error `minDistillationError` is defined as an infimum in `ENNReal` (so an empty
  protocol class has error `⊤`, never `0`).
* **LOCC scope:** `IsBipartiteFiniteRoundLOCC` models finite-round, finite-outcome LOCC via
  `QuantumCircuit.IsFiniteRoundLOCC Bool` (conjugated along `boolConfigEquiv`). No claim
  about infinite-round LOCC or topological closure is made here.
* **Layer discipline:** this module stays in `QICLean.Circuit.Model` with zero `Entropy`
  imports.

## Main definitions

* `QuantumCircuit.BipartiteSuperoperator`, `QuantumCircuit.BipartiteProtocolClass`.
* `QuantumCircuit.ClassLe`, `QuantumCircuit.IsTracePreservingClass`,
  `QuantumCircuit.IsContainedInSeparable`, `QuantumCircuit.IsSeparableTPChannel`,
  `QuantumCircuit.IsBipartiteFiniteRoundLOCC`.
* `QuantumCircuit.minDistillationError` — finite-blocklength `ENNReal` error infimum.
* `QuantumCircuit.IsAchievableDistillationRate` — achievable operational distillation rate.
* `QuantumCircuit.distillableEntanglement` — `ENNReal` distillable entanglement `E_D^P(ρ)`.
* `QuantumCircuit.HasUniformBellOverlapCap` — uniform homogeneous two-qubit Bell-overlap cap
  across all product-Kraus separable operations on `n > 0` copies.

## Main results

* `QuantumCircuit.classLe_isBipartiteFiniteRoundLOCC_isSeparableTPChannel` —
  `LOCC_ℕ ⊆ SEP` at the protocol-class level.
* `QuantumCircuit.distillableEntanglement_mono` — monotonicity under protocol class inclusion.
* `QuantumCircuit.distillableEntanglement_eq_zero_iff` — `E_D^P(ρ) = 0` iff no positive rate
  is achievable.
* `QuantumCircuit.one_sub_le_rectangularTraceNorm_sub_bellPairTarget_of_uniformBellOverlapCap` —
  single-shot trace-norm lower bound `1 - c ≤ ‖S(ρ^{⊗ n}) - Φ₂^{⊗ k}‖₁` for `n > 0`, `k ≥ 1`.
* `QuantumCircuit.distillableEntanglement_eq_zero_of_uniformBellOverlapCap` — if `ρ` has
  trace `1` and satisfies `HasUniformBellOverlapCap ρ c` with `c < 1`, then
  `distillableEntanglement P ρ = 0` for every trace-preserving protocol class `P` contained
  in product-Kraus separable operations (in particular `IsSeparableTPChannel` and
  `IsBipartiteFiniteRoundLOCC`).
* `QuantumCircuit.hasUniformBellOverlapCap_kronecker_half` and
  `QuantumCircuit.distillableEntanglement_kronecker_eq_zero` — every unit-trace PSD product
  state has Bell-overlap cap `1 / 2` and zero distillable entanglement.
* `QuantumCircuit.isAchievableDistillationRate_zero_isSeparableTPChannel` and
  `QuantumCircuit.one_le_distillableEntanglement_omegaProj_two` — non-vacuity checks showing
  rate `0` is achievable for any unit-trace state and rate `1` is achievable for `omegaProj 2`.
-/

open Filter Matrix QuantumInfo Topology
open scoped BigOperators ComplexOrder Kronecker NNReal ENNReal

namespace QuantumCircuit

/-! ### Bipartite protocol classes -/

/-- A bipartite linear superoperator between party-major product bases `A × B` and
`Aout × Bout`. -/
abbrev BipartiteSuperoperator (A B Aout Bout : Type) :=
  Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (Aout × Bout) (Aout × Bout) ℂ

/-- A class of bipartite protocols, given as a predicate on actual linear superoperators
between arbitrary finite party-major product bases. -/
abbrev BipartiteProtocolClass :=
  ∀ {A B Aout Bout : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Aout] [DecidableEq Aout] [Fintype Bout] [DecidableEq Bout],
    BipartiteSuperoperator A B Aout Bout → Prop

/-- Inclusion of bipartite protocol classes. -/
def ClassLe (P Q : BipartiteProtocolClass) : Prop :=
  ∀ {A B Aout Bout : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Aout] [DecidableEq Aout] [Fintype Bout] [DecidableEq Bout]
    {Φ : BipartiteSuperoperator A B Aout Bout},
    P Φ → Q Φ

/-- Every protocol in `P` is trace-preserving. -/
def IsTracePreservingClass (P : BipartiteProtocolClass) : Prop :=
  ∀ {A B Aout Bout : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Aout] [DecidableEq Aout] [Fintype Bout] [DecidableEq Bout]
    {Φ : BipartiteSuperoperator A B Aout Bout},
    P Φ → ∀ X : Matrix (A × B) (A × B) ℂ, (Φ X).trace = X.trace

/-- Every protocol in `P` is realized by a finite product-Kraus `QuantumInfo.SeparableOperation`. -/
def IsContainedInSeparable (P : BipartiteProtocolClass) : Prop :=
  ∀ {A B Aout Bout : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype Aout] [DecidableEq Aout] [Fintype Bout] [DecidableEq Bout]
    {Φ : BipartiteSuperoperator A B Aout Bout},
    P Φ → ∃ S : SeparableOperation A B Aout Bout, S.map = Φ

/-- The class of trace-preserving bipartite channels admitting a finite product-Kraus
`QuantumInfo.SeparableOperation` presentation. -/
def IsSeparableTPChannel : BipartiteProtocolClass :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} Φ ↦
    ∃ S : SeparableOperation _ _ _ _, S.IsTP ∧ S.map = Φ

theorem isTracePreservingClass_isSeparableTPChannel :
    IsTracePreservingClass IsSeparableTPChannel := by
  intro A B Aout Bout _ _ _ _ _ _ _ _ Φ ⟨S, hS, hmap⟩ X
  rw [← hmap]
  exact KrausFamily.trace_map (K := S.toKrausFamily) hS X

theorem isContainedInSeparable_isSeparableTPChannel :
    IsContainedInSeparable IsSeparableTPChannel := by
  intro A B Aout Bout _ _ _ _ _ _ _ _ Φ ⟨S, _, hmap⟩
  exact ⟨S, hmap⟩

theorem IsTracePreservingClass.of_classLe {P Q : BipartiteProtocolClass}
    (hPQ : ClassLe P Q) (hQ : IsTracePreservingClass Q) :
    IsTracePreservingClass P := by
  intro A B Aout Bout _ _ _ _ _ _ _ _ Φ hP X
  exact hQ (hPQ hP) X

theorem IsContainedInSeparable.of_classLe {P Q : BipartiteProtocolClass}
    (hPQ : ClassLe P Q) (hQ : IsContainedInSeparable Q) :
    IsContainedInSeparable P := by
  intro A B Aout Bout _ _ _ _ _ _ _ _ Φ hP
  exact hQ (hPQ hP)

/-- Two-party site-basis family `Bool → Type` assigning `A` to `false` and `B` to `true`. -/
def bipartiteBasis (A B : Type) : Bool → Type
  | false => A
  | true => B

instance instFintypeBipartiteBasis {A B : Type} [Fintype A] [Fintype B] :
    ∀ b : Bool, Fintype (bipartiteBasis A B b)
  | false => inferInstanceAs (Fintype A)
  | true => inferInstanceAs (Fintype B)

instance instDecidableEqBipartiteBasis {A B : Type} [DecidableEq A] [DecidableEq B] :
    ∀ b : Bool, DecidableEq (bipartiteBasis A B b)
  | false => inferInstanceAs (DecidableEq A)
  | true => inferInstanceAs (DecidableEq B)

/-- The class of bipartite party-major channels realized by a finite-round, finite-outcome
LOCC protocol on `Geometry.sites Bool` (conjugated along `boolConfigEquiv`).
This models `LOCC_ℕ` only, not infinite-round LOCC or topological closure. -/
def IsBipartiteFiniteRoundLOCC : BipartiteProtocolClass :=
  fun {A B Aout Bout _ _ _ _ _ _ _ _} Φ ↦
    ∃ Ψ : Matrix (ManyBody.Config (bipartiteBasis A B))
        (ManyBody.Config (bipartiteBasis A B)) ℂ →ₗ[ℂ]
      Matrix (ManyBody.Config (bipartiteBasis Aout Bout))
        (ManyBody.Config (bipartiteBasis Aout Bout)) ℂ,
      IsFiniteRoundLOCC Bool Ψ ∧
      ∀ ρ : Matrix (A × B) (A × B) ℂ,
        Φ ρ = (Ψ (ρ.submatrix (boolConfigEquiv (bipartiteBasis A B))
          (boolConfigEquiv (bipartiteBasis A B)))).submatrix
            (boolConfigEquiv (bipartiteBasis Aout Bout)).symm
            (boolConfigEquiv (bipartiteBasis Aout Bout)).symm

/-- Every bipartite finite-round LOCC protocol is a trace-preserving product-Kraus separable
channel (`LOCC_ℕ ⊆ SEP`). -/
theorem classLe_isBipartiteFiniteRoundLOCC_isSeparableTPChannel :
    ClassLe IsBipartiteFiniteRoundLOCC IsSeparableTPChannel := by
  intro A B Aout Bout _ _ _ _ _ _ _ _ Φ ⟨Ψ, hLOCC, hΦ⟩
  obtain ⟨S, hSTP, hSmap⟩ := hLOCC.exists_separableOperation
  refine ⟨S, hSTP, ?_⟩
  apply LinearMap.ext
  intro ρ
  exact (hSmap ρ).trans (hΦ ρ).symm

/-! ### Finite-blocklength error, achievable distillation rates, and `E_D^P(ρ)` -/

section DistillationDefs

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The `ENNReal`-valued minimal full trace-norm error for converting `n` party-major
copies of `ρ` into `k` party-major Bell pairs using a protocol in class `P`.
If no protocol in `P` exists at this input/output size, the infimum is `⊤`. -/
noncomputable def minDistillationError (P : BipartiteProtocolClass)
    (ρ : Matrix (A × B) (A × B) ℂ) (n k : ℕ) : ℝ≥0∞ :=
  sInf {e : ℝ≥0∞ | ∃ Φ : BipartiteSuperoperator (Fin n → A) (Fin n → B)
      (Fin k → Fin 2) (Fin k → Fin 2),
    P Φ ∧ e = ENNReal.ofReal
      (Matrix.rectangularTraceNorm (Φ (bipartiteCopies n ρ) - bellPairTarget k))}

theorem minDistillationError_eq_top_of_empty (P : BipartiteProtocolClass)
    (ρ : Matrix (A × B) (A × B) ℂ) (n k : ℕ)
    (hempty : ∀ Φ : BipartiteSuperoperator (Fin n → A) (Fin n → B)
      (Fin k → Fin 2) (Fin k → Fin 2), ¬ P Φ) :
    minDistillationError P ρ n k = ⊤ := by
  unfold minDistillationError
  have hset : {e : ℝ≥0∞ | ∃ Φ : BipartiteSuperoperator (Fin n → A) (Fin n → B)
      (Fin k → Fin 2) (Fin k → Fin 2),
      P Φ ∧ e = ENNReal.ofReal
        (Matrix.rectangularTraceNorm (Φ (bipartiteCopies n ρ) - bellPairTarget k))} = ∅ := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro Φ hP
    exact (hempty Φ hP).elim
  rw [hset, sInf_empty]

theorem minDistillationError_le_of_mem (P : BipartiteProtocolClass)
    (ρ : Matrix (A × B) (A × B) ℂ) {n k : ℕ}
    {Φ : BipartiteSuperoperator (Fin n → A) (Fin n → B) (Fin k → Fin 2) (Fin k → Fin 2)}
    (hΦ : P Φ) :
    minDistillationError P ρ n k ≤
      ENNReal.ofReal (Matrix.rectangularTraceNorm (Φ (bipartiteCopies n ρ) - bellPairTarget k)) :=
  sInf_le ⟨Φ, hΦ, rfl⟩

/-- A nonnegative rate `r : ℝ≥0` (in Bell pairs / ebits per copy) is operationally achievable
for distilling `ρ` under the bipartite protocol class `P` if there exists a sequence of
actual protocols `Λ n` (eventually in `P`) mapping `n` party-major copies of `ρ` to
`⌊r * n⌋₊` party-major Bell pairs with full trace-norm error tending to `0`. -/
def IsAchievableDistillationRate (P : BipartiteProtocolClass)
    (ρ : Matrix (A × B) (A × B) ℂ) (r : ℝ≥0) : Prop :=
  ∃ Λ : ∀ n : ℕ,
      BipartiteSuperoperator (Fin n → A) (Fin n → B)
        (Fin (Nat.floor ((r : ℝ) * n)) → Fin 2) (Fin (Nat.floor ((r : ℝ) * n)) → Fin 2),
    (∀ᶠ n : ℕ in atTop, P (Λ n)) ∧
    Tendsto (fun n : ℕ ↦
      Matrix.rectangularTraceNorm
        (Λ n (bipartiteCopies n ρ) - bellPairTarget (Nat.floor ((r : ℝ) * n))))
      atTop (𝓝 0)

/-- The operational distillable entanglement `E_D^P(ρ)` in `ℝ≥0∞`, defined as the supremum
of all achievable rates `r : ℝ≥0` under the protocol class `P`. -/
noncomputable def distillableEntanglement (P : BipartiteProtocolClass)
    (ρ : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  sSup {x : ℝ≥0∞ | ∃ r : ℝ≥0, (r : ℝ≥0∞) = x ∧ IsAchievableDistillationRate P ρ r}

theorem IsAchievableDistillationRate.mono {P Q : BipartiteProtocolClass}
    (hPQ : ClassLe P Q) {ρ : Matrix (A × B) (A × B) ℂ} {r : ℝ≥0}
    (h : IsAchievableDistillationRate P ρ r) :
    IsAchievableDistillationRate Q ρ r := by
  obtain ⟨Λ, hP, herr⟩ := h
  exact ⟨Λ, hP.mono fun _ hn ↦ hPQ hn, herr⟩

/-- Distillable entanglement is monotone under inclusion of protocol classes. -/
theorem distillableEntanglement_mono {P Q : BipartiteProtocolClass}
    (hPQ : ClassLe P Q) (ρ : Matrix (A × B) (A × B) ℂ) :
    distillableEntanglement P ρ ≤ distillableEntanglement Q ρ :=
  sSup_le_sSup fun _ ⟨r, hr, hach⟩ ↦ ⟨r, hr, hach.mono hPQ⟩

/-- Finite-round LOCC distillable entanglement is bounded above by separable-channel
distillable entanglement. -/
theorem distillableEntanglement_isBipartiteFiniteRoundLOCC_le_isSeparableTPChannel
    (ρ : Matrix (A × B) (A × B) ℂ) :
    distillableEntanglement IsBipartiteFiniteRoundLOCC ρ ≤
      distillableEntanglement IsSeparableTPChannel ρ :=
  distillableEntanglement_mono classLe_isBipartiteFiniteRoundLOCC_isSeparableTPChannel ρ

/-- Any achievable rate `r : ℝ≥0` lower-bounds `distillableEntanglement P ρ`. -/
theorem le_distillableEntanglement_of_achievable {P : BipartiteProtocolClass}
    {ρ : Matrix (A × B) (A × B) ℂ} {r : ℝ≥0}
    (h : IsAchievableDistillationRate P ρ r) :
    (r : ℝ≥0∞) ≤ distillableEntanglement P ρ :=
  le_sSup ⟨r, rfl, h⟩

/-- `distillableEntanglement P ρ = 0` if and only if no strictly positive rate is achievable. -/
theorem distillableEntanglement_eq_zero_iff {P : BipartiteProtocolClass}
    {ρ : Matrix (A × B) (A × B) ℂ} :
    distillableEntanglement P ρ = 0 ↔
      ∀ r : ℝ≥0, 0 < r → ¬ IsAchievableDistillationRate P ρ r := by
  constructor
  · intro h0 r hr hach
    have hle : (r : ℝ≥0∞) ≤ 0 := by
      simpa [h0] using le_distillableEntanglement_of_achievable hach
    have hr0 : (r : ℝ≥0∞) = 0 := le_antisymm hle zero_le
    have hr0' : r = 0 := ENNReal.coe_eq_zero.mp hr0
    exact hr.ne' hr0'
  · intro hno
    refine le_antisymm (sSup_le ?_) zero_le
    rintro x ⟨r, rfl, hach⟩
    by_contra hne
    have hr0 : r ≠ 0 := fun h ↦ hne (by simp [h])
    exact hno r (pos_iff_ne_zero.mpr hr0) hach

/-- If rate `r` is achievable under `P`, then the `ENNReal` minimal finite-blocklength
distillation error at target size `⌊r * n⌋₊` tends to `0`. -/
theorem tendsto_minDistillationError_of_achievable {P : BipartiteProtocolClass}
    {ρ : Matrix (A × B) (A × B) ℂ} {r : ℝ≥0}
    (h : IsAchievableDistillationRate P ρ r) :
    Tendsto (fun n : ℕ ↦ minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)))
      atTop (𝓝 0) := by
  obtain ⟨Λ, hP, herr⟩ := h
  have hofReal : Tendsto (fun n : ℕ ↦ ENNReal.ofReal
      (Matrix.rectangularTraceNorm
        (Λ n (bipartiteCopies n ρ) - bellPairTarget (Nat.floor ((r : ℝ) * n)))))
      atTop (𝓝 0) := by
    have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp herr
    rw [ENNReal.ofReal_zero] at hcomp
    exact hcomp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hofReal
    (Eventually.of_forall fun _ ↦ zero_le) ?_
  filter_upwards [hP] with n hPn
  exact minDistillationError_le_of_mem P ρ hPn

/-- Converse to `tendsto_minDistillationError_of_achievable`: if the `ℝ≥0∞` minimal
finite-blocklength error at target size `⌊r * n⌋₊` tends to `0`, then rate `r` is
operationally achievable by an explicit sequence of protocols eventually in `P`.
No nonemptiness of `P` at every `n` is needed: eventual finiteness of the `ℝ≥0∞`
infimum yields eventual membership in `P`, with the zero superoperator used at
exceptional indices. -/
theorem isAchievableDistillationRate_of_tendsto_minDistillationError
    {P : BipartiteProtocolClass} {ρ : Matrix (A × B) (A × B) ℂ} {r : ℝ≥0}
    (h : Tendsto (fun n : ℕ ↦ minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)))
      atTop (𝓝 0)) :
    IsAchievableDistillationRate P ρ r := by
  classical
  have hex : ∀ (n : ℕ), minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) < ⊤ →
      ∃ Φ : BipartiteSuperoperator (Fin n → A) (Fin n → B)
          (Fin (Nat.floor ((r : ℝ) * n)) → Fin 2) (Fin (Nat.floor ((r : ℝ) * n)) → Fin 2),
        P Φ ∧
        ENNReal.ofReal
          (Matrix.rectangularTraceNorm
            (Φ (bipartiteCopies n ρ) - bellPairTarget (Nat.floor ((r : ℝ) * n)))) <
          minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) +
            ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := by
    intro n hlt
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (((n : ℝ) + 1)⁻¹) :=
      ENNReal.ofReal_pos.mpr (by positivity)
    have hlt' : minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) <
        minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) +
          ENNReal.ofReal (((n : ℝ) + 1)⁻¹) :=
      ENNReal.lt_add_right hlt.ne hpos.ne'
    rw [minDistillationError, sInf_lt_iff] at hlt'
    rcases hlt' with ⟨_, ⟨Φ, hPΦ, rfl⟩, hΦlt⟩
    exact ⟨Φ, hPΦ, hΦlt⟩
  let Λ : ∀ n : ℕ, BipartiteSuperoperator (Fin n → A) (Fin n → B)
      (Fin (Nat.floor ((r : ℝ) * n)) → Fin 2) (Fin (Nat.floor ((r : ℝ) * n)) → Fin 2) :=
    fun n ↦
      if hlt : minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) < ⊤ then
        (hex n hlt).choose
      else
        0
  have hfin : ∀ᶠ n : ℕ in atTop,
      minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) < ⊤ :=
    h.eventually (Iio_mem_nhds ENNReal.zero_lt_top)
  refine ⟨Λ, ?_, ?_⟩
  · filter_upwards [hfin] with n hlt
    simp only [Λ, dite_eq_left hlt]
    exact (hex n hlt).choose_spec.1
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    have hsmall : ∀ᶠ n : ℕ in atTop,
        minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) < ENNReal.ofReal (ε / 2) :=
      h.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hhalf))
    have hinv : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1)⁻¹ < ε / 2 := by
      rw [eventually_atTop]
      refine ⟨Nat.ceil ((ε / 2)⁻¹), fun n hn ↦ ?_⟩
      have hceil : (ε / 2)⁻¹ ≤ (n : ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have hlt_inv : (ε / 2)⁻¹ < (n : ℝ) + 1 := by linarith
      have hpos_n : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      exact (inv_lt_comm₀ hpos_n hhalf).mpr hlt_inv
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hsmall.and hinv)
    refine ⟨N, fun n hn ↦ ?_⟩
    obtain ⟨hmin_lt, hinv_lt⟩ := hN n hn
    have hlt : minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) < ⊤ :=
      hmin_lt.trans ENNReal.ofReal_lt_top
    have hchoose : ENNReal.ofReal
        (Matrix.rectangularTraceNorm
          (Λ n (bipartiteCopies n ρ) - bellPairTarget (Nat.floor ((r : ℝ) * n)))) <
        ENNReal.ofReal ε := by
      simp only [Λ, dite_eq_left hlt]
      calc ENNReal.ofReal
            (Matrix.rectangularTraceNorm
              ((hex n hlt).choose (bipartiteCopies n ρ) -
                bellPairTarget (Nat.floor ((r : ℝ) * n))))
          < minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)) +
              ENNReal.ofReal (((n : ℝ) + 1)⁻¹) := (hex n hlt).choose_spec.2
        _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
            add_le_add hmin_lt.le (ENNReal.ofReal_le_ofReal hinv_lt.le)
        _ = ENNReal.ofReal ε := by
            rw [← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]
    have hlt_real :
        Matrix.rectangularTraceNorm
          (Λ n (bipartiteCopies n ρ) - bellPairTarget (Nat.floor ((r : ℝ) * n))) < ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).mp hchoose
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Matrix.rectangularTraceNorm_nonneg _)]
    exact hlt_real

/-- Equivalence between explicit-sequence operational rate achievability and convergence of
the `ℝ≥0∞` finite-blocklength minimal distillation error to `0`. -/
theorem isAchievableDistillationRate_iff_tendsto_minDistillationError
    {P : BipartiteProtocolClass} {ρ : Matrix (A × B) (A × B) ℂ} {r : ℝ≥0} :
    IsAchievableDistillationRate P ρ r ↔
      Tendsto (fun n : ℕ ↦ minDistillationError P ρ n (Nat.floor ((r : ℝ) * n)))
        atTop (𝓝 0) :=
  ⟨tendsto_minDistillationError_of_achievable,
    isAchievableDistillationRate_of_tendsto_minDistillationError⟩

end DistillationDefs

/-! ### Uniform Bell-overlap-cap criterion -/

section UniformBellOverlapCap

/-- Uniform homogeneous two-qubit Bell-overlap cap for `ρ` under all product-Kraus
separable operations on arbitrarily many (`n > 0`) copies of `ρ`: every two-qubit output
`S.map (bipartiteCopies n ρ)` satisfies
`maxEntangledOverlap 2 (S.map (bipartiteCopies n ρ)) ≤
  c * (S.map (bipartiteCopies n ρ)).trace.re`. -/
def HasUniformBellOverlapCap {A B : Type} [Fintype A] [Fintype B]
    (ρ : Matrix (A × B) (A × B) ℂ) (c : ℝ) : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (S : SeparableOperation (Fin n → A) (Fin n → B) (Fin 2) (Fin 2)),
      Matrix.maxEntangledOverlap 2 (S.map (bipartiteCopies n ρ)) ≤
        c * (S.map (bipartiteCopies n ρ)).trace.re

/-- **Single-shot finite-blocklength obstruction from a uniform Bell-overlap cap.**
If `ρ` has trace `1` and satisfies `HasUniformBellOverlapCap ρ c`, then for any `n > 0`,
any `k ≥ 1`, and any product-Kraus separable operation `S` producing `k` qubit pairs
with output trace `1`, the full trace-norm distance to `bellPairTarget k` is at least `1 - c`. -/
theorem one_sub_le_rectangularTraceNorm_sub_bellPairTarget_of_uniformBellOverlapCap
    {A B : Type} [Fintype A] [Fintype B]
    {ρ : Matrix (A × B) (A × B) ℂ} {c : ℝ}
    (hcap : HasUniformBellOverlapCap ρ c)
    {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (S : SeparableOperation (Fin n → A) (Fin n → B) (Fin k → Fin 2) (Fin k → Fin 2))
    (htr : (S.map (bipartiteCopies n ρ)).trace = 1) :
    1 - c ≤ Matrix.rectangularTraceNorm (S.map (bipartiteCopies n ρ) - bellPairTarget k) := by
  let D := keepFirstBellPair hk
  let T := D.comp S
  have hTmap : T.map (bipartiteCopies n ρ) = D.map (S.map (bipartiteCopies n ρ)) :=
    SeparableOperation.map_comp D S (bipartiteCopies n ρ)
  have hTtr : (T.map (bipartiteCopies n ρ)).trace = 1 := by
    rw [hTmap, SeparableOperation.map,
      KrausFamily.trace_map (K := D.toKrausFamily) (isTP_keepFirstBellPair hk), htr]
  have hov_le : Matrix.maxEntangledOverlap 2 (T.map (bipartiteCopies n ρ)) ≤ c := by
    have h := hcap n hn T
    simpa [hTtr] using h
  have hov_ge : 1 - Matrix.rectangularTraceNorm (T.map (bipartiteCopies n ρ) - Matrix.omegaProj 2) ≤
      Matrix.maxEntangledOverlap 2 (T.map (bipartiteCopies n ρ)) :=
    Matrix.one_sub_rectangularTraceNorm_le_maxEntangledOverlap (d := 2) (by decide) _
  have hcontract :
      Matrix.rectangularTraceNorm (T.map (bipartiteCopies n ρ) - Matrix.omegaProj 2) ≤
        Matrix.rectangularTraceNorm (S.map (bipartiteCopies n ρ) - bellPairTarget k) := by
    rw [hTmap]
    exact rectangularTraceNorm_keepFirstBellPair_sub_omegaProj_le hk (S.map (bipartiteCopies n ρ))
  linarith

/-- Under a uniform Bell-overlap cap `c < 1`, no strictly positive distillation rate is
achievable for any trace-preserving protocol class contained in product-Kraus separable
operations. -/
theorem not_isAchievableDistillationRate_of_uniformBellOverlapCap
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {P : BipartiteProtocolClass}
    (hP_tp : IsTracePreservingClass P)
    (hP_sep : IsContainedInSeparable P)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ_tr : ρ.trace = 1)
    {c : ℝ} (hc : c < 1) (hcap : HasUniformBellOverlapCap ρ c)
    {r : ℝ≥0} (hr : 0 < r) :
    ¬ IsAchievableDistillationRate P ρ r := by
  rintro ⟨Λ, hP_ev, herr⟩
  have hpos_gap : 0 < 1 - c := sub_pos.mpr hc
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Matrix.rectangularTraceNorm
        (Λ n (bipartiteCopies n ρ) - bellPairTarget (Nat.floor ((r : ℝ) * n))) < 1 - c :=
    herr.eventually (gt_mem_nhds hpos_gap)
  have hr_pos : (0 : ℝ) < (r : ℝ) := NNReal.coe_pos.mpr hr
  have hfloor_ge : ∀ᶠ n : ℕ in atTop, 1 ≤ Nat.floor ((r : ℝ) * n) := by
    rw [eventually_atTop]
    refine ⟨Nat.ceil ((r : ℝ)⁻¹) + 1, fun n hn ↦ ?_⟩
    apply Nat.le_floor
    have hn1 : (r : ℝ)⁻¹ ≤ (n : ℝ) := by
      have hceil : (r : ℝ)⁻¹ ≤ (Nat.ceil ((r : ℝ)⁻¹) : ℝ) := Nat.le_ceil _
      have hle : (Nat.ceil ((r : ℝ)⁻¹) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_succ_le hn)
      exact hceil.trans hle
    have hmul : (r : ℝ) * (r : ℝ)⁻¹ ≤ (r : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hn1 hr_pos.le
    rw [mul_inv_cancel₀ hr_pos.ne'] at hmul
    simpa using hmul
  have hpos_n : ∀ᶠ n : ℕ in atTop, 0 < n := by
    rw [eventually_atTop]
    exact ⟨1, fun n hn ↦ hn⟩
  obtain ⟨n, hPn, hε, hk, hn⟩ :=
    (hP_ev.and (hsmall.and (hfloor_ge.and hpos_n))).exists
  obtain ⟨S, hSmap⟩ := hP_sep hPn
  have hStr : (S.map (bipartiteCopies n ρ)).trace = 1 := by
    rw [hSmap, hP_tp hPn, trace_bipartiteCopies_eq_one n hρ_tr]
  have hlower :=
    one_sub_le_rectangularTraceNorm_sub_bellPairTarget_of_uniformBellOverlapCap
      hcap hn hk S hStr
  rw [hSmap] at hlower
  linarith

/-- **Uniform Bell-overlap-cap zero-distillation theorem.**
If a unit-trace bipartite state `ρ` satisfies `HasUniformBellOverlapCap ρ c` for some
`c < 1`, then `distillableEntanglement P ρ = 0` for every trace-preserving protocol class
`P` contained in product-Kraus separable operations. -/
theorem distillableEntanglement_eq_zero_of_uniformBellOverlapCap
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {P : BipartiteProtocolClass}
    (hP_tp : IsTracePreservingClass P)
    (hP_sep : IsContainedInSeparable P)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ_tr : ρ.trace = 1)
    {c : ℝ} (hc : c < 1) (hcap : HasUniformBellOverlapCap ρ c) :
    distillableEntanglement P ρ = 0 :=
  distillableEntanglement_eq_zero_iff.mpr fun _ hr ↦
    not_isAchievableDistillationRate_of_uniformBellOverlapCap hP_tp hP_sep hρ_tr hc hcap hr

/-- Convenience corollary for any protocol class contained in `IsSeparableTPChannel`. -/
theorem distillableEntanglement_eq_zero_of_classLe_isSeparableTPChannel
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {P : BipartiteProtocolClass}
    (hP : ClassLe P IsSeparableTPChannel)
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ_tr : ρ.trace = 1)
    {c : ℝ} (hc : c < 1) (hcap : HasUniformBellOverlapCap ρ c) :
    distillableEntanglement P ρ = 0 :=
  distillableEntanglement_eq_zero_of_uniformBellOverlapCap
    (isTracePreservingClass_isSeparableTPChannel.of_classLe hP)
    (isContainedInSeparable_isSeparableTPChannel.of_classLe hP)
    hρ_tr hc hcap

/-- Specialization of the uniform Bell-overlap-cap criterion to finite-round bipartite LOCC. -/
theorem distillableEntanglement_isBipartiteFiniteRoundLOCC_eq_zero_of_uniformBellOverlapCap
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ_tr : ρ.trace = 1)
    {c : ℝ} (hc : c < 1) (hcap : HasUniformBellOverlapCap ρ c) :
    distillableEntanglement IsBipartiteFiniteRoundLOCC ρ = 0 :=
  distillableEntanglement_eq_zero_of_classLe_isSeparableTPChannel
    classLe_isBipartiteFiniteRoundLOCC_isSeparableTPChannel hρ_tr hc hcap

end UniformBellOverlapCap

/-! ### Concrete instantiations: product states and Bell-pair achievability -/

section ConcreteExamples

/-- Every product of positive semidefinite matrices satisfies the uniform two-qubit
Bell-overlap cap with `c = 1 / 2`. -/
theorem hasUniformBellOverlapCap_kronecker_half
    {A B : Type} [Fintype A] [Fintype B]
    {ρA : Matrix A A ℂ} {ρB : Matrix B B ℂ}
    (hA : ρA.PosSemidef) (hB : ρB.PosSemidef) :
    HasUniformBellOverlapCap (ρA ⊗ₖ ρB) (1 / 2) := by
  intro n _ S
  rw [bipartiteCopies_kronecker, SeparableOperation.map_kronecker]
  have hAn : (Matrix.piKronecker fun _ : Fin n ↦ ρA).PosSemidef :=
    Matrix.piKronecker_posSemidef _ fun _ ↦ hA
  have hBn : (Matrix.piKronecker fun _ : Fin n ↦ ρB).PosSemidef :=
    Matrix.piKronecker_posSemidef _ fun _ ↦ hB
  let σ : S.Index → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := fun i ↦
    (S.left i * (Matrix.piKronecker fun _ : Fin n ↦ ρA) * (S.left i)ᴴ) ⊗ₖ
    (S.right i * (Matrix.piKronecker fun _ : Fin n ↦ ρB) * (S.right i)ᴴ)
  have hppt : ∀ i ∈ (Finset.univ : Finset S.Index), (σ i).IsPPT := fun i _ ↦ by
    rw [Matrix.IsPPT, Matrix.partialTransposeLeft_kronecker]
    exact (hAn.mul_mul_conjTranspose_same (S.left i)).transpose.kronecker
      (hBn.mul_mul_conjTranspose_same (S.right i))
  have hbound :=
    Matrix.maxEntangledOverlap_sum_le_sum_trace_re_div_of_isPPT (d := 2) (by decide)
      Finset.univ σ hppt
  have htr : (∑ i : S.Index, σ i).trace.re = ∑ i : S.Index, (σ i).trace.re := by
    rw [Matrix.trace_sum, Complex.re_sum]
  change Matrix.maxEntangledOverlap 2 (∑ i : S.Index, σ i) ≤
    (1 / 2 : ℝ) * (∑ i : S.Index, σ i).trace.re
  rw [htr]
  linarith

/-- Every unit-trace positive semidefinite product state has zero distillable entanglement
under any trace-preserving protocol class contained in product-Kraus separable operations. -/
theorem distillableEntanglement_kronecker_eq_zero
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {P : BipartiteProtocolClass}
    (hP_tp : IsTracePreservingClass P)
    (hP_sep : IsContainedInSeparable P)
    {ρA : Matrix A A ℂ} {ρB : Matrix B B ℂ}
    (hA : ρA.PosSemidef) (hB : ρB.PosSemidef)
    (hAtr : ρA.trace = 1) (hBtr : ρB.trace = 1) :
    distillableEntanglement P (ρA ⊗ₖ ρB) = 0 := by
  have htr : (ρA ⊗ₖ ρB).trace = 1 := by
    rw [Matrix.trace_kronecker, hAtr, hBtr, mul_one]
  exact distillableEntanglement_eq_zero_of_uniformBellOverlapCap
    hP_tp hP_sep htr (by norm_num) (hasUniformBellOverlapCap_kronecker_half hA hB)

/-- Equivalence identifying `Fin k → Fin 2` with `PUnit` when `k = 0`. -/
private def finZeroArrowEquivPUnit {k : ℕ} (hk : k = 0) : (Fin k → Fin 2) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ i := Fin.elim0 (hk ▸ i)
  left_inv _ := funext fun i ↦ Fin.elim0 (hk ▸ i)
  right_inv _ := rfl

/-- Rate `0` is achievable under `IsSeparableTPChannel` for any unit-trace bipartite matrix. -/
theorem isAchievableDistillationRate_zero_isSeparableTPChannel
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.trace = 1) :
    IsAchievableDistillationRate IsSeparableTPChannel ρ 0 := by
  let e : ∀ n : ℕ, (Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2) ≃ PUnit :=
    fun n ↦ finZeroArrowEquivPUnit (by simp)
  let KA : ∀ n : ℕ, KrausFamily (Fin n → A) (Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2) :=
    fun n ↦ (KrausFamily.discard (Fin n → A)).reindex (Equiv.refl _) (e n)
  let KB : ∀ n : ℕ, KrausFamily (Fin n → B) (Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2) :=
    fun n ↦ (KrausFamily.discard (Fin n → B)).reindex (Equiv.refl _) (e n)
  let S : ∀ n : ℕ, SeparableOperation (Fin n → A) (Fin n → B)
      (Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2)
      (Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2) := fun n ↦
    { Index := (KA n).Index × (KB n).Index
      left := fun p ↦ (KA n).op p.1
      right := fun p ↦ (KB n).op p.2 }
  have hSTP : ∀ n : ℕ, (S n).IsTP := fun n ↦
    ((KrausFamily.isTP_discard (Fin n → A)).reindex _ _).prod
      ((KrausFamily.isTP_discard (Fin n → B)).reindex _ _)
  refine ⟨fun n ↦ (S n).map, Eventually.of_forall fun n ↦ ⟨S n, hSTP n, rfl⟩, ?_⟩
  have hzero : ∀ n : ℕ,
      Matrix.rectangularTraceNorm
        ((S n).map (bipartiteCopies n ρ) -
          bellPairTarget (Nat.floor (((0 : ℝ≥0) : ℝ) * n))) = 0 := by
    intro n
    let u0 : Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2 := (e n).symm PUnit.unit
    have hsub : ∀ x : Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2, x = u0 := fun x ↦ by
      apply (e n).injective
      exact Subsingleton.elim _ _
    have hEq : (S n).map (bipartiteCopies n ρ) =
        bellPairTarget (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) := by
      have htr1 : ((S n).map (bipartiteCopies n ρ)).trace = 1 := by
        rw [SeparableOperation.map,
          KrausFamily.trace_map (K := (S n).toKrausFamily) (hSTP n),
          trace_bipartiteCopies_eq_one n hρ]
      have htr2 : (bellPairTarget (Nat.floor (((0 : ℝ≥0) : ℝ) * n))).trace = 1 :=
        trace_bellPairTarget _
      have huniv :
          (Finset.univ : Finset ((Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2) ×
            (Fin (Nat.floor (((0 : ℝ≥0) : ℝ) * n)) → Fin 2))) = {(u0, u0)} := by
        ext ⟨x, y⟩
        rw [hsub x, hsub y]
        exact ⟨fun _ ↦ Finset.mem_singleton_self _, fun _ ↦ Finset.mem_univ _⟩
      ext ⟨x, y⟩ ⟨x', y'⟩
      rw [hsub x, hsub y, hsub x', hsub y']
      have h1 : ((S n).map (bipartiteCopies n ρ)) (u0, u0) (u0, u0) =
          ((S n).map (bipartiteCopies n ρ)).trace := by
        change _ = ∑ i ∈ Finset.univ, ((S n).map (bipartiteCopies n ρ)) i i
        rw [huniv, Finset.sum_singleton]
      have h2 : (bellPairTarget (Nat.floor (((0 : ℝ≥0) : ℝ) * n))) (u0, u0) (u0, u0) =
          (bellPairTarget (Nat.floor (((0 : ℝ≥0) : ℝ) * n))).trace := by
        change _ = ∑ i ∈ Finset.univ, (bellPairTarget (Nat.floor (((0 : ℝ≥0) : ℝ) * n))) i i
        rw [huniv, Finset.sum_singleton]
      rw [h1, h2, htr1, htr2]
    rw [hEq, sub_self, Matrix.rectangularTraceNorm_zero]
  simp_rw [hzero]
  exact tendsto_const_nhds

/-- Rate `1` is achievable for the two-qubit Bell state `Matrix.omegaProj 2` under
`IsSeparableTPChannel`. -/
theorem isAchievableDistillationRate_one_omegaProj_two :
    IsAchievableDistillationRate IsSeparableTPChannel (Matrix.omegaProj 2) 1 := by
  let e : ∀ n : ℕ, (Fin (Nat.floor (((1 : ℝ≥0) : ℝ) * n)) → Fin 2) ≃ (Fin n → Fin 2) :=
    fun n ↦ Equiv.arrowCongr (finCongr (by simp)) (Equiv.refl (Fin 2))
  let U : ∀ n : ℕ, Matrix (Fin (Nat.floor (((1 : ℝ≥0) : ℝ) * n)) → Fin 2) (Fin n → Fin 2) ℂ :=
    fun n ↦ (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ).submatrix (e n) id
  have hU_isom : ∀ n : ℕ, (U n)ᴴ * U n = 1 := fun n ↦ by
    change ((1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ).submatrix (e n) (Equiv.refl _))ᴴ *
      (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ).submatrix (e n) (Equiv.refl _) = 1
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.conjTranspose_one,
      Matrix.mul_one, Matrix.submatrix_one_equiv]
  let S : ∀ n : ℕ, SeparableOperation (Fin n → Fin 2) (Fin n → Fin 2)
      (Fin (Nat.floor (((1 : ℝ≥0) : ℝ) * n)) → Fin 2)
      (Fin (Nat.floor (((1 : ℝ≥0) : ℝ) * n)) → Fin 2) := fun n ↦
    SeparableOperation.single (U n) (U n)
  have hSTP : ∀ n : ℕ, (S n).IsTP := fun n ↦ by
    rw [SeparableOperation.IsTP, KrausFamily.isTP_iff_effect_eq_one, KrausFamily.effect]
    change (∑ _ : Unit, (U n ⊗ₖ U n)ᴴ * (U n ⊗ₖ U n)) = 1
    rw [Fintype.sum_unique, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hU_isom n, Matrix.one_kronecker_one]
  refine ⟨fun n ↦ (S n).map, Eventually.of_forall fun n ↦ ⟨S n, hSTP n, rfl⟩, ?_⟩
  have hzero : ∀ n : ℕ,
      Matrix.rectangularTraceNorm
        ((S n).map (bipartiteCopies n (Matrix.omegaProj 2)) -
          bellPairTarget (Nat.floor (((1 : ℝ≥0) : ℝ) * n))) = 0 := by
    intro n
    have hEq : (S n).map (bipartiteCopies n (Matrix.omegaProj 2)) =
        bellPairTarget (Nat.floor (((1 : ℝ≥0) : ℝ) * n)) := by
      rw [SeparableOperation.map_single]
      ext ⟨xA, xB⟩ ⟨yA, yB⟩
      have hL : ∀ p : (Fin n → Fin 2) × (Fin n → Fin 2),
          (U n ⊗ₖ U n) (xA, xB) p = if p = (e n xA, e n xB) then 1 else 0 := by
        rintro ⟨pA, pB⟩
        simp only [U, Matrix.kroneckerMap_apply, Matrix.submatrix_apply, id_eq,
          Matrix.one_apply, Prod.mk.injEq]
        split_ifs <;> simp_all
      have hR : ∀ q : (Fin n → Fin 2) × (Fin n → Fin 2),
          (U n ⊗ₖ U n)ᴴ q (yA, yB) = if q = (e n yA, e n yB) then 1 else 0 := by
        rintro ⟨qA, qB⟩
        simp only [U, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
          Matrix.submatrix_apply, id_eq, Matrix.one_apply, Prod.mk.injEq]
        split_ifs <;> simp_all
      have hmul : ((U n ⊗ₖ U n) * bipartiteCopies n (Matrix.omegaProj 2) * (U n ⊗ₖ U n)ᴴ)
          (xA, xB) (yA, yB) =
          bipartiteCopies n (Matrix.omegaProj 2) (e n xA, e n xB) (e n yA, e n yB) := by
        simp only [Matrix.mul_apply]
        trans (∑ q : (Fin n → Fin 2) × (Fin n → Fin 2),
            (∑ p : (Fin n → Fin 2) × (Fin n → Fin 2),
              (if p = (e n xA, e n xB) then (1 : ℂ) else 0) *
                bipartiteCopies n (Matrix.omegaProj 2) p q) *
              (if q = (e n yA, e n yB) then (1 : ℂ) else 0))
        · refine Finset.sum_congr rfl fun q _ ↦ ?_
          rw [hR q]
          congr 1
          refine Finset.sum_congr rfl fun p _ ↦ ?_
          rw [hL p]
        · simp
      rw [hmul, bellPairTarget, bipartiteCopies_apply, bipartiteCopies_apply]
      let f : Fin (Nat.floor (((1 : ℝ≥0) : ℝ) * n)) ≃ Fin n := finCongr (by simp)
      have heval : ∀ (g : Fin (Nat.floor (((1 : ℝ≥0) : ℝ) * n)) → Fin 2)
          (i : Fin (Nat.floor (((1 : ℝ≥0) : ℝ) * n))), e n g (f i) = g i := by
        intro g i
        change g (f.symm (f i)) = g i
        rw [Equiv.symm_apply_apply]
      exact (Fintype.prod_equiv f _ _ fun i ↦ by
        rw [heval xA i, heval xB i, heval yA i, heval yB i]).symm
    rw [hEq, sub_self, Matrix.rectangularTraceNorm_zero]
  simp_rw [hzero]
  exact tendsto_const_nhds

/-- The two-qubit Bell state `Matrix.omegaProj 2` has distillable entanglement at least `1`
under `IsSeparableTPChannel`. -/
theorem one_le_distillableEntanglement_omegaProj_two :
    (1 : ℝ≥0∞) ≤ distillableEntanglement IsSeparableTPChannel (Matrix.omegaProj 2) :=
  le_distillableEntanglement_of_achievable isAchievableDistillationRate_one_omegaProj_two

end ConcreteExamples

end QuantumCircuit
