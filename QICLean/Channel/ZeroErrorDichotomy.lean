/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.QuantumWielandt
import QICLean.Channel.FixedPoint.Cesaro
import QICLean.Channel.FixedPoint.FullRankFixedPointAlgebra
import QICLean.Channel.Irreducible.FromSpectral
import QICLean.Channel.Peripheral.IrreducibleChannel
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity

/-!
# The zero-error dichotomy for channels with a full-rank fixed point

A channel `E` can transmit one bit with zero error in a single use if two input states have
orthogonal outputs. For a channel with a full-rank fixed point, either every power `Eⁿ` can
transmit a bit with zero error, or the power `E^q` at the quantum Wielandt index `q` cannot.

If the fixed points are not all multiples of the full-rank one, the positive and negative parts
of a traceless Hermitian fixed point give two orthogonal fixed states. Otherwise the channel is
irreducible. If it is not primitive, a peripheral eigenvalue `μ ≠ 1` is a root of unity of some
order `p`, so `E^p` has two orthogonal fixed states `σ₀, σ₁`; for every `n` the inputs
`E^m σᵢ` with `n + m ≡ 0 (mod p)` have the orthogonal outputs `σᵢ`. If it is primitive, `E^q`
maps every nonzero positive input to a full-rank output, so no two outputs are orthogonal.

## Main results

* `HasOneShotZeroErrorBit`: two input states with orthogonal outputs.
* `Kraus.zeroError_dichotomy`: Sanz, Pérez-García, Wolf and Cirac, arXiv:0909.5347,
  Theorem `thm:zero`, in its one-shot form.

## References

* M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac, *A quantum version of Wielandt's
  inequality*, arXiv:0909.5347, Theorem 2 (`thm:zero`), lines 736--771 of `main.tex`. The
  footnote to the theorem allows the one-shot zero-error capacity, which is the version proved
  here; the asymptotic statement for `n ≥ q` additionally invokes Cubitt et al. and is not
  formalized.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A map **transmits one bit with zero error in a single use** if two density matrices have
orthogonal outputs, `tr(E(ρ₀) E(ρ₁)) = 0`. This is the statement `C₀(E) ≥ 1` for the one-shot
zero-error classical capacity; its negation is `C₀(E) = 0`. -/
def HasOneShotZeroErrorBit (E : Mat →ₗ[ℂ] Mat) : Prop :=
  ∃ ρ₀ ∈ densityMatrices D, ∃ ρ₁ ∈ densityMatrices D, (E ρ₀ * E ρ₁).trace = 0

namespace Kraus

/-- Two orthogonal fixed states from a positive semidefinite fixed point that is not a multiple
of a positive definite one. The positive and negative parts of the traceless Hermitian fixed
point `σ - (tr σ / tr ρ) ρ` are nonzero, orthogonal and fixed. Wolf, Proposition 6.8. -/
theorem exists_orthogonal_fixed_densities [NeZero D] (E : Mat →ₗ[ℂ] Mat) (hE : IsPositiveMap E)
    (hTP : IsTracePreservingMap E) {ρ σ : Mat} (hρ : ρ.PosDef) (hρfix : E ρ = ρ)
    (hσ : σ.PosSemidef) (hσfix : E σ = σ) (hne : ¬ ∃ c : ℂ, σ = c • ρ) :
    ∃ τ₀ ∈ densityMatrices D, ∃ τ₁ ∈ densityMatrices D,
      E τ₀ = τ₀ ∧ E τ₁ = τ₁ ∧ (τ₀ * τ₁).trace = 0 := by
  have hreal : ∀ {A : Mat}, A.PosSemidef → A.trace = ((A.trace.re : ℝ) : ℂ) := fun hA ↦
    (Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm))
  have hρtr : 0 < ρ.trace.re := by
    have h := hρ.trace_pos
    exact (Complex.pos_iff.mp h).1
  let t : ℝ := σ.trace.re / ρ.trace.re
  let X : Mat := σ - (t : ℂ) • ρ
  have hXherm : X.IsHermitian := by
    simp only [IsHermitian, X, conjTranspose_sub, conjTranspose_smul, hσ.isHermitian.eq,
      hρ.isHermitian.eq, Complex.star_def, Complex.conj_ofReal]
  have hXfix : E X = X := by simp [X, map_sub, hσfix, hρfix]
  have hXtr : X.trace = 0 := by
    simp only [X, trace_sub, trace_smul, smul_eq_mul]
    rw [hreal hσ, hreal hρ.posSemidef]
    simp only [t]
    push_cast
    field_simp [hρtr.ne']
    ring
  have hX0 : X ≠ 0 := fun h ↦ hne ⟨(t : ℂ), sub_eq_zero.mp h⟩
  obtain ⟨hPfix, hNfix⟩ := hE.posPart_negPart_fixed_of_hermitian_fixedPoint E hTP hXherm hXfix
  have hXsa : IsSelfAdjoint X := isSelfAdjoint_iff.mpr hXherm
  have hP : (X⁺).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg X)
  have hN : (X⁻).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg X)
  have hdecomp : X = X⁺ - X⁻ := (CFC.posPart_sub_negPart X hXsa).symm
  have htrPN : (X⁺).trace = (X⁻).trace := by
    have := congrArg Matrix.trace hdecomp
    rw [hXtr, trace_sub] at this
    exact (sub_eq_zero.mp this.symm)
  have hPne : X⁺ ≠ 0 := by
    intro h
    apply hX0
    have hN0 : X⁻ = 0 := (hN.trace_eq_zero_iff).mp (by rw [← htrPN, h, trace_zero])
    rw [hdecomp, h, hN0, sub_zero]
  have hNne : X⁻ ≠ 0 := by
    intro h
    apply hX0
    have hP0 : X⁺ = 0 := (hP.trace_eq_zero_iff).mp (by rw [htrPN, h, trace_zero])
    rw [hdecomp, h, hP0, sub_zero]
  have hdens : ∀ {A : Mat}, A.PosSemidef → A ≠ 0 →
      ((A.trace)⁻¹ • A) ∈ densityMatrices D := by
    intro A hA hA0
    have htr0 : A.trace ≠ 0 := fun h ↦ hA0 ((hA.trace_eq_zero_iff).mp h)
    refine ⟨hA.smul ?_, ?_⟩
    · rw [hreal hA, ← Complex.ofReal_inv]
      exact Complex.zero_le_real.mpr (inv_nonneg.mpr (by
        have := (Complex.nonneg_iff.mp hA.trace_nonneg).1
        simpa using this))
    · rw [trace_smul, smul_eq_mul, inv_mul_cancel₀ htr0]
  refine ⟨_, hdens hP hPne, _, hdens hN hNne, ?_, ?_, ?_⟩
  · rw [LinearMap.map_smul, hPfix]
  · rw [LinearMap.map_smul, hNfix]
  · rw [Matrix.smul_mul, Matrix.mul_smul, CFC.posPart_mul_negPart, smul_zero, smul_zero,
      trace_zero]

/-- A fixed point that is not a multiple of a positive definite fixed point yields a positive
semidefinite fixed point that is not a multiple of it, by the four positive fixed parts of
Wolf, Proposition 6.9. -/
theorem exists_posSemidef_fixed_not_smul (E : Mat →ₗ[ℂ] Mat) (hE : IsPositiveMap E)
    (hTP : IsTracePreservingMap E) {ρ X : Mat} (hXfix : E X = X)
    (hne : ¬ ∃ c : ℂ, X = c • ρ) :
    ∃ σ : Mat, σ.PosSemidef ∧ E σ = σ ∧ ¬ ∃ c : ℂ, σ = c • ρ := by
  obtain ⟨P₁, P₂, P₃, P₄, h₁, h₂, h₃, h₄, f₁, f₂, f₃, f₄, hX⟩ :=
    hE.exists_posSemidef_fixedPoints_decomposition E hTP hXfix
  by_contra hall
  push Not at hall
  obtain ⟨c₁, e₁⟩ := hall P₁ h₁ f₁
  obtain ⟨c₂, e₂⟩ := hall P₂ h₂ f₂
  obtain ⟨c₃, e₃⟩ := hall P₃ h₃ f₃
  obtain ⟨c₄, e₄⟩ := hall P₄ h₄ f₄
  apply hne
  refine ⟨(2⁻¹ : ℂ) * (c₁ - c₂) - ((2⁻¹ : ℂ) * Complex.I) * (c₃ - c₄), ?_⟩
  rw [hX, e₁, e₂, e₃, e₄, ← sub_smul, ← sub_smul, smul_smul, smul_smul, ← sub_smul]

/-- A fixed point of a linear map is fixed by all its powers. -/
theorem pow_apply_of_apply_eq (E : Mat →ₗ[ℂ] Mat) {X : Mat} (hX : E X = X) (k : ℕ) :
    (E ^ k) X = X := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Module.End.mul_apply, hX, ih]

open Classical in
/-- **The zero-error dichotomy.** Let `K` be a trace-preserving Kraus family on `M_D(ℂ)` whose
channel has a full-rank fixed point. Then either every power of the channel transmits one bit
with zero error in a single use, or the power at the quantum Wielandt index does not.

Source: Sanz, Pérez-García, Wolf and Cirac, arXiv:0909.5347, Theorem 2 (`thm:zero`), lines
736--771, in the one-shot form allowed by its footnote. -/
theorem zeroError_dichotomy [NeZero D] {r : ℕ} (K : Fin r → Mat) (hTP : IsTP K)
    {ρ : Mat} (hρ : IsUnit ρ) (hρfix : mapLM K ρ = ρ) :
    (∀ n : ℕ, HasOneShotZeroErrorBit ((mapLM K) ^ n)) ∨
      ¬ HasOneShotZeroErrorBit ((mapLM K) ^ wielandtIndex K) := by
  let E := mapLM K
  have hCh : IsChannel E := isChannel_mapLM K hTP
  have hPos : IsPositiveMap E := hCh.pos
  -- A positive definite fixed point.
  obtain ⟨ρ', hρ'pd, hρ'fix⟩ : ∃ ρ' : Mat, ρ'.PosDef ∧ E ρ' = ρ' := by
    let F := Matrix.traceAdjointMap E
    have hF : IsPositiveMap F := hPos.traceAdjointMap
    have hF1 : F 1 = 1 := isTracePreservingMap_iff_traceAdjointMap_one.mp hCh.tp
    have hfix : Matrix.traceAdjointMap F ρ = ρ := by
      simpa only [F, Matrix.traceAdjointMap_traceAdjointMap] using hρfix
    obtain ⟨σ, hσ, hσfix⟩ :=
      SchwarzMap.exists_posDef_traceAdjoint_fixedPoint_of_isUnit F hF hF1 hρ hfix
    exact ⟨σ, hσ, by simpa only [F, Matrix.traceAdjointMap_traceAdjointMap] using hσfix⟩
  -- A bit for every power from two orthogonal states fixed by a positive power.
  have hshift : ∀ p : ℕ, 0 < p → ∀ τ₀ ∈ densityMatrices D, ∀ τ₁ ∈ densityMatrices D,
      (E ^ p) τ₀ = τ₀ → (E ^ p) τ₁ = τ₁ → (τ₀ * τ₁).trace = 0 →
      ∀ n : ℕ, HasOneShotZeroErrorBit (E ^ n) := by
    intro p hp τ₀ hτ₀ τ₁ hτ₁ f₀ f₁ horth n
    let m := p - n % p
    have hk : n + m = p * (n / p + 1) := by
      have h1 := Nat.div_add_mod n p
      have h2 := Nat.mod_lt n hp
      dsimp only [m]
      rw [Nat.mul_succ]
      omega
    have hfixk : ∀ k : ℕ, ∀ τ, (E ^ p) τ = τ → (E ^ (p * k)) τ = τ := by
      intro k τ hτ
      induction k with
      | zero => simp
      | succ k ih => rw [Nat.mul_succ, pow_add, Module.End.mul_apply, hτ, ih]
    have hout : ∀ τ, (E ^ p) τ = τ → (E ^ n) ((E ^ m) τ) = τ := by
      intro τ hτ
      rw [← Module.End.mul_apply, ← pow_add, hk]
      exact hfixk _ τ hτ
    have hdensE : ∀ τ ∈ densityMatrices D, (E ^ m) τ ∈ densityMatrices D := by
      intro τ hτ
      have hm := isChannel_pow E hCh m
      exact ⟨hm.pos _ hτ.1, by rw [hm.tp, hτ.2]⟩
    exact ⟨_, hdensE τ₀ hτ₀, _, hdensE τ₁ hτ₁, by rw [hout τ₀ f₀, hout τ₁ f₁]; exact horth⟩
  by_cases hmult : ∃ σ : Mat, σ.PosSemidef ∧ E σ = σ ∧ ¬ ∃ c : ℂ, σ = c • ρ'
  · -- Two independent fixed points.
    obtain ⟨σ, hσ, hσfix, hne⟩ := hmult
    obtain ⟨τ₀, hτ₀, τ₁, hτ₁, f₀, f₁, horth⟩ :=
      exists_orthogonal_fixed_densities E hPos hCh.tp hρ'pd hρ'fix hσ hσfix hne
    exact Or.inl (hshift 1 one_pos τ₀ hτ₀ τ₁ hτ₁ (by simpa using f₀) (by simpa using f₁) horth)
  push Not at hmult
  have hIrr : IsIrreducibleMap E :=
    isIrreducibleMap_of_channel_posDef_fixedPoint_unique E hCh ρ' hρ'pd hρ'fix
      (fun σ hσ hσfix ↦ by
        by_contra h
        push Not at h
        exact hmult σ hσ hσfix |>.elim fun c hc ↦ h c hc)
  by_cases hPrim : IsPrimitive E
  · -- The primitive case: the power at the Wielandt index is positivity improving.
    right
    rintro ⟨ρ₀, hρ₀, ρ₁, hρ₁, horth⟩
    have hFull := hasEventuallyFullWordSpan_of_isIrreducibleMap_of_isPrimitive K hTP hIrr hPrim
    have hq := hasFullWordSpanFrom_wielandtIndex K hFull (wielandtIndex K) le_rfl
    have hspread : ∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan K φ (wielandtIndex K) = ⊤ :=
      fun φ hφ ↦ vectorSpreadSpan_eq_top_of_wordSpan_eq_top K hq φ hφ
    have hne : ∀ {τ : Mat}, τ ∈ densityMatrices D → τ ≠ 0 := fun hτ h ↦ by
      have := hτ.2; rw [h, trace_zero] at this; exact zero_ne_one this
    have h₀ := mapLM_pow_positivityImproving_of_vectorSpreadSpan_eq_top K hspread hρ₀.1 (hne hρ₀)
    have h₁ := mapLM_pow_positivityImproving_of_vectorSpreadSpan_eq_top K hspread hρ₁.1 (hne hρ₁)
    have hpdne : ∀ {A : Mat}, A.PosDef → A ≠ 0 := fun hA h ↦ by
      have := hA.trace_pos; rw [h, trace_zero] at this; exact lt_irrefl _ this
    have hpos := h₀.trace_mul_pos_of_posSemidef_of_ne_zero h₁.posSemidef (hpdne h₁)
    rw [horth] at hpos
    exact lt_irrefl _ hpos
  · -- A peripheral root of unity other than one.
    left
    have hper : ∃ μ ∈ peripheralEigenvalues E, μ ≠ 1 := by
      by_contra h
      push Not at h
      apply hPrim
      ext μ
      refine ⟨fun hμ ↦ h μ hμ, fun hμ ↦ ?_⟩
      rw [Set.mem_singleton_iff] at hμ
      subst hμ
      have hne' : ρ' ≠ 0 := fun h ↦ by
        have := hρ'pd.trace_pos; rw [h, trace_zero] at this; exact lt_irrefl _ this
      exact ⟨hasEigenvalue_of_eigenvector_eq E 1 ρ' (by simp [hρ'fix]) hne', by simp⟩
    obtain ⟨μ, hμ, hμ1⟩ := hper
    obtain ⟨p, hp, hμp⟩ := peripheral_isRootOfUnity_of_irreducible_channel E hCh hIrr μ hμ
    obtain ⟨X, hX⟩ := hμ.1.exists_hasEigenvector
    have hEX : E X = μ • X := hX.apply_eq_smul
    have hpowX : (E ^ p) X = X := by
      have : ∀ k : ℕ, (E ^ k) X = μ ^ k • X := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ, Module.End.mul_apply, hEX, LinearMap.map_smul, ih, smul_smul, ← pow_succ']
      rw [this p, hμp, one_smul]
    have hXne : ¬ ∃ c : ℂ, X = c • ρ' := by
      rintro ⟨c, hc⟩
      apply hμ1
      have h1 : E X = X := by rw [hc, LinearMap.map_smul, hρ'fix]
      rw [hEX] at h1
      have hX0 : X ≠ 0 := hX.2
      have h2 : (μ - 1) • X = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hX0)
    have hChp := isChannel_pow E hCh p
    have hρ'p : (E ^ p) ρ' = ρ' := pow_apply_of_apply_eq E hρ'fix p
    obtain ⟨σ, hσ, hσfix, hne⟩ :=
      exists_posSemidef_fixed_not_smul (E ^ p) hChp.pos hChp.tp hpowX hXne
    obtain ⟨τ₀, hτ₀, τ₁, hτ₁, f₀, f₁, horth⟩ :=
      exists_orthogonal_fixed_densities (E ^ p) hChp.pos hChp.tp hρ'pd hρ'p hσ hσfix hne
    exact hshift p hp τ₀ hτ₀ τ₁ hτ₁ f₀ f₁ horth

end Kraus
