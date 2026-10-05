/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ChoiResidual
import QICLean.Channel.OrderedRectangular
import QICLean.Channel.FixedPoint.Cesaro

/-!
# Fixed-window minorization on changing matrix spaces

Local Choi minorization on actual, nonwrapping intervals gives a completely positive
residual for every longer interval. Complete windows contribute their trace scales;
the remaining shorter interval needs only complete positivity and trace preservation.
The matrix spaces may vary, and the minorizing densities need not be faithful or stationary.

For a closed sequence of matrix spaces, compatible reference densities are derived from
a fixed density of the full-cycle channel and transported through the actual suffixes.

## References

* Wolf, *Quantum Channels & Operations*, Theorems 6.11 and 8.17 and Eq. (8.86).
-/

open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {D : ℕ → ℕ}
  (E : ∀ i, Matrix (Fin (D (i + 1))) (Fin (D (i + 1))) ℂ →ₗ[ℂ]
    Matrix (Fin (D i)) (Fin (D i)) ℂ)

/-- A closed sequence of rectangular channels has compatible density matrices on its
actual cut spaces. The closing equality uses only the identification of the endpoint
dimensions; the references are obtained from the full-cycle fixed point. -/
theorem exists_compatible_channelInterval_densities (N : ℕ) (hD : 0 < D 0)
    (hcyc : D N = D 0) (hE : ∀ i, i < N → IsKrausCPTP (E i)) :
    ∃ σ : ∀ a, a ≤ N → Matrix (Fin (D a)) (Fin (D a)) ℂ,
      (∀ a ha, (σ a ha).PosSemidef ∧ (σ a ha).trace = 1) ∧
      σ N le_rfl = equivReindexMap (finCongr hcyc.symm) (σ 0 (Nat.zero_le N)) ∧
      ∀ a b (hab : a ≤ b) (hb : b ≤ N),
        channelInterval E a b hab (σ b hb) = σ a (hab.trans hb) := by
  classical
  let C := equivReindexMap (finCongr hcyc.symm)
  have hC : IsKrausCPTP C := equivReindexMap_isKrausCPTP _
  have hF (a : ℕ) (ha : a ≤ N) : IsKrausCPTP (channelInterval E a N ha) :=
    channelInterval_isKrausCPTP E ha fun i _ hi => hE i hi
  let T := (channelInterval E 0 N (Nat.zero_le N)).comp C
  have hT : IsKrausCPTP T := isKrausCPTP_comp hC (hF 0 (Nat.zero_le N))
  obtain ⟨ρ, hρ, hρne, hfix⟩ := IsPositiveMap.exists_posSemidef_fixedPoint
    (E := T) (fun X hX => hT.map_posSemidef hX) hT.trace_map hD
  have hρtr : ρ.trace ≠ 0 := fun h => hρne (hρ.trace_eq_zero_iff.mp h)
  let θ := ρ.trace⁻¹ • ρ
  have hθ : θ.PosSemidef := hρ.smul (inv_nonneg_of_nonneg hρ.trace_nonneg)
  have hθtr : θ.trace = 1 := by simp [θ, hρtr]
  have hθfix : T θ = θ := by simp [θ, map_smul, hfix]
  let σ (a : ℕ) (ha : a ≤ N) := channelInterval E a N ha (C θ)
  have hσ0 : σ 0 (Nat.zero_le N) = θ := hθfix
  refine ⟨σ, fun a ha => ?_, ?_, fun a b hab hb => ?_⟩
  · exact ⟨(hF a ha).map_posSemidef (hC.map_posSemidef hθ),
      by rw [(hF a ha).trace_map, hC.trace_map, hθtr]⟩
  · change channelInterval E N N le_rfl (C θ) = C (σ 0 (Nat.zero_le N))
    rw [channelInterval_self, LinearMap.id_apply, hσ0]
  · exact congrArg (fun S => S (C θ)) (channelInterval_comp E hab hb)

/-- Fixed-width Choi domination leaves an actual rectangular residual with trace scale
`(1 - η)^floor((b-a)/s)`. Shorter intervals, including the empty interval, contribute
trace scale one. Neither stationarity nor a common matrix space is assumed. -/
theorem exists_channelInterval_residual_of_window_domination
    (N s : ℕ) (hs : 0 < s) (η : ℝ)
    (hD : ∀ i, i ≤ N → 0 < D i)
    (hE : ∀ i, i < N → IsKrausCPTP (E i))
    (hwindow : ∀ a (_ha : a + s ≤ N), ∃ τ : Matrix (Fin (D a)) (Fin (D a)) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (channelInterval E a (a + s) (Nat.le_add_right a s)) ≥
        ((η : ℂ) / D (a + s)) •
          (τ ⊗ₖ (1 : Matrix (Fin (D (a + s))) (Fin (D (a + s))) ℂ)))
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
    ∃ Q : Matrix (Fin (D b)) (Fin (D b)) ℂ →ₗ[ℂ]
        Matrix (Fin (D a)) (Fin (D a)) ℂ,
      IsKrausCP Q ∧
      (∀ X, (Q X).trace = (((1 - η) ^ ((b - a) / s) : ℝ) : ℂ) * X.trace) ∧
      ∀ X, X.trace = 0 → Q X = channelInterval E a b hab X := by
  have hF (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N) :
      IsKrausCPTP (channelInterval E a b hab) :=
    channelInterval_isKrausCPTP E hab fun i _ hi => hE i (hi.trans_le hb)
  suffices ∀ n a b (hab : a ≤ b) (hb : b ≤ N), b - a = n →
      ∃ Q : Matrix (Fin (D b)) (Fin (D b)) ℂ →ₗ[ℂ]
          Matrix (Fin (D a)) (Fin (D a)) ℂ,
        IsKrausCP Q ∧
        (∀ X, (Q X).trace = (((1 - η) ^ (n / s) : ℝ) : ℂ) * X.trace) ∧
        ∀ X, X.trace = 0 → Q X = channelInterval E a b hab X by
    exact this (b - a) a b hab hb rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab hb hn
    by_cases hshort : n < s
    · refine ⟨channelInterval E a b hab, (hF a b hab hb).isKrausCP, ?_, fun X _ => rfl⟩
      intro X
      simp only [Nat.div_eq_of_lt hshort, pow_zero, Complex.ofReal_one, one_mul]
      exact (hF a b hab hb).trace_map X
    · let c := b - s
      have hac : a ≤ c := by dsimp [c]; omega
      have hcb : c ≤ b := Nat.sub_le _ _
      have hcN : c ≤ N := hcb.trans hb
      have hc : c + s = b := by dsimp [c]; omega
      have hless : c - a < n := by dsimp [c]; omega
      obtain ⟨Q, hQ, hQtr, hQzero⟩ := ih (c - a) hless a c hac hcN rfl
      have hw : ∀ b' (hcb' : c ≤ b'), c + s = b' →
          ∃ τ : Matrix (Fin (D c)) (Fin (D c)) ℂ,
            τ.PosSemidef ∧ τ.trace = 1 ∧
            ChoiRectangular.choiMatrix (channelInterval E c b' hcb') ≥
              ((η : ℂ) / D b') •
                (τ ⊗ₖ (1 : Matrix (Fin (D b')) (Fin (D b')) ℂ)) := by
        intro b' hcb' hc'
        subst b'
        exact hwindow c (by omega)
      obtain ⟨τ, _hτ, hτtr, hchoi⟩ := hw b hcb hc
      let : NeZero (D b) := ⟨Nat.ne_of_gt (hD b hb)⟩
      let R := channelInterval E c b hcb -
        (η : ℂ) • tracePrepareMap (α := Fin (D b)) τ
      have hR : IsKrausCP R :=
        isKrausCP_sub_smul_tracePrepareMap_of_choi_domination _ τ η hchoi
      have hRtr (X : Matrix (Fin (D b)) (Fin (D b)) ℂ) :
          (R X).trace = ((1 - η : ℝ) : ℂ) * X.trace :=
        trace_sub_smul_tracePrepareMap _ (hF c b hcb hb).trace_map τ hτtr η X
      have hnDiv : n / s = (c - a) / s + 1 := by
        rw [show n = (c - a) + s by omega, Nat.add_div_right _ hs]
      refine ⟨Q.comp R, isKrausCP_comp hR hQ, ?_, ?_⟩
      · intro X
        rw [LinearMap.comp_apply, hQtr, hRtr, hnDiv, pow_succ]
        push_cast
        ring
      · intro X hX
        have hRX : R X = channelInterval E c b hcb X := by
          simp [R, tracePrepareMap_apply, hX]
        rw [LinearMap.comp_apply, hRX,
          hQzero _ (by rw [(hF c b hcb hb).trace_map, hX])]
        exact congrArg (fun S => S X) (channelInterval_comp E hac hcb)

/-- Actual window minorization gives a Hilbert--Schmidt induced interval estimate relative
to the transported input density. The prefactor uses only the actual input dimension. -/
theorem norm_linearMapMatrix_channelInterval_sub_transport_le_of_window_domination
    (N s : ℕ) (hs : 0 < s) (η : ℝ) (hη : η ≤ 1)
    (hD : ∀ i, i ≤ N → 0 < D i)
    (hE : ∀ i, i < N → IsKrausCPTP (E i))
    (hwindow : ∀ a (_ha : a + s ≤ N), ∃ τ : Matrix (Fin (D a)) (Fin (D a)) ℂ,
      τ.PosSemidef ∧ τ.trace = 1 ∧
      ChoiRectangular.choiMatrix (channelInterval E a (a + s) (Nat.le_add_right a s)) ≥
        ((η : ℂ) / D (a + s)) •
          (τ ⊗ₖ (1 : Matrix (Fin (D (a + s))) (Fin (D (a + s))) ℂ)))
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ N)
    (ρ : Matrix (Fin (D b)) (Fin (D b)) ℂ) (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) :
    ‖linearMapMatrix (channelInterval E a b hab -
      tracePrepareMap (α := Fin (D b)) (channelInterval E a b hab ρ))‖ ≤
        2 * D b * (1 - η) ^ ((b - a) / s) := by
  let : NeZero (D b) := ⟨Nat.ne_of_gt (hD b hb)⟩
  obtain ⟨Q, hQ, hQtr, hQzero⟩ :=
    exists_channelInterval_residual_of_window_domination E N s hs η hD hE hwindow a b hab hb
  exact norm_linearMapMatrix_sub_tracePrepareMap_le_of_residual _ Q hQ _
    (pow_nonneg (sub_nonneg.mpr hη) _) hQtr hQzero ρ hρ hρtr

end Matrix
