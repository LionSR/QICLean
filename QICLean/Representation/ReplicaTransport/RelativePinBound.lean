/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Proposition
import QICLean.Representation.ReplicaEtaForms

/-!
# The relative coherent pin in the form used by the transport estimate

The transport estimate (Proposition 7.4 of the area-law paper, *A two-dimensional area law
from a global spectral gap*, `06-transport.tex`, lines 377–434) was proved assuming
Lemma 6.3 (`lem:relative-pin`, `05-replicas.tex`, lines 486–505) in the form
`TensorPower.ReplicaTransport.RelativePinBound`: a Loewner bound on the band metrics for each
move of one band, with the entropy `I_θ(x:F|P)` for a move to `P` and `I_θ(x:P|F)` for a move
to `F` (`06-transport.tex`, display `transport:move-eta`, lines 315–328). This file proves that
proposition from `TensorPower.relativePin_regionalMovementEta`, and hence states
Proposition 7.4 with the skew bound as its only remaining replica input.

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `Matrix.smul_vecMulVec_le_of_forall` — a rank-one Loewner bound from quadratic forms.
* `TensorPower.ReplicaTransport.relativePinBound` — Lemma 6.3 in the form `RelativePinBound`.
* `TensorPower.ReplicaTransport.transport_of_splitSkewBound` — Proposition 7.4 assuming only
  the split-leaf skew bound.
-/

open scoped Matrix ComplexOrder MatrixOrder unitInterval
open Matrix Set Filter Topology Asymptotics PermutationRepresentation Entropy

noncomputable section

universe u

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

omit [DecidableEq m] in
/-- **A rank-one Loewner bound from quadratic forms**: if `c |⟨z, w⟩|² ≤ ⟨w, M w⟩` for every
`w` and `M` is Hermitian, then `c |z⟩⟨z| ≤ M`. -/
theorem smul_vecMulVec_le_of_forall {M : Matrix m m ℂ} (hM : M.IsHermitian) {c : ℝ}
    {z : m → ℂ} (h : ∀ w, c * ‖star z ⬝ᵥ w‖ ^ 2 ≤ (star w ⬝ᵥ (M *ᵥ w)).re) :
    c • vecMulVec z (star z) ≤ M := by
  have hP : (c • vecMulVec z (star z)).IsHermitian := by
    rw [IsHermitian, conjTranspose_smul, star_trivial,
      (posSemidef_vecMulVec_self_star z).isHermitian.eq]
  rw [Matrix.le_iff]
  refine .of_dotProduct_mulVec_nonneg (hM.sub hP) fun w => ?_
  rw [Complex.nonneg_iff]
  refine ⟨?_, ((hM.sub hP).im_star_dotProduct_mulVec_self w).symm⟩
  have hc : star w ⬝ᵥ z = (starRingEnd ℂ) (star z ⬝ᵥ w) := by
    simp [dotProduct, map_sum, mul_comm]
  have h1 : star w ⬝ᵥ ((c • vecMulVec z (star z)) *ᵥ w) =
      (c : ℂ) * ((‖star z ⬝ᵥ w‖ ^ 2 : ℝ) : ℂ) := by
    rw [smul_mulVec, dotProduct_smul, star_dotProduct_vecMulVec_mulVec, hc, Complex.mul_conj',
      Complex.real_smul]
    push_cast
    ring
  rw [sub_mulVec, dotProduct_sub, Complex.sub_re, h1, ← Complex.ofReal_mul, Complex.ofReal_re]
  linarith [h w]

end Matrix

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

omit [Fintype V] in
theorem logDim_eq (x : Finset V) :
    logDim n x = Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) := by
  rw [logDim, Fintype.card_pi]
  push_cast
  simp only [Fintype.card_fin]
  rw [Finset.prod_coe_sort x fun v => (n v : ℝ)]

/-- A band partition with a valid move of `x` gives the four-part partition `P, x, Y \ x, F`. -/
theorem fourPartition_of_isPartition {π : PYF V} (hπ : π.IsPartition) {x : Finset V}
    (hx : x ⊆ π.Y) : FourPartition π.P x (π.Y \ x) π.F := by
  obtain ⟨hPY, hPF, hYF, hcov⟩ := hπ
  refine ⟨Finset.disjoint_of_subset_right hx hPY,
    Finset.disjoint_of_subset_right Finset.sdiff_subset hPY, hPF, Finset.disjoint_sdiff,
    Finset.disjoint_of_subset_left hx hYF,
    Finset.disjoint_of_subset_left Finset.sdiff_subset hYF, fun v => ?_⟩
  have hv : v ∈ π.P ∪ π.Y ∪ π.F := hcov ▸ Finset.mem_univ v
  simp only [Finset.mem_union] at hv
  by_cases hvx : v ∈ x
  · exact Or.inr (Or.inl hvx)
  · rcases hv with (hv | hv) | hv
    · exact Or.inl hv
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨hv, hvx⟩)))
    · exact Or.inr (Or.inr (Or.inr hv))

theorem norm_toLp_eq_one {θ : SiteConfig n → ℂ} (hθ : star θ ⬝ᵥ θ = 1) :
    ‖(WithLp.toLp 2 θ : EuclideanSpace ℂ (SiteConfig n))‖ = 1 := by
  have h := Entropy.ConditionalSkew.norm_toLp_sq_eq_re' θ
  rw [hθ, Complex.one_re] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 θ : EuclideanSpace ℂ (SiteConfig n))]

/-- `-log (K (k + 2)^N)⁻¹ = O(log (k + 1))`. -/
theorem isBigO_neg_log_inv_poly {K N : ℝ} (hK : 0 < K) :
    (fun k : ℕ => -Real.log (K * ((k : ℝ) + 2) ^ N)⁻¹) =O[atTop]
      fun k : ℕ => Real.log (k + 1) := by
  refine IsBigO.of_bound (|Real.log K| + 2 * |N|) ?_
  filter_upwards [eventually_ge_atTop 2] with k hk
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  have hl1 : 1 ≤ Real.log ((k : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl2 : Real.log ((k : ℝ) + 2) ≤ 2 * Real.log ((k : ℝ) + 1) := by
    rw [← Real.log_rpow (by linarith)]
    exact Real.log_le_log h2 (by norm_num; nlinarith)
  have hl2' : 0 ≤ Real.log ((k : ℝ) + 2) := Real.log_nonneg (by linarith)
  rw [Real.log_inv, neg_neg, Real.log_mul hK.ne' (Real.rpow_pos_of_pos h2 N).ne',
    Real.log_rpow h2, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤
      Real.log ((k : ℝ) + 1))]
  calc |Real.log K + N * Real.log (↑k + 2)|
        ≤ |Real.log K| + |N * Real.log (↑k + 2)| := abs_add_le _ _
    _ = |Real.log K| + |N| * Real.log (↑k + 2) := by rw [abs_mul, abs_of_nonneg hl2']
    _ ≤ |Real.log K| * Real.log (↑k + 1) + |N| * (2 * Real.log (↑k + 1)) :=
        add_le_add (le_mul_of_one_le_right (abs_nonneg _) hl1)
          (mul_le_mul_of_nonneg_left hl2 (abs_nonneg _))
    _ = (|Real.log K| + 2 * |N|) * Real.log (↑k + 1) := by ring

/-- From a quadratic-form pin to the Loewner bound of `RelativePinBound`. -/
theorem smul_coherentProj_le_of_pin {k : ℕ} {M : Matrix (Config k fun v => Fin (n v))
    (Config k fun v => Fin (n v)) ℂ} (hM : M.IsHermitian) {K N e : ℝ} (hK : 0 < K)
    {θ : SiteConfig n → ℂ}
    (H : ∀ w, ‖star (tensorVec k θ) ⬝ᵥ w‖ ^ 2 * Real.exp e ≤
      K * ((k : ℝ) + 2) ^ N * (star w ⬝ᵥ (M *ᵥ w)).re) :
    ((K * ((k : ℝ) + 2) ^ N)⁻¹ * Real.exp e) • coherentProj k θ ≤ M := by
  have hpos : 0 < K * ((k : ℝ) + 2) ^ N := mul_pos hK (Real.rpow_pos_of_pos (by positivity) N)
  refine smul_vecMulVec_le_of_forall hM fun w => ?_
  have := H w
  rw [mul_assoc, inv_mul_le_iff₀ hpos]
  linarith

theorem rpow_neg_half_eq_inv_sqrt {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ}
    (hA : A.PosDef) : A ^ (-(1 / 2) : ℝ) = (CFC.sqrt A)⁻¹ := by
  rw [CFC.sqrt_eq_rpow, eq_comm]
  exact Matrix.inv_eq_right_inv (hA.rpow_mul_rpow_neg (1 / 2))

/-- **Lemma 6.3 in the form used by the transport estimate** (`05-replicas.tex`, display
`replicas:relative-pin`, lines 486–505, read with the entropy `transport:move-eta` of
`06-transport.tex`, lines 315–328): `RelativePinBound` holds. For a move to `P` the exponent
`η_θ = S_θ(x|P) + S_θ(x|Y \ x)` of `TensorPower.relativePin_regionalMovementEta` is
`I_θ(x:F|P)`; for a move to `F` the outer parts are exchanged; a choice making no move has
relative metric `I`. -/
theorem relativePinBound : RelativePinBound.{u} := by
  obtain ⟨C, c, hC, hc, H⟩ := relativePin_regionalMovementEta.{u}
  refine ⟨c, C, 2, hc, ?_⟩
  intro V _ _ n _ π hπ m hm t ht0 ht14 hsmall
  have ht0' : (0 : ℝ) ≤ t := ht0.le
  have hA := posDef_bandMetric (n := n) hπ ht0'
  cases m with
  | stay =>
    refine ⟨fun _ => 1, fun _ => one_pos, ?_, fun k θ hθ => ?_⟩
    · simp only [Real.log_one, neg_zero]
      exact isBigO_zero _ _
    have hI : bandMetric n t k π ^ (-(1 / 2) : ℝ) * bandMetric n t k ((Move.stay).apply π) *
        bandMetric n t k π ^ (-(1 / 2) : ℝ) = 1 := by
      change bandMetric n t k π ^ (-(1 / 2) : ℝ) * bandMetric n t k π *
        bandMetric n t k π ^ (-(1 / 2) : ℝ) = 1
      nth_rewrite 2 [← (hA k).rpow_one]
      rw [(hA k).rpow_mul_rpow, (hA k).rpow_mul_rpow]
      norm_num [(hA k).rpow_zero]
    rw [hI]
    refine smul_vecMulVec_le_of_forall isHermitian_one fun w => ?_
    have hz : ‖(EuclideanSpace.equiv _ ℂ).symm (tensorVec k θ)‖ = 1 := by
      rw [norm_tensorVec, show (EuclideanSpace.equiv _ ℂ).symm θ = WithLp.toLp 2 θ from rfl,
        norm_toLp_eq_one hθ, one_pow]
    have hcs := norm_star_dotProduct_sq_le_inv PosDef.one (tensorVec k θ) w
    rw [inv_one, one_mulVec, one_mulVec] at hcs
    have hzz : (star (tensorVec k θ) ⬝ᵥ tensorVec k θ).re = 1 := by
      rw [← Entropy.ConditionalSkew.norm_toLp_sq_eq_re']
      have h2 := congrArg (· ^ 2) hz
      simp only [one_pow] at h2
      exact h2
    rw [hzz, one_mul] at hcs
    have hlog : 0 ≤ logDim n (Move.stay : Move V).subsystem := by
      simp [Move.subsystem, logDim]
    have hexp : Real.exp ((k : ℝ) * (2 * t) * (moveEta n π .stay
        ((EuclideanSpace.equiv _ ℂ).symm θ) - C * (2 * t) ^ (1 / 4 : ℝ) *
          logDim n (Move.stay : Move V).subsystem ^ (2 : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff, moveEta, zero_sub]
      have : 0 ≤ C * (2 * t) ^ (1 / 4 : ℝ) * logDim n (Move.stay : Move V).subsystem ^ (2 : ℝ) :=
        by positivity
      have hk : 0 ≤ (k : ℝ) * (2 * t) := by positivity
      have := mul_nonneg hk this
      linarith
    rw [one_mulVec, one_mul]
    nlinarith [mul_le_mul_of_nonneg_right hexp (sq_nonneg ‖star (tensorVec k θ) ⬝ᵥ w‖)]
  | toP x =>
    have h4 := fourPartition_of_isPartition hπ (x := x) hm
    obtain ⟨K, N, hK, H'⟩ := H h4 ht0 (by linarith) (by rw [← logDim_eq]; exact hsmall)
    refine ⟨fun k => (K * ((k : ℝ) + 2) ^ N)⁻¹,
      fun k => inv_pos.mpr (mul_pos hK (Real.rpow_pos_of_pos (by positivity) N)),
      isBigO_neg_log_inv_poly hK, fun k θ hθ => ?_⟩
    have hM : bandMetric n t k π ^ (-(1 / 2) : ℝ) * bandMetric n t k ((Move.toP x).apply π) *
        bandMetric n t k π ^ (-(1 / 2) : ℝ) = relativeMetric n t k π.P x (π.Y \ x) π.F := by
      have hm' : x ⊆ π.Y := hm
      rw [rpow_neg_half_eq_inv_sqrt (hA k), relativeMetric, Finset.union_sdiff_of_subset hm']
      rfl
    rw [hM]
    refine smul_coherentProj_le_of_pin
      (posDef_relativeMetric_and_inv ht0' k h4.moveParts).1.isHermitian hK fun w => ?_
    have := H' k (WithLp.toLp 2 θ) (norm_toLp_eq_one hθ) w
    rw [regionalMovementEta_eq_cmi_left h4, ← logDim_eq] at this
    simpa [moveEta, Move.subsystem, Real.rpow_two] using this
  | toF x =>
    have h4 := fourPartition_of_isPartition hπ (x := x) hm
    obtain ⟨K, N, hK, H'⟩ := H h4.swap ht0 (by linarith) (by rw [← logDim_eq]; exact hsmall)
    refine ⟨fun k => (K * ((k : ℝ) + 2) ^ N)⁻¹,
      fun k => inv_pos.mpr (mul_pos hK (Real.rpow_pos_of_pos (by positivity) N)),
      isBigO_neg_log_inv_poly hK, fun k θ hθ => ?_⟩
    have hM : bandMetric n t k π ^ (-(1 / 2) : ℝ) * bandMetric n t k ((Move.toF x).apply π) *
        bandMetric n t k π ^ (-(1 / 2) : ℝ) = relativeMetric n t k π.F x (π.Y \ x) π.P := by
      have hm' : x ⊆ π.Y := hm
      rw [rpow_neg_half_eq_inv_sqrt (hA k), relativeMetric, Finset.union_sdiff_of_subset hm',
        leafMetric_comm ht0' k h4.PF,
        leafMetric_comm ht0' k (Finset.disjoint_union_right.mpr ⟨h4.PF, h4.Px⟩)]
      rfl
    rw [hM]
    refine smul_coherentProj_le_of_pin
      (posDef_relativeMetric_and_inv ht0' k h4.swap.moveParts).1.isHermitian hK fun w => ?_
    have := H' k (WithLp.toLp 2 θ) (norm_toLp_eq_one hθ) w
    rw [regionalMovementEta_eq_cmi_left h4.swap, ← logDim_eq] at this
    simpa [moveEta, Move.subsystem, Real.rpow_two] using this

/-- **Proposition 7.4, entropy and energy transport, assuming only the split-leaf skew bound**
(area-law paper, `prop:transport`, `06-transport.tex` lines 377--434): the relative coherent
pin is `TensorPower.ReplicaTransport.relativePinBound`. -/
theorem transport_of_splitSkewBound (hskew : SplitSkewBound.{u}) :
    ∃ c₀ Cent eent Cen een : ℝ, 0 < c₀ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] (n : V → ℕ) [∀ v, NeZero (n v)]
        {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
        [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)
        {ι : Type*} [Fintype ι] (E : EnergyTerms V n ι),
        D.IsAdmissible → (∀ i, 0 ≤ E.term i) → (∀ i, E.term i ≤ 1) →
        (∀ i, IsSupportedOn (E.term i) (E.support i)) → D.SupportCompatible E →
        ∀ {a ℓ : ℝ}, 0 < a → 1 ≤ ℓ → a * ℓ ≤ c₀ → (∀ k, D.CrossBandCommute n (a / 2) k) →
        (∀ h c g, logDim n (D.move h c g).subsystem ≤ ℓ) →
        (∀ i, (D.splitLeaves E i).Nonempty → logDim n (E.support i) ≤ ℓ) →
        ∃ β r : ℕ → ℝ, (β =O[atTop] fun k : ℕ => Real.log (k + 1)) ∧ Tendsto r atTop (𝓝 0) ∧
          ∀ (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ),
            pre ∈ symmetricSubspace k (fun v => Fin (n v)) → pre ≠ 0 → ∀ p ∈ Ioo (0 : ℝ) 1,
              HasDerivAt
                (fun q => -Real.log (Transport.filteredNormSq (D.rootPath n (a / 2) k q) pre))
                (D.exactDerivative n (a / 2) k pre p) p ∧
              (k : ℝ) * a * D.entropyGain n (a / 2) k pre p -
                  Cent * k * a * K * a ^ (1 / 4 : ℝ) * ℓ ^ eent - β k ≤
                D.exactDerivative n (a / 2) k pre p ∧
              ∀ E₀ : ℝ, E.replicaEnergy k *ᵥ pre = (E₀ : ℂ) • pre →
                let v := Transport.filteredVector (D.rootPath n (a / 2) k p) pre
                (star v ⬝ᵥ (E.replicaEnergy k *ᵥ v)).re ≤
                  2 * E₀ + Cen * a ^ 2 * ℓ ^ een * D.energyError E (a / 2) k pre p + r k :=
  transport_of_relativePin_of_splitSkewBound relativePinBound hskew

end TensorPower.ReplicaTransport
