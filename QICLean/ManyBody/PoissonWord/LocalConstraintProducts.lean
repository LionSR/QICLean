/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.Constraint.LatticeConstraints
import QICLean.ManyBody.Sites.Lattice.IntegerRectangle
import QICLean.Spectral.Gap.ContractionWordDecay
import QICLean.Probability.PoissonWord.Partition
import QICLean.Probability.PoissonWord.RealOccupation
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.Probability.PoissonWord.ContractionWord
import QICLean.ManyBody.PoissonWord.LatticeOmission

/-!
# Local constraint products

This module states Lemma 10.1 of the area-law manuscript in the generality of the
source. Let `k_i` be positive contractions on a finite domain `Λ ⊆ ℤ²`, anchored at
`a_i` with at most `μ` labels per site, with `‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}`
for every `l ≥ 0`. On one realization of independent rate-one Poisson clocks, let `D` be
the chronological product of the roots `G_i = (I - k_i)^{1/2}` over all events, later
factors on the left, `D_ret` the product over the events with `d_Λ(a_i, S) ≤ r`, and `L`
the product of the radius-`r` roots `(I - E_{N_r(a_i)} k_i)^{1/2}` over the same events.
Then `E‖D_ret - L‖ ≤ C' t |S| (1 + r)² e^{-c' r^α}`, every `L` is a contraction supported
on `N_{2r}(S)`, and, if every `k_i` annihilates a unit vector `Ω` and `B` acts on `S` and
a finite spectator, `E‖(D - D_ret) B (Ω ⊗ ξ)‖ ≤ C' t |S| ‖B‖ e^{v t - c' r^α}` for every
unit spectator vector `ξ`. All three products are read off the same full Poisson word,
and the constants depend only on `C`, `c`, `α` and `μ`.

The truncation estimate is proved below for any finite domain and on the lattice, and the
omission estimate is `QICLean.ManyBody.PoissonWord.LatticeOmission`; they are put on one clock
realization through the list description of the retained product in
`QICLean.Probability.PoissonWord.ContractionWord`.

## Main statements

* `ManyBody.exists_domainLocalConstraintProducts`: Lemma 10.1.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 10.1 (`lem:amplification-local-products`), `09-amplification.tex`, lines 42–72
  (statement) and 74–235 (proof), at revision
  `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean text is reused.
-/

section
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true
open QuantumCircuit SpectralFilter Matrix MeasureTheory
open scoped BigOperators NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open ManyBody (IsGapped groundSpace AdmissibleSupport graphBall graphNeighborhood
  planeDomainGraph PlaneInteraction)
namespace ManyBody

section Lattice

variable {Λ : Finset (ℤ × ℤ)}

/-- With at most `μ` labels anchored at each site, at most `2 μ |S| (1 + r)²` labels have
anchors in `N_r(S)`. Source: area law, `09-amplification.tex`, line 228, with the ball
count of `01-preliminaries.tex`, lines 82–103. -/
theorem card_filter_anchor_mem_graphNeighborhood_le {κ : Type*} [Fintype κ]
    (a : κ → ↥Λ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hfiber : ∀ x, ((Finset.univ.filter fun i => a i = x).card : ℝ) ≤ μ)
    (S : Finset ↥Λ) (r : ℕ) :
    ((Finset.univ.filter fun i => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r).card : ℝ) ≤
      2 * μ * S.card * (1 + (r : ℝ)) ^ 2 := by
  classical
  have hsub : (Finset.univ.filter fun i => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r) ⊆
      S.biUnion fun s => (graphBall (planeDomainGraph Λ) s r).biUnion
        fun x => Finset.univ.filter fun i => a i = x := by
    intro i hi
    obtain ⟨s, hs, hd⟩ := ManyBody.mem_graphNeighborhood.mp (Finset.mem_filter.mp hi).2
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨s, hs, a i, ManyBody.mem_graphBall.mpr hd, rfl⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hball (s : ↥Λ) : (((graphBall (planeDomainGraph Λ) s r).biUnion
      fun x => Finset.univ.filter fun i => a i = x).card : ℝ) ≤
        μ * (2 * ((r : ℝ) + 1) ^ 2) := by
    calc _ ≤ ((∑ x ∈ graphBall (planeDomainGraph Λ) s r,
          (Finset.univ.filter fun i => a i = x).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ graphBall (planeDomainGraph Λ) s r, μ := by
          push_cast; exact Finset.sum_le_sum fun x _ => hfiber x
      _ = μ * (graphBall (planeDomainGraph Λ) s r).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ μ * (2 * ((r : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (card_graphBall_planeDomainGraph_le s r) hμ
  calc ((Finset.univ.filter fun i => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r).card : ℝ)
      ≤ ((∑ s ∈ S, ((graphBall (planeDomainGraph Λ) s r).biUnion
          fun x => Finset.univ.filter fun i => a i = x).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ _s ∈ S, μ * (2 * ((r : ℝ) + 1) ^ 2) := by
        push_cast; exact Finset.sum_le_sum fun s _ => hball s
    _ = 2 * μ * S.card * (1 + (r : ℝ)) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- At most `2 μ_R |S| (1 + r)²` labels have anchors in `N_r(S)`, where `μ_R` is the
anchor multiplicity. Source: area law, `09-amplification.tex`, line 228, with the
counts of `01-preliminaries.tex`, lines 82–103. -/
theorem card_anchor_graphNeighborhood_le {R : ℕ} (a : AdmissibleSupport Λ R → ↥Λ)
    (ha : ∀ X, a X ∈ X.1) (S : Finset ↥Λ) (r : ℕ) :
    ((Finset.univ.filter fun i => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r).card : ℝ) ≤
      2 * (2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) * S.card * (1 + (r : ℝ)) ^ 2 :=
  card_filter_anchor_mem_graphNeighborhood_le a (Nat.cast_nonneg _)
    (fun x => by exact_mod_cast card_anchor_fiber_le a ha x) S r

/-- Every product of the radius-`r` local roots `(I - E_{N_r(a_i)} k_i)^{1/2}` over labels
anchored in `N_r(S)` is supported on `N_{2r}(S)`.
Source: area law, `09-amplification.tex`, lines 232–234. -/
theorem contractionWord_regionExpectation_mem_supportedOperators {q : ℕ}
    {κ : Type*} (a : κ → ↥Λ) {S : Finset ↥Λ} {r : ℕ}
    (k : {i // a i ∈ graphNeighborhood (planeDomainGraph Λ) S r} →
      Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ) :
    ∀ (m : ℕ) (u : Fin m → {i // a i ∈ graphNeighborhood (planeDomainGraph Λ) S r}),
      contractionWord (fun i : {i // a i ∈ graphNeighborhood (planeDomainGraph Λ) S r} =>
          ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i))
        m u ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
            (graphNeighborhood (planeDomainGraph Λ) S (2 * r) : Finset ↥Λ) := by
  have hmem (i : {i // a i ∈ graphNeighborhood (planeDomainGraph Λ) S r}) :
      CFC.sqrt (1 - ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i)) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin q)
            (graphNeighborhood (planeDomainGraph Λ) S (2 * r) : Finset ↥Λ) := by
    set K := graphBall (planeDomainGraph Λ) (a i) r
    have hK : CFC.sqrt (1 - ManyBody.regionExpectation K (k i)) ∈
        ManyBody.supportedOperators (fun _ ↦ Fin q) K :=
      (ManyBody.sqrt_mem_supportedOperators
          ((Subalgebra.toSubmodule
              (ManyBody.supportedOperators (fun _ ↦ Fin q) K).toSubalgebra).sub_mem
              (one_mem (ManyBody.supportedOperators _ _))
          (ManyBody.regionExpectation_mem_supportedOperators K (k i))))
    exact ManyBody.supportedOperators_mono
      (by rw [two_mul]; exact_mod_cast ManyBody.graphBall_subset_graphNeighborhood_add i.2 r) hK
  intro m
  induction m with
  | zero => intro u; rw [contractionWord_zero]; exact (one_mem (ManyBody.supportedOperators _ _))
  | succ m ih =>
    intro u
    rw [contractionWord]
    exact mul_mem (hmem _) (ih _)

/-- The prefactor `2 μ √C` of the truncation of the retained constraint product, for
localization tails `C e^{-c l^α}` and at most `μ` labels per site. Source: area law,
`09-amplification.tex`, lines 228–234. -/
noncomputable def constraintWordTruncationPrefactor (μ C : ℝ) : ℝ :=
  2 * μ * Real.sqrt C

theorem constraintWordTruncationPrefactor_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (C : ℝ) :
    0 ≤ constraintWordTruncationPrefactor μ C := by
  unfold constraintWordTruncationPrefactor; positivity

/-- **Truncation of the retained constraint product for general constraints, with explicit
constants** (Lemma 10.1, `eq:amplification-product-truncation`, `09-amplification.tex`,
lines 42–63 and 228–234). The bound of `exists_domainConstraintWord_truncation` holds with
`A = constraintWordTruncationPrefactor μ C = 2 μ √C` and `γ = c / 2`. -/
theorem domainConstraintWord_truncation {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ) :
    ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
      (a : κ → ↥Λ) (k : κ → Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ),
      (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
      (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
      (∀ i (l : ℕ), ‖k i - ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) l) (k
          i)‖ ≤
        C * Real.exp (-(c * (l : ℝ) ^ α))) →
      ∀ (S : Finset ↥Λ) (r : ℕ) (t : ℝ≥0),
      let P := fun i : κ => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r
      let kr := fun i : {i // P i} =>
        ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i)
      let D := fun w : PoissonWord.Word κ =>
        contractionWord (fun i : {i // P i} => k i) (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      let L := fun w : PoissonWord.Word κ =>
        contractionWord kr (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure κ t) ∧
      (∫ w, ‖D w - L w‖ ∂PoissonWord.measure κ t) ≤
        constraintWordTruncationPrefactor μ C * t * S.card * (1 + (r : ℝ)) ^ 2 *
          Real.exp (-(c / 2 * (r : ℝ) ^ α)) ∧
      ∀ w, ‖L w‖ ≤ 1 ∧
        L w ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
            (graphNeighborhood (planeDomainGraph Λ) S (2 * r) : Finset ↥Λ) := by
  unfold constraintWordTruncationPrefactor
  intro q _ Λ κ _ a k hk₀ hk₁ hfiber htail S r t P kr D L
  have hkr₀ (i : {i // P i}) : 0 ≤ kr i := Matrix.nonneg_iff_posSemidef.mpr
      (ManyBody.posSemidef_regionExpectation (Matrix.nonneg_iff_posSemidef.mp (hk₀ i)))
  have hkr₁ (i : {i // P i}) : kr i ≤ 1 := (ManyBody.regionExpectation_mono (hk₁ i)).trans_eq
      ManyBody.regionExpectation_one
  set ε := Real.sqrt C * Real.exp (-(c / 2 * (r : ℝ) ^ α)) with hε_def
  have hε (i : {i // P i}) : ‖CFC.sqrt (1 - k i) - CFC.sqrt (1 - kr i)‖ ≤ ε := by
    refine (norm_sqrt_one_sub_sub_le (hk₁ i) (hkr₁ i)).trans ?_
    calc Real.sqrt ‖k i - kr i‖ ≤ Real.sqrt (C * Real.exp (-(c * (r : ℝ) ^ α))) :=
          Real.sqrt_le_sqrt (htail i r)
      _ = ε := by
          rw [Real.sqrt_mul hC, ← Real.exp_half, hε_def]
          ring_nf
  obtain ⟨hint, hle⟩ := integrable_and_integral_norm_contractionWord_retained_sub_le P
    (fun i : {i // P i} => k i) kr (fun i => hk₀ i) hkr₀ hε t
  refine ⟨hint, hle.trans ?_, fun w => ⟨norm_contractionWord_le_one kr hkr₀ _ _,
    contractionWord_regionExpectation_mem_supportedOperators a _ _ _⟩⟩
  have hcardP : (Fintype.card {i // P i} : ℝ) ≤ 2 * μ * S.card * (1 + (r : ℝ)) ^ 2 := by
    rw [Fintype.card_subtype]; exact card_filter_anchor_mem_graphNeighborhood_le a hμ hfiber S r
  have hε0 : 0 ≤ ε := by positivity
  calc ε * Fintype.card {i // P i} * t ≤ ε * (2 * μ * S.card * (1 + (r : ℝ)) ^ 2) * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcardP hε0) t.2
    _ = _ := by rw [hε_def]; ring

/-- **Truncation of the retained constraint product for general constraints**
(Lemma 10.1, `lem:amplification-local-products`, `eq:amplification-product-truncation`,
`09-amplification.tex`, lines 42–63, proof at lines 228–234).
For tail constants `C ≥ 0`, `c > 0` and a multiplicity bound `μ ≥ 0` there are `A ≥ 0`
and `γ > 0` with the following property. Let `k_i` be positive contractions on a finite
domain `Λ`, anchored at `a_i` with at most `μ` labels per site, with
`‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}` for all `l`. Retain the labels with
`d_Λ(a_i, S) ≤ r`. On each realization `w` of the full Poisson word, let `D_ret(w)` be
the chronological product of the roots `(I - k_i)^{1/2}` over the retained events and
`L(w)` the same product of `(I - E_{N_r(a_i)} k_i)^{1/2}`. Then `‖D_ret - L‖` is
integrable, `E‖D_ret - L‖ ≤ A t |S| (1 + r)² e^{-γ r^α}`, and every `L(w)` is a
contraction supported on `N_{2r}(S)`. The constants precede the local dimension,
domain, labels, anchors, constraints, `S`, `r` and `t`. The source assumes `S`
nonempty and `r ≥ 1`; neither is needed here. -/
theorem exists_domainConstraintWord_truncation {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ)
    (hc : 0 < c) :
    ∃ A γ : ℝ, 0 ≤ A ∧ 0 < γ ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
        (a : κ → ↥Λ) (k : κ → Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        (∀ i (l : ℕ), ‖k i - ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) l) (k
            i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (S : Finset ↥Λ) (r : ℕ) (t : ℝ≥0),
        let P := fun i : κ => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r
        let kr := fun i : {i // P i} =>
          ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i)
        let D := fun w : PoissonWord.Word κ =>
          contractionWord (fun i : {i // P i} => k i) (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2
        let L := fun w : PoissonWord.Word κ =>
          contractionWord kr (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2
        Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure κ t) ∧
        (∫ w, ‖D w - L w‖ ∂PoissonWord.measure κ t) ≤
          A * t * S.card * (1 + (r : ℝ)) ^ 2 * Real.exp (-(γ * (r : ℝ) ^ α)) ∧
        ∀ w, ‖L w‖ ≤ 1 ∧
          L w ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
              (graphNeighborhood (planeDomainGraph Λ) S (2 * r) : Finset ↥Λ) :=
  ⟨_, _, constraintWordTruncationPrefactor_nonneg hμ C, half_pos hc,
    domainConstraintWord_truncation hC hμ⟩

open Classical in
/-- **Truncation of the retained constraint product for the exact positive constraints, with
explicit constants** (Lemma 10.1, `eq:amplification-product-truncation`;
`09-amplification.tex`, lines 42–63 and 228–234). Let `C ≥ 0` be a localization prefactor of
the positive constraints, in the form of Proposition 4.3, with rate `c`. Then the bound of
`exists_latticeConstraintWord_truncation` holds with
`C_t = constraintWordTruncationPrefactor μ_R C = 2 μ_R √C`, `μ_R = 2^{2R(R+1)}`, and
`c_t = c / 2`. -/
theorem latticeConstraintWord_truncation_of_positiveConstraints {p : ℕ} (R : ℕ) {J Δ C c : ℝ}
    (hC : 0 ≤ C)
    (hpos : ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R)
        (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
        (a : AdmissibleSupport Λ R → ↥Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        let cs := positiveNormalization p (Δ / 2) J
        let k := fun i => positiveConstraint cs
            (centeredFilter p (Δ / 2) h.hamiltonian Ω (h.term i))
        0 < cs ∧
        (∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ WithLp.ofLp Ω = 0) ∧
        cs⁻¹ • (h.hamiltonian - (E₀ : ℂ) • 1) ≤ ∑ i, k i ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          cs⁻¹ • (h.hamiltonian - (E₀ : ℂ) • 1) ∧
        ((Δ / cs : ℝ) : ℂ) • (1 - Matrix.vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
          ∑ i, k i ∧
        (∀ i (l : ℕ), 0 ≤ ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) l) (k i)
            ∧
          ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) l) (k i) ≤ 1 ∧
          ‖k i - ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) l) (k i)‖ ≤
            C * Real.exp (-(c * (l : ℝ) ^ kernelExponent p))) ∧
        (∀ i, k i ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) (Finset.univ.filter fun x ↦
            (planeDomainGraph Λ).Reachable (a i) x))) :
    ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R)
        (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
      (a : AdmissibleSupport Λ R → ↥Λ), (∀ X, a X ∈ X.1) →
      ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ (S : Finset ↥Λ) (r : ℕ) (t : ℝ≥0),
      let P := fun i : AdmissibleSupport Λ R => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r
      let k := fun i : {i // P i} => positiveConstraint (positiveNormalization p (Δ / 2) J)
        (centeredFilter p (Δ / 2) h.hamiltonian Ω (h.term i))
      let kr := fun i : {i // P i} =>
        ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i)
      let D := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
        contractionWord k (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      let L := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
        contractionWord kr (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
      (∫ w, ‖D w - L w‖ ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
        constraintWordTruncationPrefactor ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) C * t *
          S.card * (1 + (r : ℝ)) ^ 2 * Real.exp (-(c / 2 * (r : ℝ) ^ kernelExponent p)) ∧
      ∀ w, ‖L w‖ ≤ 1 ∧
        L w ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
            (graphNeighborhood (planeDomainGraph Λ) S (2 * r) : Finset ↥Λ) := by
  intro q _ Λ h hh hhJ a ha E₀ Ω hΩ hgap hspan S r t
  obtain ⟨-, hk, -, -, -, htail, -⟩ := hpos Λ h hh hhJ a ha E₀ Ω hΩ hgap hspan
  exact domainConstraintWord_truncation hC (Nat.cast_nonneg _) Λ (AdmissibleSupport Λ R) a _
    (fun i => (hk i).1) (fun i => (hk i).2.1)
    (fun x => by exact_mod_cast card_anchor_fiber_le a ha x) (fun i l => (htail i l).2.2) S r t

/-- **Truncation of the retained constraint product for the exact positive constraints, at the
named constants** (Lemma 10.1, `eq:amplification-product-truncation`; `09-amplification.tex`,
lines 42–63 and 228–234, with Proposition 4.3, `03-quasilocal.tex`, lines 220–334). The bound
of `exists_latticeConstraintWord_truncation` holds with
`C_t = constraintWordTruncationPrefactor μ_R C₃` and `c_t = c₃ / 2`, where
`C₃ = latticePositiveConstraintConst R J Δ p` and `c₃ = latticePositiveConstraintRate R J Δ p`. -/
theorem latticeConstraintWord_truncation_explicit {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R)
        (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
      (a : AdmissibleSupport Λ R → ↥Λ), (∀ X, a X ∈ X.1) →
      ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ (S : Finset ↥Λ) (r : ℕ) (t : ℝ≥0),
      let P := fun i : AdmissibleSupport Λ R => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r
      let k := fun i : {i // P i} => positiveConstraint (positiveNormalization p (Δ / 2) J)
        (centeredFilter p (Δ / 2) h.hamiltonian Ω (h.term i))
      let kr := fun i : {i // P i} =>
        ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i)
      let D := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
        contractionWord k (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      let L := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
        contractionWord kr (PoissonWord.partitionWords P w).1.1
          (PoissonWord.partitionWords P w).1.2
      Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
      (∫ w, ‖D w - L w‖ ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
        constraintWordTruncationPrefactor ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)
            (latticePositiveConstraintConst R J Δ p) * t * S.card * (1 + (r : ℝ)) ^ 2 *
          Real.exp (-(latticePositiveConstraintRate R J Δ p / 2 * (r : ℝ) ^ kernelExponent p)) ∧
      ∀ w, ‖L w‖ ≤ 1 ∧
        L w ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
            (graphNeighborhood (planeDomainGraph Λ) S (2 * r) : Finset ↥Λ) :=
  latticeConstraintWord_truncation_of_positiveConstraints R
    (latticePositiveConstraintConst_nonneg R J Δ p) (latticePositiveConstraints_explicit hp R hJ hΔ)

/-- **Truncation of the retained constraint product** (Lemma 10.1,
`lem:amplification-local-products`, `eq:amplification-product-truncation`,
`09-amplification.tex`, lines 42–63, proof at lines 228–234).
For `p ≥ 1`, `R`, `J ≥ 0` and `Δ > 0` there are `C ≥ 0` and `c > 0` such that the
following holds for the exact positive constraints `k_i` of every gapped lattice
Hamiltonian, every anchoring `a_i ∈ X_i`, every set `S`, radius `r` and time `t`.
Retain the labels with `d_Λ(a_i, S) ≤ r`. On each realization `w` of the full
Poisson word, let `D_ret(w)` be the chronological product of the roots
`(I - k_i)^{1/2}` over the retained events and `L(w)` the same product of
`(I - E_{N_r(a_i)} k_i)^{1/2}`. Then `‖D_ret - L‖` is integrable,
`E‖D_ret - L‖ ≤ C t |S| (1 + r)² e^{-c r^α}` with `α = p / (p + 1)`, and every
`L(w)` is a contraction supported on `N_{2r}(S)`. The constants precede the local
dimension, domain, Hamiltonian, anchors, ground state, `S`, `r` and `t`.
The source assumes `S` nonempty and `r ≥ 1`; neither is needed here. -/
theorem exists_latticeConstraintWord_truncation {p : ℕ} (hp : 1 ≤ p) (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R)
          (_ : ∀ X, (h.term X).IsHermitian) (_ : ∀ X, ‖h.term X‖ ≤ J)
        (a : AdmissibleSupport Λ R → ↥Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
        groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
        ∀ (S : Finset ↥Λ) (r : ℕ) (t : ℝ≥0),
        let P := fun i : AdmissibleSupport Λ R => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r
        let k := fun i : {i // P i} => positiveConstraint (positiveNormalization p (Δ / 2) J)
          (centeredFilter p (Δ / 2) h.hamiltonian Ω (h.term i))
        let kr := fun i : {i // P i} =>
          ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i)
        let D := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
          contractionWord k (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2
        let L := fun w : PoissonWord.Word (AdmissibleSupport Λ R) =>
          contractionWord kr (PoissonWord.partitionWords P w).1.1
            (PoissonWord.partitionWords P w).1.2
        Integrable (fun w => ‖D w - L w‖) (PoissonWord.measure (AdmissibleSupport Λ R) t) ∧
        (∫ w, ‖D w - L w‖ ∂PoissonWord.measure (AdmissibleSupport Λ R) t) ≤
          C * t * S.card * (1 + (r : ℝ)) ^ 2 *
            Real.exp (-(c * (r : ℝ) ^ kernelExponent p)) ∧
        ∀ w, ‖L w‖ ≤ 1 ∧
          L w ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
              (graphNeighborhood (planeDomainGraph Λ) S (2 * r) : Finset ↥Λ) := by
  obtain ⟨C, c, hC, hc, hpos⟩ := exists_latticePositiveConstraints hp R hJ hΔ
  exact ⟨_, _, constraintWordTruncationPrefactor_nonneg (Nat.cast_nonneg _) C, half_pos hc,
    latticeConstraintWord_truncation_of_positiveConstraints R hC hpos⟩

end Lattice

end ManyBody
end

open Matrix MeasureTheory QuantumCircuit
open scoped Kronecker NNReal Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open ManyBody (graphBall graphNeighborhood planeDomainGraph)

namespace ManyBody

/-- **Local constraint products** (Lemma 10.1, `lem:amplification-local-products`,
`09-amplification.tex`, lines 42–72, proof at lines 74–235).
For tail constants `C ≥ 0`, `c > 0`, `0 < α ≤ 1` and a multiplicity bound `μ ≥ 0` there
are `A ≥ 0` and `γ, v > 0` with the following property. Let `k_i` be positive
contractions on a finite domain `Λ`, anchored at `a_i` with at most `μ` labels per site,
with `‖k_i - E_{N_l(a_i)} k_i‖ ≤ C e^{-c l^α}` for all `l`. Fix `S ⊆ Λ`, an integer `r`
and `t ≥ 0`, and retain the labels with `d_Λ(a_i, S) ≤ r`. On each realization `w` of
the full Poisson word, let `D(w)` be the product of the roots `(I - k_i)^{1/2}` over all
events in occurrence order, later factors on the left, `D_ret(w)` the product over the
retained events, and `L(w)` the product of the roots `(I - E_{N_r(a_i)} k_i)^{1/2}` over
the retained events. Then

* `E‖D_ret - L‖ ≤ A t |S| (1 + r)² e^{-γ r^α}`, and every `L(w)` is a contraction
  supported on `N_{2r}(S)`;
* if `k_i Ω = 0` for a unit vector `Ω` and `B` acts on `S` and a finite spectator, then
  `E‖(D - D_ret) B (Ω ⊗ ξ)‖ ≤ A t |S| ‖B‖ e^{v t - γ r^α}` for every unit spectator
  vector `ξ`.

Both norms are integrable for the Poisson-word law. The constants precede the local
dimension, domain, labels, anchors, constraints, spectator, `S`, `r` and `t`. The source
assumes `S` nonempty and `r ≥ 1`; neither is needed here. -/
theorem exists_domainLocalConstraintProducts {C μ c α : ℝ} (hC : 0 ≤ C) (hμ : 0 ≤ μ)
    (hc : 0 < c) (hα : 0 < α) (hα₁ : α ≤ 1) :
    ∃ A γ v : ℝ, 0 ≤ A ∧ 0 < γ ∧ 0 < v ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (κ : Type*) [Fintype κ]
        (a : κ → ↥Λ) (k : κ → Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ),
        (∀ i, 0 ≤ k i) → (∀ i, k i ≤ 1) →
        (∀ x, ((Finset.univ.filter fun i : κ => a i = x).card : ℝ) ≤ μ) →
        (∀ i (l : ℕ), ‖k i - ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) l) (k
            i)‖ ≤
          C * Real.exp (-(c * (l : ℝ) ^ α))) →
        ∀ (S : Finset ↥Λ) (r : ℕ) (t : ℝ≥0),
        let P := fun i : κ => a i ∈ graphNeighborhood (planeDomainGraph Λ) S r
        let G := fun i : κ => CFC.sqrt (1 - k i)
        let Gr := fun i : κ =>
          CFC.sqrt (1 - ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i))
        let ret := fun w : PoissonWord.Word κ => (List.ofFn w.2).filter fun i => decide (P i)
        let D := fun w : PoissonWord.Word κ => ((List.ofFn w.2).reverse.map G).prod
        let Dret := fun w : PoissonWord.Word κ => ((ret w).reverse.map G).prod
        let L := fun w : PoissonWord.Word κ => ((ret w).reverse.map Gr).prod
        (Integrable (fun w => ‖Dret w - L w‖) (PoissonWord.measure κ t) ∧
          (∫ w, ‖Dret w - L w‖ ∂PoissonWord.measure κ t) ≤
            A * t * S.card * (1 + (r : ℝ)) ^ 2 * Real.exp (-(γ * (r : ℝ) ^ α))) ∧
        (∀ w, ‖L w‖ ≤ 1 ∧
          L w ∈ ManyBody.supportedOperators (fun _ ↦ Fin q)
              (graphNeighborhood (planeDomainGraph Λ) S (2 * r) : Finset ↥Λ)) ∧
        ∀ (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 → (∀ i, k i *ᵥ WithLp.ofLp Ω = 0) →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux]
          (B : Matrix ((↥Λ → Fin q) × Aux) ((↥Λ → Fin q) × Aux) ℂ),
          (∀ x y : Aux, (Matrix.of fun σ τ => B (σ, x) (τ, y)) ∈
            ManyBody.supportedOperators (fun _ ↦ Fin q) S) →
          ∀ (ξ : Aux → ℂ), ‖WithLp.toLp 2 ξ‖ = 1 →
            let F := fun w : PoissonWord.Word κ =>
              ‖WithLp.toLp 2 (((D w - Dret w) ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ
                (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2))‖
            Integrable F (PoissonWord.measure κ t) ∧
            (∫ w, F w ∂PoissonWord.measure κ t) ≤
              A * t * S.card * ‖B‖ * Real.exp (v * t - γ * (r : ℝ) ^ α) := by
  obtain ⟨At, γt, hAt, hγt, htr⟩ := exists_domainConstraintWord_truncation (α := α) hC hμ hc
  obtain ⟨Ao, v, γo, hAo, hv, hγo, hom⟩ := exists_domainConstraintWord_omission hC hμ hc hα hα₁
  refine ⟨max At Ao, min γt γo, v, hAt.trans (le_max_left _ _), lt_min hγt hγo, hv, ?_⟩
  intro q _ Λ κ _ a k hk₀ hk₁ hfiber htail S r t P G Gr ret D Dret L
  classical
  have hDret (w : PoissonWord.Word κ) : contractionWord (fun i : {i // P i} => k i)
      (PoissonWord.partitionWords P w).1.1 (PoissonWord.partitionWords P w).1.2 = Dret w :=
    contractionWord_partitionWords_fst P k w
  have hLw (w : PoissonWord.Word κ) : contractionWord
      (fun i : {i // P i} => ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k
          i))
      (PoissonWord.partitionWords P w).1.1 (PoissonWord.partitionWords P w).1.2 = L w :=
    contractionWord_partitionWords_fst P
      (fun i => ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i) r) (k i)) w
  have e : (fun w : PoissonWord.Word κ => ‖Dret w - L w‖) = fun w =>
      ‖contractionWord (fun i : {i // P i} => k i)
          (PoissonWord.partitionWords P w).1.1 (PoissonWord.partitionWords P w).1.2 -
        contractionWord
          (fun i : {i // P i} => ManyBody.regionExpectation (graphBall (planeDomainGraph Λ) (a i)
              r) (k
              i))
          (PoissonWord.partitionWords P w).1.1 (PoissonWord.partitionWords P w).1.2‖ :=
    funext fun w => by rw [hDret, hLw]
  obtain ⟨hint, hle, hL⟩ := htr Λ κ a k hk₀ hk₁ hfiber htail S r t
  refine ⟨⟨by rw [e]; exact hint, ?_⟩, fun w => by rw [← hLw]; exact hL w, ?_⟩
  · rw [e]
    refine hle.trans ?_
    gcongr
    · exact le_max_left _ _
    · exact min_le_left _ _
  intro Ω hΩ hkΩ Aux _ _ B hB ξ hξ F
  obtain ⟨hFint, hFle⟩ := hom Λ κ a k hk₀ hk₁ hfiber htail Ω hΩ hkΩ Aux S B hB ξ hξ r t
  have hF : (fun w => ‖WithLp.toLp 2
      (((D w ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2)) -
        ((Dret w ⊗ₖ (1 : Matrix Aux Aux ℂ)) *ᵥ (B *ᵥ fun x => WithLp.ofLp Ω x.1 * ξ x.2)))‖) =
      F := by
    funext w
    have hsub : (D w - Dret w) ⊗ₖ (1 : Matrix Aux Aux ℂ) =
        D w ⊗ₖ (1 : Matrix Aux Aux ℂ) - Dret w ⊗ₖ (1 : Matrix Aux Aux ℂ) := by
      rw [eq_sub_iff_add_eq, ← add_kronecker, sub_add_cancel]
    simp only [F, hsub, sub_mulVec]
  rw [← hF]
  refine ⟨hFint, hFle.trans ?_⟩
  gcongr
  · exact le_max_right _ _
  · exact min_le_right _ _

end ManyBody
