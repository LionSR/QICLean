/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.SupportedGaussianIntegral
import QICLean.ManyBody.Dynamics.SwappedDoubledInteraction
import QICLean.ManyBody.Hamiltonian.Chain.Doubled

/-!
# Localization and Gaussian averaging for the relative evolution on a chain

Swapping the two copies on a region changes only the interaction terms that cross the
boundary. The relative-evolution generator is localized by evolving each of these
differences and projecting onto the neighborhood of the crossing supports. The norm
error grows linearly in the number of sites.

The localized generator defines one unitary path. Its Gaussian averages against
localized observables are supported on the neighborhood of the union of the
observable and crossing supports. The chain and finite-domain versions follow from
the corresponding statements on finite graphs.

Source: TNLean one-dimensional note, `part2a_mps_information.tex`, lines 380–402.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped Kronecker Matrix.Norms.L2Operator NNReal

namespace ManyBody

/-- The relative-evolution generator is exponentially close to its
expectation on the neighborhood of the crossing supports, with error linear
in the chain length. A negative radius gives the radius-zero neighborhood.
Source: TNLean note, `part2a_mps_information.tex`, lines 380–400. -/
theorem ChainInteraction.norm_relativeGenerator_sub_regionExpectation_le
    {L q R : ℕ} {J : ℝ} (h : ChainInteraction L q R) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin L)) (hq : 1 ≤ q) (ℓ : ℝ) (t : ℝ) :
    let K := h.doubledFin.hamiltonian
    let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
    let K' := F * K * Fᴴ
    let C := ManyBody.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
    let Z := C.biUnion (fun X ↦ X.1)
    let B := ManyBody.graphNeighborhood (SimpleGraph.pathGraph L) Z ⌊ℓ⌋₊
    let G := ManyBody.heisenbergEvolution K' t (K' - K)
    let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
    let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
      (1 - Real.exp (-(1 / 2)))
    let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
    ‖G - ManyBody.regionExpectation B G‖ ≤
      (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
        (L : ℝ) * Real.exp (v * |t| - ℓ / 2) := by
  classical
  intro K pr e F K' C Z B G b₀ a v
  have : NeZero (q * q) := ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos hq hq)⟩
  let Φ : ManyBody.Interaction (fun _ : Fin L ↦ Fin (q * q)) (fun X : ChainSupport L R ↦ X.1) :=
    (h.doubled.conj (ManyBody.pairSwapOp (X := fun _ ↦ Fin q) D) fun X ↦
        ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators D
          (h.doubled.mem X)).relabel (X' := fun _ ↦ Fin (q * q)) (Equiv.refl _)
      (fun _ ↦ finProdFinEquiv) (fun X : ChainSupport L R ↦ X.1) fun _ _ ↦ Iff.rfl
  have hΦ : Φ.hamiltonian = K' :=
    (ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled (X' := fun _ ↦ Fin (q * q))
      h D _ (Equiv.refl _) (fun _ ↦ finProdFinEquiv) _ fun _ _ ↦ Iff.rfl).trans
      (congrArg (fun M ↦ F * M * Fᴴ) h.hamiltonian_doubledFin.symm)
  have hΦh : ∀ X, (Φ.term X).IsHermitian := fun X ↦
    ManyBody.Interaction.isHermitian_relabel_term _ _ _ _
      (ManyBody.Interaction.isHermitian_conj_term _ _
        (ManyBody.Interaction.isHermitian_doubled_term (hh X)))
  have hΦn : ∀ X, ‖Φ.term X‖ ≤ 2 * J := fun X ↦
    ((ManyBody.Interaction.norm_relabel_term _ _ _ _ _ X).trans
      (ManyBody.Interaction.norm_conj_term _ (ManyBody.pairSwapOp_mem_unitaryGroup D) _
        X)).trans_le ((ManyBody.Interaction.norm_doubled_term_le h X).trans
          (by linarith [hhJ X]))
  let T (X : ChainSupport L R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  let A (p : ChainSupport L R × Bool) := F * T p.1 p.2 * Fᴴ - T p.1 p.2
  obtain ⟨hsum, hcount⟩ := h.partialSwap_difference_eq_sum_crossing D
  have hdiff : K' - K = ∑ p ∈ C ×ˢ Finset.univ, A p := by
    rw [Finset.sum_product]
    exact hsum
  have hgen := norm_heisenberg_sum_sub_regionExpectation_graphNeighborhood_le
    (SimpleGraph.pathGraph L) (SimpleGraph.pathGraph_card_sphere_le_two L) Φ
    (fun X ↦ ManyBody.ChainSupport.edist_le X) (fun X ↦ X.2.card_le) hΦh b₀
    (ManyBody.ChainInteraction.sum_norm_terms_containing_le Φ hΦn) (C ×ˢ Finset.univ)
        (fun p ↦ p.1.1) Z
    (fun p hp ↦ Finset.subset_biUnion_of_mem (fun X ↦ X.1) (Finset.mem_product.mp hp).1)
    (fun p _ ↦ p.1.2.card_le) A (fun p _ ↦ (h.partialSwap_term_difference_spec hh hhJ D p.1 p.2).1)
    (2 * |J|) (fun p _ ↦ (h.partialSwap_term_difference_spec hh hhJ D p.1 p.2).2.2.trans
      (mul_le_mul_of_nonneg_left (le_abs_self J) (by norm_num))) ℓ t
  dsimp only at hgen
  rw [hΦ, ← hdiff] at hgen
  have hb : (boundaryEdges L D).card ≤ L :=
    (Finset.card_le_card fun p hp ↦ Finset.mem_range.mpr
      (by have := (ManyBody.mem_boundaryEdges.mp hp).1; omega)).trans (Finset.card_range _).le
  have hc : ((C ×ˢ (Finset.univ : Finset Bool)).card : ℝ) ≤ (chainCrossConst R : ℝ) * L := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
    exact_mod_cast hcount.trans (Nat.mul_le_mul_left _ hb)
  have ha : 0 ≤ a := (div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))).le
  calc
    _ ≤ _ := hgen
    _ ≤ ((chainCrossConst R : ℝ) * L) *
        (2 * (a * (R + 1 : ℝ) ^ 2 * (2 * |J|) * Real.exp (v * |t| - ℓ / 2))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

/-- Natural-radius localization of the relative-evolution generator on an
actual finite integer domain. This extends the chain localization argument of
TNLean note, part2a_mps_information.tex, lines 380–400, to the finite domains of
part0_preamble.tex, lines 191–215. No spectral gap or reset conclusion is asserted. -/
theorem DomainInteraction.norm_relativeGenerator_sub_regionExpectation_le
    {Λ : Finset ℤ} {q R : ℕ} {J : ℝ} (h : DomainInteraction Λ q R)
        (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (D : Finset (Fin Λ.card)) (hq : 1 ≤ q) (m : ℕ) (t : ℝ) :
    let K := h.doubledFin.hamiltonian
    let pr := Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q
    let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv)
    let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
    let K' := F * K * Fᴴ
    let C := ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
    let Z := C.biUnion (fun X ↦ X.1)
    let B := ManyBody.graphNeighborhood (lineDomainGraph Λ) Z m
    let G := ManyBody.heisenbergEvolution K' t (K' - K)
    let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
    let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
      (1 - Real.exp (-(1 / 2)))
    let v : ℝ := 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1
    ‖G - ManyBody.regionExpectation B G‖ ≤
      (4 * |J| * a * (R + 1 : ℝ) ^ 2 * (chainCrossConst R : ℝ)) *
        (Λ.card : ℝ) * Real.exp (v * |t| - (m : ℝ) / 2) := by
  classical
  intro K pr e F K' C Z B G b₀ a v
  have : NeZero (q * q) := ⟨Nat.pos_iff_ne_zero.mp (Nat.mul_pos hq hq)⟩
  let Φ : ManyBody.Interaction (fun _ : Fin Λ.card ↦ Fin (q * q))
      (fun X : DomainSupport Λ R ↦ X.1) :=
    (h.doubled.conj (ManyBody.pairSwapOp (X := fun _ ↦ Fin q) D) fun X ↦
        ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators D
          (h.doubled.mem X)).relabel (X' := fun _ ↦ Fin (q * q)) (Equiv.refl _)
      (fun _ ↦ finProdFinEquiv) (fun X : DomainSupport Λ R ↦ X.1) fun _ _ ↦ Iff.rfl
  have hΦ : Φ.hamiltonian = K' :=
    (ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled (X' := fun _ ↦ Fin (q * q))
      h D _ (Equiv.refl _) (fun _ ↦ finProdFinEquiv) _ fun _ _ ↦ Iff.rfl).trans
      (congrArg (fun M ↦ F * M * Fᴴ) h.hamiltonian_doubledFin.symm)
  have hΦh : ∀ X, (Φ.term X).IsHermitian := fun X ↦
    ManyBody.Interaction.isHermitian_relabel_term _ _ _ _
      (ManyBody.Interaction.isHermitian_conj_term _ _
        (ManyBody.Interaction.isHermitian_doubled_term (hh X)))
  have hΦn : ∀ X, ‖Φ.term X‖ ≤ 2 * J := fun X ↦
    ((ManyBody.Interaction.norm_relabel_term _ _ _ _ _ X).trans
      (ManyBody.Interaction.norm_conj_term _ (ManyBody.pairSwapOp_mem_unitaryGroup D) _
        X)).trans_le ((ManyBody.Interaction.norm_doubled_term_le h X).trans
          (by linarith [hhJ X]))
  let T (X : DomainSupport Λ R) (b : Bool) := Matrix.reindex e e
    (if b then (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ) ⊗ₖ h.term X
      else h.term X ⊗ₖ (1 : Matrix (Fin Λ.card → Fin q) (Fin Λ.card → Fin q) ℂ))
  let A (p : DomainSupport Λ R × Bool) := F * T p.1 p.2 * Fᴴ - T p.1 p.2
  obtain ⟨hsum, hcount⟩ := h.partialSwap_difference_eq_sum_crossing D
  have hdiff : K' - K = ∑ p ∈ C ×ˢ Finset.univ, A p := by
    rw [Finset.sum_product]
    exact hsum
  have hgen := norm_heisenberg_sum_sub_regionExpectation_graphNeighborhood_le
    (lineDomainGraph Λ) (lineDomainGraph_card_sphere_le_two Λ) Φ
    (fun X ↦ X.2.2) (fun X ↦ X.2.isChainSupport.card_le) hΦh b₀
    (ManyBody.DomainInteraction.sum_norm_terms_containing_le Φ hΦn) (C ×ˢ Finset.univ)
        (fun p ↦ p.1.1) Z
    (fun p hp ↦ Finset.subset_biUnion_of_mem (fun X ↦ X.1) (Finset.mem_product.mp hp).1)
    (fun p _ ↦ p.1.2.isChainSupport.card_le) A
    (fun p _ ↦ (h.partialSwap_term_difference_spec hh hhJ D p.1 p.2).1)
    (2 * |J|) (fun p _ ↦ (h.partialSwap_term_difference_spec hh hhJ D p.1 p.2).2.2.trans
      (mul_le_mul_of_nonneg_left (le_abs_self J) (by norm_num))) (m : ℝ) t
  dsimp only at hgen
  rw [Nat.floor_natCast, hΦ, ← hdiff] at hgen
  have hc : ((C ×ˢ (Finset.univ : Finset Bool)).card : ℝ) ≤
      (chainCrossConst R : ℝ) * Λ.card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
    exact_mod_cast hcount
  have ha : 0 ≤ a := (div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))).le
  calc
    _ ≤ _ := hgen
    _ ≤ ((chainCrossConst R : ℝ) * Λ.card) *
        (2 * (a * (R + 1 : ℝ) ^ 2 * (2 * |J|) * Real.exp (v * |t| - (m : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

/-- A single supported unitary path yields the localized truncated
Gaussian integrals for every supported observable, variance and cutoff. A negative radius
gives the radius-zero neighborhood.
Source: TNLean note, `part2a_mps_information.tex`, lines 381–402. -/
theorem exists_supported_gaussian_integral (R : ℕ) (J : ℝ) :
    ∃ C v : ℝ, 0 < C ∧ 0 < v ∧
      ∀ (q : ℕ), 1 ≤ q →
      ∀ (L : ℕ) (h : ChainInteraction L q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J) (D : Finset (Fin L))
        (ℓ : ℝ),
        let K := h.doubledFin.hamiltonian
        let pr := Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin q) fun _ ↦ Fin q
        let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv)
        let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
        let K' := F * K * Fᴴ
        let crossing := ManyBody.crossingTerms (fun X : ChainSupport L R ↦ X.1) D
        let Z := crossing.biUnion (fun X ↦ X.1)
        let N := fun S : Finset (Fin L) ↦
          ManyBody.graphNeighborhood (SimpleGraph.pathGraph L) S ⌊ℓ⌋₊
        ∃ U : ℝ → Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ,
          U 0 = 1 ∧
          (∀ t, HasDerivAt U
            ((Complex.I • ManyBody.regionExpectation (N Z)
              (ManyBody.heisenbergEvolution K' t (K' - K))) * U t) t) ∧
          (∀ t, U t ∈ Matrix.unitaryGroup (Fin L → Fin (q * q)) ℂ) ∧
          (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) (N Z : Finset (Fin L))) ∧
          ∀ (Q : Finset (Fin L))
            (W : Matrix (Fin L → Fin (q * q)) (Fin L → Fin (q * q)) ℂ),
            W ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q →
            ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
              let B := N (Q ∪ Z)
              let M := ∫ t : ℝ in Set.Icc (-T) T,
                ManyBody.regionExpectation (N Q) (ManyBody.heisenbergEvolution K' t W) * U t
                  ∂gaussianReal 0 η
              M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
              ‖M‖ ≤ ‖W‖ ∧
              ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K W‖ ≤
                ‖W‖ * C * (L : ℝ) ^ 2 * (1 + T) *
                  Real.exp (v * T - ℓ / 2) := by
  classical
  let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
  let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
    (1 - Real.exp (-(1 / 2)))
  let d : ℝ := 4 * |J| * a * (R + 1 : ℝ) ^ 2 * (ManyBody.chainCrossConst R : ℝ)
  have ha : 0 < a := div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
  have hd : 0 ≤ d := by positivity
  refine ⟨a + d, 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1, by positivity, by positivity, ?_⟩
  intro q hq L h hh hhJ D ℓ K pr e F K' crossing Z N
  let Φ : ManyBody.Interaction (fun _ : Fin L ↦ Fin (q * q)) (fun X : ChainSupport L R ↦ X.1) :=
    (h.doubled.conj (ManyBody.pairSwapOp (X := fun _ ↦ Fin q) D) fun X ↦
        ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators D
          (h.doubled.mem X)).relabel (X' := fun _ ↦ Fin (q * q)) (Equiv.refl _)
      (fun _ ↦ finProdFinEquiv) (fun X : ChainSupport L R ↦ X.1) fun _ _ ↦ Iff.rfl
  have hΦ : Φ.hamiltonian = K' :=
    (ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled (X' := fun _ ↦ Fin (q * q))
      h D _ (Equiv.refl _) (fun _ ↦ finProdFinEquiv) _ fun _ _ ↦ Iff.rfl).trans
      (congrArg (fun M ↦ F * M * Fᴴ) h.hamiltonian_doubledFin.symm)
  have hΦh : ∀ X, (Φ.term X).IsHermitian := fun X ↦
    ManyBody.Interaction.isHermitian_relabel_term _ _ _ _
      (ManyBody.Interaction.isHermitian_conj_term _ _
        (ManyBody.Interaction.isHermitian_doubled_term (hh X)))
  have hΦn : ∀ X, ‖Φ.term X‖ ≤ 2 * J := fun X ↦
    ((ManyBody.Interaction.norm_relabel_term _ _ _ _ _ X).trans
      (ManyBody.Interaction.norm_conj_term _ (ManyBody.pairSwapOp_mem_unitaryGroup D) _
        X)).trans_le ((ManyBody.Interaction.norm_doubled_term_le h X).trans
          (by linarith [hhJ X]))
  have hgen := exists_supported_gaussian_integral_graphNeighborhood
    (SimpleGraph.pathGraph L) (SimpleGraph.pathGraph_card_sphere_le_two L) Φ
    (fun X ↦ ManyBody.ChainSupport.edist_le X) (fun X ↦ X.2.card_le) hΦh b₀
    (ManyBody.ChainInteraction.sum_norm_terms_containing_le Φ hΦn)
        (ManyBody.Interaction.isHermitian_hamiltonian (Φ := h.doubledFin) fun X ↦
          (ManyBody.Interaction.isHermitian_doubled_term (hh X)).reindex _) Z ℓ
        d hd (fun s ↦ by
      rw [hΦ, Fintype.card_fin]
      exact h.norm_relativeGenerator_sub_regionExpectation_le hh hhJ D hq ℓ s)
  simp only [hΦ, Fintype.card_fin] at hgen
  exact hgen

/-- One supported unitary path gives the localized truncated Gaussian integrals
for every supported observable, variance and cutoff on an actual finite integer
domain. This extends the chain argument of the TNLean one-dimensional note,
part2a_mps_information.tex, lines 381–402, to the finite domains specified in
part0_preamble.tex, lines 191–215. No gap or information-reset conclusion is asserted. -/
theorem exists_supported_gaussian_integral_domain (R : ℕ) (J : ℝ) :
    ∃ C v : ℝ, 0 < C ∧ 0 < v ∧
      ∀ (q : ℕ), 1 ≤ q →
      ∀ (Λ : Finset ℤ) (h : DomainInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian)
          (_ : ∀ X, ‖h.term X‖ ≤ J)
        (D : Finset (Fin Λ.card)) (m : ℕ),
        let K := h.doubledFin.hamiltonian
        let pr := Equiv.arrowProdEquivProdArrow (Fin Λ.card) (fun _ ↦ Fin q) fun _ ↦ Fin q
        let e := pr.symm.trans (Equiv.arrowCongr (Equiv.refl (Fin Λ.card)) finProdFinEquiv)
        let F := Matrix.reindex e e (Matrix.reindex pr pr (ManyBody.pairSwapOp D))
        let K' := F * K * Fᴴ
        let crossing := ManyBody.crossingTerms (fun X : DomainSupport Λ R ↦ X.1) D
        let Z := crossing.biUnion (fun X ↦ X.1)
        let N := fun S : Finset (Fin Λ.card) ↦
          ManyBody.graphNeighborhood (lineDomainGraph Λ) S m
        ∃ U : ℝ → Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ,
          U 0 = 1 ∧
          (∀ t, HasDerivAt U
            ((Complex.I • ManyBody.regionExpectation (N Z)
              (ManyBody.heisenbergEvolution K' t (K' - K))) * U t) t) ∧
          (∀ t, U t ∈ Matrix.unitaryGroup (Fin Λ.card → Fin (q * q)) ℂ) ∧
          (∀ t, U t ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q))
              (N Z : Finset (Fin Λ.card))) ∧
          ∀ (Q : Finset (Fin Λ.card))
            (W : Matrix (Fin Λ.card → Fin (q * q)) (Fin Λ.card → Fin (q * q)) ℂ),
            W ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) Q →
            ∀ (η : ℝ≥0) (T : ℝ), 0 ≤ T →
              let B := N (Q ∪ Z)
              let M := ∫ t : ℝ in Set.Icc (-T) T,
                ManyBody.regionExpectation (N Q) (ManyBody.heisenbergEvolution K' t W) * U t
                  ∂gaussianReal 0 η
              M ∈ ManyBody.supportedOperators (fun _ ↦ Fin (q * q)) B ∧
              ‖M‖ ≤ ‖W‖ ∧
              ‖M - GaussianFilter.gaussianIntertwinerTruncated η T K' K W‖ ≤
                ‖W‖ * C * (Λ.card : ℝ) ^ 2 * (1 + T) *
                  Real.exp (v * T - (m : ℝ) / 2) := by
  classical
  let b₀ : ℝ := ((2 ^ (2 * R + 1) : ℕ) : ℝ) * (2 * J)
  let a : ℝ := 2 * (2 + 4 * |b₀| * Real.exp (2 * R)) * Real.exp 1 /
    (1 - Real.exp (-(1 / 2)))
  let d : ℝ := 4 * |J| * a * (R + 1 : ℝ) ^ 2 * (ManyBody.chainCrossConst R : ℝ)
  have ha : 0 < a := div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num)))
  have hd : 0 ≤ d := by positivity
  refine ⟨a + d, 2 * (R + 1) * |b₀| * Real.exp (2 * R) + 1, by positivity, by positivity, ?_⟩
  intro q hq Λ h hh hhJ D m K pr e F K' crossing Z N
  let Φ : ManyBody.Interaction (fun _ : Fin Λ.card ↦ Fin (q * q))
      (fun X : DomainSupport Λ R ↦ X.1) :=
    (h.doubled.conj (ManyBody.pairSwapOp (X := fun _ ↦ Fin q) D) fun X ↦
        ManyBody.pairSwapOp_mul_mul_conjTranspose_mem_supportedOperators D
          (h.doubled.mem X)).relabel (X' := fun _ ↦ Fin (q * q)) (Equiv.refl _)
      (fun _ ↦ finProdFinEquiv) (fun X : DomainSupport Λ R ↦ X.1) fun _ _ ↦ Iff.rfl
  have hΦ : Φ.hamiltonian = K' :=
    (ManyBody.Interaction.hamiltonian_relabel_conj_pairSwapOp_doubled (X' := fun _ ↦ Fin (q * q))
      h D _ (Equiv.refl _) (fun _ ↦ finProdFinEquiv) _ fun _ _ ↦ Iff.rfl).trans
      (congrArg (fun M ↦ F * M * Fᴴ) h.hamiltonian_doubledFin.symm)
  have hΦh : ∀ X, (Φ.term X).IsHermitian := fun X ↦
    ManyBody.Interaction.isHermitian_relabel_term _ _ _ _
      (ManyBody.Interaction.isHermitian_conj_term _ _
        (ManyBody.Interaction.isHermitian_doubled_term (hh X)))
  have hΦn : ∀ X, ‖Φ.term X‖ ≤ 2 * J := fun X ↦
    ((ManyBody.Interaction.norm_relabel_term _ _ _ _ _ X).trans
      (ManyBody.Interaction.norm_conj_term _ (ManyBody.pairSwapOp_mem_unitaryGroup D) _
        X)).trans_le ((ManyBody.Interaction.norm_doubled_term_le h X).trans
          (by linarith [hhJ X]))
  have hgen := exists_supported_gaussian_integral_graphNeighborhood
    (lineDomainGraph Λ) (ManyBody.lineDomainGraph_card_sphere_le_two Λ) Φ
    (fun X ↦ X.2.2) (fun X ↦ X.2.isChainSupport.card_le) hΦh b₀
    (ManyBody.DomainInteraction.sum_norm_terms_containing_le Φ hΦn)
        (ManyBody.Interaction.isHermitian_hamiltonian (Φ := h.doubledFin) fun X ↦
          (ManyBody.Interaction.isHermitian_doubled_term (hh X)).reindex _) Z (m : ℝ)
        d hd (fun s ↦ by
      rw [hΦ, Nat.floor_natCast, Fintype.card_fin]
      exact h.norm_relativeGenerator_sub_regionExpectation_le hh hhJ D hq m s)
  simp only [hΦ, Nat.floor_natCast, Fintype.card_fin] at hgen
  exact hgen

end ManyBody
