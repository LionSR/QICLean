/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.Chain.ConsecutiveRegions
import QICLean.Spectral.LowEnergy.WeightedLowRestriction
import QICLean.Spectral.Eigenvalue.MatrixSpectralDecomp
import QICLean.Spectral.Filter.EnergyTruncation
import QICLean.Spectral.Projection.ExponentialDrop
import QICLean.Algebra.Combinatorics.FinSum
import Mathlib.Tactic.FinCases

/-!
# Spectral tails and truncation on a chain

Bounds for the spectral tails across consecutive cuts and for truncating the two
exterior blocks of a nearest-neighbour Hamiltonian.

**Local fix (constant).** The boundary estimate uses the constant 2 obtained by
centering an interaction term at half the identity. See
`docs/paper-gaps/aklv13_robustness_constants.tex`.

Moved from TNLean at commit `2417e0a2e4d8a1dc2db0a14e0c9cae4ca735829e`.
Sources in `TNLean/MPS/AreaLaw/Spectral/`: `SpectralTail.lean`, `GroundStateTail.lean`,
`RegionalTruncationResidual.lean` and `TwoBlockTruncation.lean`. The lemmas are collected under
`ManyBody.BondInteraction`.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace ManyBody.BondInteraction

/-- A positive contraction centered at half the identity has norm at most
one half. This is the centering correction in AKLV, Lemma 6.6(2). -/
private theorem norm_sub_half_one_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h0 : 0 ≤ A) (h1 : A ≤ 1) :
    ‖A - (1 / 2 : ℂ) • 1‖ ≤ (1 / 2 : ℝ) := by
  let c : Matrix n n ℂ := (1 / 2 : ℂ) • 1
  have hsplit : (1 : Matrix n n ℂ) = c + c := by
    dsimp [c]
    rw [← add_smul]
    norm_num
  have hlo : -c ≤ A - c := by
    simpa only [zero_sub] using sub_le_sub_right h0 c
  have hhi : A - c ≤ c := by
    apply (sub_le_iff_le_add).2
    rw [← hsplit]
    exact h1
  have hc : IsSelfAdjoint c := by
    dsimp [c]
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.coe_smul]
    exact (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.one _)
  have hb := IsSelfAdjoint.norm_le_max_of_le_of_le hlo hhi
    ((IsSelfAdjoint.of_nonneg h0).sub hc)
  have hnorm : ‖c‖ ≤ (1 / 2 : ℝ) := by
    calc
      ‖c‖ = (1 / 2 : ℝ) * ‖(1 : Matrix n n ℂ)‖ := by
        dsimp [c]
        norm_num [norm_smul]
      _ ≤ (1 / 2 : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left
          (IsStarProjection.norm_le _ (IsStarProjection.one (Matrix n n ℂ))) (by norm_num)
      _ = 1 / 2 := by ring
  exact hb.trans (by simpa only [norm_neg, max_self] using hnorm)

/-- A single unit boundary bond has an exponentially small block across
separated energies of any original nearest-neighbour regional sum. Scalar
shifts of that sum are allowed. Auxiliary to AKLV, arXiv:1301.1162v1,
Lemma 6.6(2); the coefficient is one after centering the boundary term. -/
theorem norm_boundary_spectral_offDiagonal_le {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (a : Fin (L - 1)) (z t u : ℝ) (hut : u ≤ t) :
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := (Φ.partialHamiltonian I) - (z : ℂ) • 1
    ‖Matrix.spectralProjectionGE B t * Φ.term a *
      (1 - Matrix.spectralProjectionGE B u)‖ ≤ Real.exp (-(t - u) / 8) := by
  intro B
  let O := Φ.term a - (1 / 2 : ℂ) • 1
  have hB : B.IsHermitian := by
    change IsSelfAdjoint B
    apply IsSelfAdjoint.sub
    · exact IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)
    · rw [Complex.coe_smul]
      exact (IsSelfAdjoint.all z).smul (IsSelfAdjoint.one _)
  have hO : ManyBody.IsSupportedOn (X := fun _ ↦ Fin q) O
      (interval L a.val (a.val + 2)) := by
    change _ ∈ ManyBody.supportedOperators _ _
    exact sub_mem
      (Φ.mem a)
      (SMulMemClass.smul_mem _ (one_mem (ManyBody.supportedOperators _ _)))
  have hnorm : ‖O‖ ≤ (1 / 2 : ℝ) := norm_sub_half_one_le (Φ.term a) (h0 a) (h1 a)
  have hconj := ManyBody.BondInteraction.norm_exp_conjugation_shift_le_two I Φ
    (fun i _ ↦ h0 i) (fun i _ ↦ h1 i) O hO (z : ℂ)
    (1 / 8) (by norm_num) le_rfl
  have hzero := hB.spectralProjectionGE_mul_one_sub_eq_zero hut
  have hcenter : Matrix.spectralProjectionGE B t * Φ.term a *
      (1 - Matrix.spectralProjectionGE B u) =
      Matrix.spectralProjectionGE B t * O * (1 - Matrix.spectralProjectionGE B u) := by
    dsimp [O]
    conv_rhs => lhs; rw [mul_sub]
    rw [sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hzero, smul_zero, sub_zero]
  rw [hcenter]
  calc
    _ ≤ Real.exp (-(1 / 8) * (t - u)) *
        ‖NormedSpace.exp (((1 / 8 : ℝ) : ℂ) • B) * O *
          NormedSpace.exp (-(((1 / 8 : ℝ) : ℂ) • B))‖ :=
      hB.norm_spectral_offDiagonal_le_exp_conjugation O t u (1 / 8) (by norm_num)
    _ ≤ Real.exp (-(1 / 8) * (t - u)) * (2 * ‖O‖) :=
      mul_le_mul_of_nonneg_left hconj (Real.exp_pos _).le
    _ ≤ Real.exp (-(t - u) / 8) := by
      have htwo : 2 * ‖O‖ ≤ 1 := by linarith
      simpa only [mul_one, show -(1 / 8 : ℝ) * (t - u) = -(t - u) / 8 by ring] using
        mul_le_mul_of_nonneg_left htwo (Real.exp_pos (-(1 / 8) * (t - u))).le

/-- The boundary coupling of AKLV has norm at most `2 exp(-(t-u)/8)`
between the two separated energy windows of the complementary Hamiltonian.
AKLV, arXiv:1301.1162v1, Lemma 6.6(2). The generator consists of original
positive unit nearest-neighbour terms and an arbitrary real scalar shift. -/
theorem norm_two_boundary_spectral_offDiagonal_le {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (a b : Fin (L - 1)) (z t u : ℝ) (hut : u ≤ t) :
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := (Φ.partialHamiltonian I) - (z : ℂ) • 1
    ‖Matrix.spectralProjectionGE B t * (Φ.term a + Φ.term b) *
      (1 - Matrix.spectralProjectionGE B u)‖ ≤ 2 * Real.exp (-(t - u) / 8) := by
  intro B
  rw [mul_add, add_mul]
  exact (norm_add_le _ _).trans (by
    have ha := norm_boundary_spectral_offDiagonal_le I Φ h0 h1 a z t u hut
    have hb := norm_boundary_spectral_offDiagonal_le I Φ h0 h1 b z t u hut
    dsimp only at ha hb
    linarith)

/-- The boundary perturbation has a short imaginary-time norm bound
independent of the chain length. This is derived from the original local
positive unit terms, as required by AKLV, arXiv:1301.1162v1, Lemma 6.6. -/
theorem norm_exp_conjugation_two_boundary_le_four {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (a b : Fin (L - 1)) (z : ℝ) :
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      (Φ.partialHamiltonian I) - (z : ℂ) • 1
    ‖NormedSpace.exp (((1 / 8 : ℝ) : ℂ) • B) * (Φ.term a + Φ.term b) *
      NormedSpace.exp (-(((1 / 8 : ℝ) : ℂ) • B))‖ ≤ 4 := by
  intro B
  have hbound (i : Fin (L - 1)) :=
    ManyBody.BondInteraction.norm_exp_conjugation_shift_le_two I Φ
      (fun j _ ↦ h0 j) (fun j _ ↦ h1 j)
      (Φ.term i) (Φ.mem i) (z : ℂ) (1 / 8) (by norm_num) le_rfl
  have hnorm (i : Fin (L - 1)) : ‖Φ.term i‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg (Φ.term i) (h0 i)).mpr (h1 i)
  rw [mul_add, add_mul]
  exact (norm_add_le _ _).trans (by
    have ha := hbound a
    have hb := hbound b
    dsimp only at ha hb
    linarith [hnorm a, hnorm b])

/-- **Explicit AKLV truncation lemma.** An eigenvector of the normalized
chain with energy in `[0,6]` has high-energy tail at most
`2 exp(-(t-20)/8)` for the complementary Hamiltonian. In particular this
applies to the ground vector after the normalization of Section 6.1.
AKLV, arXiv:1301.1162v1, Lemma 6.7; this proof uses an exponential moment
instead of the printed shell induction. No energy-tail estimate is assumed. -/
theorem norm_groundState_highProjection_le_exp {L q : ℕ}
    (I : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (a b : Fin (L - 1)) (z e t : ℝ)
    (x : EuclideanSpace ℂ (Fin L → Fin q))
    (he0 : 0 ≤ e) (he6 : e ≤ 6) :
    let B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
      (Φ.partialHamiltonian I) - (z : ℂ) • 1
    Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (B + (Φ.term a + Φ.term b)) x =
        (e : ℂ) • x →
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ) (Matrix.spectralProjectionGE B t) x‖ ≤
        2 * Real.exp (-(t - 20) / 8) * ‖x‖ := by
  intro B he
  have hB : B.IsHermitian := by
    change IsSelfAdjoint B
    apply IsSelfAdjoint.sub
    · exact IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)
    · rw [Complex.coe_smul]
      exact (IsSelfAdjoint.all z).smul (IsSelfAdjoint.one _)
  have hC := norm_exp_conjugation_two_boundary_le_four I Φ h0 h1 a b z
  have hsmall : |e| + 4 ≤ (20 : ℝ) / 2 := by rw [abs_of_nonneg he0]; linarith
  simpa only [show -(1 / 8 : ℝ) * (t - 20) = -(t - 20) / 8 by ring] using
    hB.norm_highProjection_eigenvector_le_exp (Φ.term a + Φ.term b) x e (1 / 8) 20 4 t
      (by norm_num) (by norm_num) he hC hsmall

/-- The sum of supplied original nearest-neighbour boundary bonds has
short-time conjugation norm at most twice their number, even after a scalar
energy shift: the bond case of `ManyBody.Interaction.norm_exp_conjugation_shift_sum_le`.
Supporting AKL14, arXiv:1406.3898, low70.tex, lines 795–880.
No conjugation or residual estimate is supplied as a hypothesis. -/
theorem norm_exp_conjugation_boundary_sum_le
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ Φ.term i) (h1 : ∀ i ∈ I ∪ J, Φ.term i ≤ 1)
    (z : ℂ) (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1 / 8) :
    let H : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.partialHamiltonian I
    ‖NormedSpace.exp ((t : ℂ) • (H - z • 1)) * (Φ.partialHamiltonian J) *
      NormedSpace.exp (-((t : ℂ) • (H - z • 1)))‖ ≤ 2 * (J.card : ℝ) := by
  classical
  intro H
  have hI : H = ∑ i ∈ I, (Φ.restrict (· ∈ I ∪ J)).term i :=
    (ManyBody.Interaction.partialHamiltonian_restrict_of_forall fun _ hi ↦
      Finset.mem_union_left J hi).symm
  have hJ : Φ.partialHamiltonian J = ∑ j ∈ J, (Φ.restrict (· ∈ I ∪ J)).term j :=
    (ManyBody.Interaction.partialHamiltonian_restrict_of_forall fun _ hj ↦
      Finset.mem_union_right I hj).symm
  rw [hI, hJ]
  exact (Φ.restrict (· ∈ I ∪ J)).norm_exp_conjugation_shift_sum_le I J (k := 2) (g := 2)
    (fun i ↦ by
      rw [ManyBody.Interaction.restrict_term]
      split_ifs with hi
      exacts [h0 i hi, le_rfl])
    (fun i ↦ by
      rw [ManyBody.Interaction.restrict_term]
      split_ifs with hi
      exacts [h1 i hi, zero_le_one])
    (fun i ↦ by simpa using ManyBody.card_interval_le (L := L) i.val (i.val + 2))
    (card_filter_mem_bond_le_two I) z ht0 (by push_cast; linarith)

/-- The actual exponential weight on the original regional sum has a small
restriction from the actual low spectral span to the original high projection
range. All commutations, range memberships, quadratic bounds and boundary norms
are derived. The structural commutation and matrix order must be established
from the spatial decomposition in a physical application.

This is an auxiliary weighted spectral estimate for ALVV,
arXiv:1602.08828v2, Theorem t:ais, lines 1010--1024, and AKL14,
arXiv:1406.3898, Theorem lowspec, lines 1102--1168. It is not the full physical
truncation-error or subspace-closeness theorem. -/
theorem exists_weighted_low_restriction
    {L q : ℕ} (I J : Finset (Fin (L - 1)))
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i ∈ I ∪ J, 0 ≤ Φ.term i) (h1 : ∀ i ∈ I ∪ J, Φ.term i ≤ 1)
    (X : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (r u e s : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 8)
    (hXA : Commute X (Φ.partialHamiltonian I))
    (horder : u • Matrix.spectralProjectionGE (Φ.partialHamiltonian I) (r + u) ≤ X)
    (b : OrthonormalBasis (Fin L → Fin q) ℂ
      (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ)
    (hEigen : ∀ j, Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (X + Φ.partialHamiltonian J) (b j) = (a j : ℂ) • b j)
    (hgap : 2 * (J.card : ℝ) < u - e) :
    let A : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Φ.partialHamiltonian I
    let Q := Matrix.spectralProjectionGE A (r + u)
    let W := NormedSpace.exp (s • (A - (r + u) •
      (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)))
    let T := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a e
    let U := (T Q).range
    ∃ Z : G →L[ℂ] U,
      U.subtypeL ∘L Z = (T W * T Q).domRestrict G ∧
      ‖Z‖ ≤ (2 * (J.card : ℝ)) / (u - e - 2 * (J.card : ℝ)) := by
  intro A Q W T G U
  have hA : A.IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i hi ↦
      h0 i (Finset.mem_union_left J hi))).isHermitian
  have hconj := norm_exp_conjugation_boundary_sum_le
    I J Φ h0 h1 ((r + u : ℝ) : ℂ) s hs0.le hs1
  simp only [Complex.coe_smul] at hconj
  exact Matrix.exists_weighted_low_restriction_of_conjugation_le A X _ hA r u e s _ hs0
    hXA horder b a hEigen hconj hgap

/-- The single-region tail bound for a literal partially clipped consecutive
regional sum. Original bond supports imply commutation, and the original
regional lower bounds imply the required order. No current-commutation,
current-order or norm estimate is supplied. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005. -/
theorem norm_consecutive_regional_truncation_low_le
    {L q m : ℕ} (k : Fin (m + 1) → ℕ) (hk : Monotone k)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (e : Fin m → ℝ) (T : Finset (Fin m)) (j : Fin m)
    (J : Finset (Fin (L - 1))) (u ε s t : ℝ)
    (hs0 : 0 < s) (hs1 : s ≤ 1 / 8) (hu : 0 ≤ u) (hut : u ≤ t)
    (b : OrthonormalBasis (Fin L → Fin q) ℂ (EuclideanSpace ℂ (Fin L → Fin q)))
    (a : (Fin L → Fin q) → ℝ) :
    let A : Fin m → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := fun i ↦
      ∑ r ∈ (Finset.univ : Finset (Fin (L - 1))).filter
        (fun r ↦ k i.castSucc ≤ r.val ∧ r.val + 1 < k i.succ), Φ.term r
    let X := ∑ i, ((if i ∈ T then cfc (fun x : ℝ ↦ min x (e i + t)) (A i)
      else A i) - (e i : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
    let ι := Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a ε
    (∀ i, (e i : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) ≤ A i) →
    (∀ v, ι (X + Φ.partialHamiltonian J) (b v) = (a v : ℂ) • b v) →
    2 * (J.card : ℝ) < u - ε →
    ‖(ι (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict G‖ ≤
      (Real.exp (-s * (t - u) - 1) / s) *
        ((2 * (J.card : ℝ)) / (u - ε - 2 * (J.card : ℝ))) := by
  intro A X ι G he hEigen hgap
  have hA (i : Fin m) : (A i).IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun r _ ↦ h0 r)).isHermitian
  have hconj := norm_exp_conjugation_boundary_sum_le
    ((Finset.univ : Finset (Fin (L - 1))).filter
      (fun r ↦ k j.castSucc ≤ r.val ∧ r.val + 1 < k j.succ)) J Φ
    (fun r _ ↦ h0 r) (fun r _ ↦ h1 r) ((e j + u : ℝ) : ℂ) s hs0.le hs1
  simp only [Complex.coe_smul] at hconj
  exact Matrix.norm_partially_clipped_truncation_low_le A hA
    (pairwise_commute_sum_internal_consecutive_regions k hk Φ) e he T j _ u ε s t _
    hs0 hu hut b a hEigen hconj hgap

/-- The three actual consecutive regional sums used for clipping the two exterior
blocks. AKLV, arXiv:1301.1162v1, Section 6.1, the definition of `H^(t)` after (5). -/
def threeRegionHamiltonians {L q : ℕ} (l r : ℕ)
    (Φ : ManyBody.BondInteraction L q) :
    Fin 3 → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  let k : Fin 4 → ℕ := ![0, l, r, L]
  fun j ↦ ∑ i ∈ Finset.univ.filter
    (fun i : Fin (L - 1) ↦ k j.castSucc ≤ i.val ∧ i.val + 1 < k j.succ), Φ.term i

open Classical in
/-- The centered partially clipped Hamiltonian: the selector `T : Finset (Fin 2)`
can select only the left and right blocks. The middle block is never clipped.
AKLV, arXiv:1301.1162v1, Section 6.1, the definition of `H^(t)` after (5). -/
noncomputable def twoBlockTruncatedHamiltonian {L q : ℕ} (l r : ℕ)
    (Φ : ManyBody.BondInteraction L q)
    (e : Fin 3 → ℝ) (t : ℝ) (T : Finset (Fin 2)) :
    Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ :=
  let A := threeRegionHamiltonians l r Φ
  let O := T.image (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3))
  (∑ j, ((if j ∈ O then cfc (fun x : ℝ ↦ min x (e j + t)) (A j) else A j) -
    (e j : ℂ) • 1)) +
    ∑ i ∈ Finset.univ.filter
      (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)), Φ.term i

/-- The original bond sum is the sum of its three consecutive regional Hamiltonians and
the crossing bonds. Empty regions and coincident cuts are included. Auxiliary to AKLV,
arXiv:1301.1162v1, Section 6.1, and ALVV, arXiv:1602.08828v2, `def:hard-trunc`,
lines 873–886. -/
theorem hamiltonian_eq_sum_threeRegionHamiltonians_add_crossings {L q l r : ℕ} (hlr : l ≤ r)
    (Φ : ManyBody.BondInteraction L q) :
    Φ.hamiltonian = (∑ j, threeRegionHamiltonians l r Φ j) +
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (L - 1) ↦ i.val + 1 ∈ ({l, r} : Finset ℕ)), Φ.term i := by
  have hempty (c : ℕ) :
      (∑ i ∈ Finset.univ.filter (fun i : Fin (L - 1) ↦
        c ≤ i.val ∧ i.val + 1 < c), Φ.term i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have := (Finset.mem_filter.mp hi).2
    omega
  have hsum := Fin.sum_eq_five_internal_add_crossings
    (L := L) (k1 := l) (k2 := l) (k3 := r) (k4 := r) le_rfl hlr le_rfl Φ.term
  rw [ManyBody.Interaction.hamiltonian, hsum]
  simp [threeRegionHamiltonians, Fin.sum_univ_three, hempty]
  abel

private theorem two_block_tail_coefficient_le {c ε t : ℝ} (hc : c ≤ 2) :
    (Real.exp (-(1 / 8) * (t - (ε + 5)) - 1) / (1 / 8)) *
      ((2 * c) / ((ε + 5) - ε - 2 * c)) ≤
        32 * Real.exp (-(t - ε) / 8) := by
  have hd : 1 ≤ (ε + 5) - ε - 2 * c := by linarith
  have hq : (2 * c) / ((ε + 5) - ε - 2 * c) ≤ 4 := by
    apply (div_le_iff₀ (by linarith : 0 < (ε + 5) - ε - 2 * c)).mpr
    linarith
  have hexp : -(1 / 8 : ℝ) * (t - (ε + 5)) - 1 =
      -3 / 8 + (-(t - ε) / 8) := by ring
  calc
    _ ≤ (Real.exp (-(1 / 8) * (t - (ε + 5)) - 1) / (1 / 8)) * 4 :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 32 * Real.exp (-3 / 8) * Real.exp (-(t - ε) / 8) := by
      rw [hexp, Real.exp_add]
      ring
    _ ≤ 32 * 1 * Real.exp (-(t - ε) / 8) := by
      gcongr
      exact Real.exp_le_one_iff.mpr (by norm_num)
    _ = _ := by ring

open Classical in
/-- The actual two-outer-block truncation has exponentially small residual on each
actual partially clipped low-energy space. The only energy normalization assumptions
are the original regional lower bounds; no perturbation estimate or low-space witness
is supplied. AKLV, arXiv:1301.1162v1, Section 6.1, equation (5) and Theorem 6.1.
This bounded residual statement does not assert that theorem's gap preservation. -/
theorem norm_twoBlockTruncatedHamiltonian_low_le {L q l r : ℕ}
    (hlr : l ≤ r) (hrL : r ≤ L)
    (Φ : ManyBody.BondInteraction L q)
    (h0 : ∀ i, 0 ≤ Φ.term i) (h1 : ∀ i, Φ.term i ≤ 1)
    (e : Fin 3 → ℝ) (ε t : ℝ) (hε : 0 ≤ ε) (ht : ε + 5 ≤ t)
    (he : ∀ j, (e j : ℂ) • 1 ≤ threeRegionHamiltonians l r Φ j) :
    let B := twoBlockTruncatedHamiltonian l r Φ e t
    ∃ hB : ∀ T, (B T).IsHermitian,
      B ∅ = Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1 ∧
      ∀ T : Finset (Fin 2),
        let G := Submodule.spectralSpanLE (hB T).eigenvectorBasis (hB T).eigenvalues ε
        ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
          (B ∅ - B Finset.univ)).domRestrict G)‖ ≤
            64 * Real.exp (-(t - ε) / 8) := by
  intro B
  let k : Fin 4 → ℕ := ![0, l, r, L]
  let A := threeRegionHamiltonians l r Φ
  let J := (Finset.univ : Finset (Fin (L - 1))).filter
    (fun i ↦ i.val + 1 ∈ ({l, r} : Finset ℕ))
  let Y := ∑ i ∈ J, Φ.term i
  let O : Finset (Fin 3) := {0, 2}
  let clip (T : Finset (Fin 2)) := T.image (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3))
  let X (T : Finset (Fin 2)) := ∑ j,
    ((if j ∈ clip T then cfc (fun x : ℝ ↦ min x (e j + t)) (A j) else A j) -
      (e j : ℂ) • (1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ))
  have hk : Monotone k := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [k]
    omega
  have hA (j : Fin 3) : (A j).IsHermitian :=
    (IsSelfAdjoint.of_nonneg (Finset.sum_nonneg fun i _ ↦ h0 i)).isHermitian
  have hY : Y.PosSemidef := nonneg_iff_posSemidef.mp
    (show 0 ≤ Y from Finset.sum_nonneg fun i _ ↦ h0 i)
  have hB (T : Finset (Fin 2)) : (B T).IsHermitian := by
    obtain ⟨hX, _⟩ := Matrix.centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t (clip T) hA he (0 : (Fin L → Fin q) → ℂ) (by intro j; simp) (by linarith)
    exact (hX.add hY).isHermitian
  have hcenter : B ∅ = Φ.hamiltonian - (((∑ j, e j) : ℝ) : ℂ) • 1 := by
    have hsum := hamiltonian_eq_sum_threeRegionHamiltonians_add_crossings hlr Φ
    simp only [B, twoBlockTruncatedHamiltonian, Finset.image_empty, Finset.notMem_empty,
      ite_false, Finset.sum_sub_distrib]
    rw [hsum]
    push_cast
    rw [Finset.sum_smul]
    abel
  refine ⟨hB, hcenter, ?_⟩
  intro T G
  have hJ : (J.card : ℝ) ≤ 2 := by exact_mod_cast Fin.card_filter_two_cut_crossing_le L l r
  have hEigen (v : Fin L → Fin q) :
      Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (X T + Y) ((hB T).eigenvectorBasis v) =
          ((hB T).eigenvalues v : ℂ) • (hB T).eigenvectorBasis v := by
    exact (hB T).toEuclideanCLM_eigenvectorBasis v
  have hsingle (j : Fin 3) :
      ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict G)‖ ≤
          32 * Real.exp (-(t - ε) / 8) := by
    have htail := norm_consecutive_regional_truncation_low_le k hk Φ h0 h1
      e (clip T) j J (ε + 5) ε (1 / 8) t
      (by norm_num) (by norm_num) (by linarith) ht
      (hB T).eigenvectorBasis (hB T).eigenvalues he hEigen (by linarith)
    exact htail.trans (two_block_tail_coefficient_le hJ)
  have hsum := Matrix.norm_centered_clipping_discrepancy_domRestrict_le_sum
    A (fun j ↦ cfc (fun x : ℝ ↦ min x (e j + t)) (A j))
    (fun j ↦ (e j : ℂ)) O G
  have hfull : clip Finset.univ = O := by
    change (Finset.univ : Finset (Fin 2)).image
      (fun j ↦ (⟨2 * j.val, by omega⟩ : Fin 3)) = {0, 2}
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hsumB : ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      (B ∅ - B Finset.univ)).domRestrict G)‖ ≤
      ∑ j ∈ O, ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
        (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict G)‖ := by
    change _ ≤ _ at hsum
    change ‖((Matrix.toEuclideanCLM (n := Fin L → Fin q) (𝕜 := ℂ)
      ((X ∅ + Y) - (X Finset.univ + Y))).domRestrict G)‖ ≤ _
    simpa only [X, hfull, clip, Finset.image_empty,
      Finset.notMem_empty, ite_false, add_sub_add_right_eq_sub] using hsum
  exact hsumB.trans (by
    calc
      _ ≤ ∑ _j ∈ O, (32 * Real.exp (-(t - ε) / 8)) :=
        Finset.sum_le_sum fun j _ ↦ hsingle j
      _ = _ := by norm_num [O, Finset.sum_const, nsmul_eq_mul]; ring)

end ManyBody.BondInteraction
