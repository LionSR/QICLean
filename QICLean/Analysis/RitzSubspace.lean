/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyPerturbation
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Order.Interval.Finset.Fin

/-!
# Low Rayleigh–Ritz subspaces

An actual symmetric operator determines its ordered orthonormal eigenbasis.
A trial subspace of dimension r with a uniform energy bound controls the
r smallest eigenvalues, hence the whole span of their eigenvectors.
This is the finite-dimensional variational step in ALVV,
arXiv:1602.08828v2, the final compression in `fig:algo1`, lines 1620–1643,
and the last step of `t:alg1`, lines 1811–1817. The trial-space energy
bound is an explicit hypothesis of this auxiliary result.
-/

open scoped InnerProductSpace

private theorem finrank_span_basis_image {n : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] (b : Module.Basis (Fin n) ℂ E) (A : Set (Fin n)) :
    Module.finrank ℂ (Submodule.span ℂ (b '' A)) = Nat.card A := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : Fintype (b '' A) := ((Set.toFinite A).image b).fintype
  rw [Nat.card_eq_fintype_card]
  rw [finrank_span_set_eq_card (b.linearIndepOn A).id_image]
  simpa only [Set.toFinset_card] using
    (Fintype.card_congr (Equiv.Set.image b A b.injective)).symm

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E} {n : ℕ}

/-- A trial-space quadratic-form bound controls the corresponding ordered
low eigenvalue of the actual symmetric operator. This is the min–max step
supporting ALVV, arXiv:1602.08828v2, `fig:algo1`, lines 1620–1643, and
`t:alg1`, lines 1811–1817; no extracted space is assumed. -/
theorem eigenvalue_le_of_trial_subspace (hH : H.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (V : Submodule ℂ E) (e : ℝ)
    (hV : ∀ x ∈ V, (inner ℂ x (H x)).re ≤ e * ‖x‖ ^ 2)
    (i : Fin n) (hi : n - i.val ≤ Module.finrank ℂ V) :
    hH.eigenvalues hn i ≤ e := by
  classical
  let b := hH.eigenvectorBasis hn
  let P := Submodule.span ℂ (b '' Set.Iic i)
  have hdimP : Module.finrank ℂ P = i.val + 1 := by
    change Module.finrank ℂ (Submodule.span ℂ (b.toBasis '' Set.Iic i)) = i.val + 1
    rw [finrank_span_basis_image]
    simp
  have hneg (j : Fin n) : (-H) (b j) = ((-hH.eigenvalues hn j : ℝ) : ℂ) • b j := by
    have heigen : H (b j) = (hH.eigenvalues hn j : ℂ) • b j :=
      hH.apply_eigenvectorBasis hn j
    change -(H (b j)) = _
    rw [heigen, Complex.ofReal_neg, neg_smul]
  have hP : P ≤ Submodule.spectralSpanLE b (fun j ↦ -hH.eigenvalues hn j)
      (-hH.eigenvalues hn i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    apply Submodule.subset_span
    exact ⟨j, neg_le_neg (hH.eigenvalues_antitone hn hj), rfl⟩
  have hPlower (x : E) (hx : x ∈ P) :
      hH.eigenvalues hn i * ‖x‖ ^ 2 ≤ (inner ℂ x (H x)).re := by
    have hbound := Submodule.re_inner_apply_le_of_mem_spectralSpanLE b
      (fun j ↦ -hH.eigenvalues hn j) (-H) hneg (-hH.eigenvalues hn i) (hP hx)
    simpa only [LinearMap.neg_apply, inner_neg_right, Complex.neg_re, neg_mul,
      neg_le_neg_iff] using hbound
  have hnotdisjoint : ¬ Disjoint P V := by
    intro hdisjoint
    have hdimension := Submodule.finrank_add_finrank_le_of_disjoint hdisjoint
    rw [hdimP, hn] at hdimension
    omega
  have hbot : ⊥ < P ⊓ V := by
    apply bot_lt_iff_ne_bot.mpr
    intro heq
    exact hnotdisjoint (disjoint_iff.mpr heq)
  obtain ⟨x, hx⟩ := Submodule.nonzero_mem_of_bot_lt hbot
  have hxE : (x : E) ≠ 0 := by
    intro heq
    exact hx (Subtype.ext heq)
  have henergy := (hPlower x x.property.1).trans (hV x x.property.2)
  exact _root_.le_of_mul_le_mul_right henergy (sq_pos_of_pos (norm_pos_iff.mpr hxE))

/-- The span of the actual r smallest ordered eigenvectors, counting
multiplicity. The definition retains the whole space when r exceeds its
dimension. This is the spectral selection in ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, lines 1620–1643. -/
noncomputable def ritzSubspace (hH : H.IsSymmetric) (r : ℕ) : Submodule ℂ E :=
  let n := Module.finrank ℂ E
  let b := hH.eigenvectorBasis (n := n) rfl
  Submodule.span ℂ (b '' {j : Fin n | n - r ≤ j.val})

/-- Selecting r actual lowest eigenvectors has dimension r whenever that
many vectors are available. This is the dimension assertion for the
spectral selection in ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1641–1643; repeated eigenvalues and r=0 are included. -/
theorem finrank_ritzSubspace (hH : H.IsSymmetric) (r : ℕ)
    (hr : r ≤ Module.finrank ℂ E) :
    Module.finrank ℂ (hH.ritzSubspace r) = r := by
  classical
  let n := Module.finrank ℂ E
  let b := hH.eigenvectorBasis (n := n) rfl
  change Module.finrank ℂ
    (Submodule.span ℂ (b.toBasis '' {j : Fin n | n - r ≤ j.val})) = r
  rw [finrank_span_basis_image]
  by_cases hr0 : r = 0
  · subst r
    have hset : {j : Fin n | n ≤ j.val} = ∅ := by
      ext j
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    simp [hset]
  · let i : Fin n := ⟨n - r, by dsimp only [n]; omega⟩
    have hset : {j : Fin n | n - r ≤ j.val} = Set.Ici i := by
      ext j
      rfl
    rw [hset]
    simp [i, n, Nat.sub_sub_self hr]

/-- The span of the actual dim(V) lowest eigenvectors has no larger
quadratic form than a uniform trial-space bound. The conclusion concerns
every vector in the selected span, not only its eigenbasis. This is the
variational selection in ALVV, arXiv:1602.08828v2, Figure `fig:algo1`,
lines 1641–1643, and `t:alg1`, lines 1811–1817. -/
theorem re_inner_apply_le_of_mem_ritzSubspace (hH : H.IsSymmetric)
    (V : Submodule ℂ E) (e : ℝ)
    (hV : ∀ x ∈ V, (inner ℂ x (H x)).re ≤ e * ‖x‖ ^ 2)
    {x : E} (hx : x ∈ hH.ritzSubspace (Module.finrank ℂ V)) :
    (inner ℂ x (H x)).re ≤ e * ‖x‖ ^ 2 := by
  classical
  let n := Module.finrank ℂ E
  let r := Module.finrank ℂ V
  let b := hH.eigenvectorBasis (n := n) rfl
  have hr : r ≤ n := Submodule.finrank_le V
  have hR : hH.ritzSubspace r ≤
      Submodule.spectralSpanLE b (hH.eigenvalues (n := n) rfl) e := by
    change Submodule.span ℂ (b '' {j : Fin n | n - r ≤ j.val}) ≤ _
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    change n - r ≤ j.val at hj
    have hr0 : 0 < r := by omega
    let i : Fin n := ⟨n - r, by omega⟩
    have heigenvalue : hH.eigenvalues (n := n) rfl i ≤ e :=
      hH.eigenvalue_le_of_trial_subspace rfl V e hV i (by
        change n - (n - r) ≤ r
        omega)
    apply Submodule.subset_span
    exact ⟨j, (hH.eigenvalues_antitone rfl (show i ≤ j from hj)).trans heigenvalue, rfl⟩
  have hb (j : Fin n) : H (b j) = (hH.eigenvalues (n := n) rfl j : ℂ) • b j :=
    hH.apply_eigenvectorBasis rfl j
  exact Submodule.re_inner_apply_le_of_mem_spectralSpanLE b
    (hH.eigenvalues (n := n) rfl) H hb e (hR hx)

end LinearMap.IsSymmetric
