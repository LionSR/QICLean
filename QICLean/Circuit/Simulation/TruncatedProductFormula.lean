/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.ProductFormula
import QICLean.ManyBody.Dynamics.TruncatedEvolution

/-!
# Spatial truncation error of Trotter circuits

The Hamiltonian of `localFamilyInside` is the sum of the placed interaction terms
whose supports lie in the simulated region. The finite spatial truncation estimate
therefore adds to the product-formula error of that family. In the first form of the circuit
error bound the total norm of the deleted terms is explicit; in the boundary form only the
terms crossing the boundary of the simulated region enter, and their total norm is at most the
per-site budget times the number of sites of the region lying in a crossing term
(`ManyBody.Interaction.sum_norm_term_crossing_le`).
-/

open Matrix ManyBody ProductFormula SimpleGraph
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit

variable {S κ : Type} [Fintype S] [DecidableEq S] [Fintype κ] [DecidableEq κ]
  {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  {T : κ → Finset S}
  (h : (k : κ) → Matrix (RegionConfig X (T k)) (RegionConfig X (T k)) ℂ)

omit [DecidableEq κ] [∀ s, Fintype (X s)] in
/-- The Hamiltonian of the restricted local family is exactly the sum of the kept
placed terms. This identity does not require Hermitian terms. -/
theorem sum_place_localFamilyInside (L : Finset S) :
    (∑ k, place (T k) (localFamilyInside h L k)) =
      ∑ k ∈ Finset.univ.filter (fun k ↦ T k ⊆ L), place (T k) (h k) := by
  classical
  simp only [Finset.sum_filter, localFamilyInside]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

variable {h} (hh : ∀ k, (h k).IsHermitian)
  (G : SimpleGraph S) (r : ℕ)
  (hDiam : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, G.edist x y ≤ r)
  (v : ℕ) (hCard : ∀ k, (T k).card ≤ v)
  (b : ℝ)
  (hBudget : ∀ x, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ T k), ‖place (T k) (h k)‖ ≤ b)
  {R L : Finset S} {A : Matrix (Config X) (Config X) ℂ}
  (hA : A ∈ supportedOperators X R) (μ : ℝ) (hμ : 0 ≤ μ) (d : ℕ)
  (hd : ∀ x ∈ R, ∀ z ∉ L, (d : ℕ∞) + r ≤ G.edist x z)

include hh hDiam hCard hBudget hA hμ hd

omit [DecidableEq κ] in
/-- The exact evolution of the restricted local family differs from the full evolution
by the finite spatial truncation bound, with the total norm of deleted placed terms. -/
theorem norm_heisenbergEvolution_localFamilyInside_sub_le_graphDistance (t : ℝ) :
    ‖heisenbergEvolution (∑ k, place (T k) (localFamilyInside h L k)) t A -
      heisenbergEvolution (∑ k, place (T k) (h k)) t A‖ ≤
      (4 * (R.card : ℝ) * ‖A‖ *
        (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ T k ⊆ L), ‖place (T k) (h k)‖) *
        Real.exp ((4 * v * |b| * Real.exp (2 * μ * r)) * |t| - μ * d)) * |t| := by
  let Φ : Interaction X T := ⟨fun k ↦ place (T k) (h k),
    fun k ↦ place_mem_supportedOperators (h k)⟩
  rw [sum_place_localFamilyInside, norm_sub_rev]
  exact norm_heisenbergEvolution_sub_spatial_truncation_le G Φ
    (fun k ↦ isHermitian_place (hh k)) r hDiam v hCard b hBudget L R hA μ hμ d hd t

variable {m : ℕ} (c : (overlapGraph T).Coloring (Fin m))

/-- The Trotter circuit of the restricted family approximates full Hamiltonian evolution
by the sum of its product-formula error and the finite spatial truncation error. -/
theorem norm_dual_trotterCircuit_localFamilyInside_sub_le_graphDistance
    (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖(trotterCircuit c (localFamilyInside h L) t n).dual KrausGate.ev A -
      heisenbergEvolution (∑ k, place (T k) (h k)) t A‖ ≤
      2 * ‖A‖ * (t ^ 2 / (2 * n) *
        commSum (fun k ↦ place (T k) (localFamilyInside h L k)) (colourOrder c)) +
      (4 * (R.card : ℝ) * ‖A‖ *
        (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ T k ⊆ L), ‖place (T k) (h k)‖) *
        Real.exp ((4 * v * |b| * Real.exp (2 * μ * r)) * |t| - μ * d)) * |t| := by
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (heisenbergEvolution (∑ k, place (T k) (localFamilyInside h L k)) t A) _).trans
    (add_le_add (norm_dual_trotterCircuit_sub_le c (isHermitian_localFamilyInside hh L) t hn A)
      (norm_heisenbergEvolution_localFamilyInside_sub_le_graphDistance
        hh G r hDiam v hCard b hBudget hA μ hμ d hd t))

/-- When the simulated region contains the circuit light cone, the full Trotter circuit
has the same local error bound in terms of the restricted family's commutator sum. -/
theorem norm_dual_trotterCircuit_sub_le_restrict_graphDistance
    (t : ℝ) {n : ℕ} (hn : 0 < n)
    (hRL : (Geometry.ofSupports T).neighbourhood^[n * m] R ⊆ L) :
    ‖(trotterCircuit c h t n).dual KrausGate.ev A -
      heisenbergEvolution (∑ k, place (T k) (h k)) t A‖ ≤
      2 * ‖A‖ * (t ^ 2 / (2 * n) *
        commSum (fun k ↦ place (T k) (localFamilyInside h L k)) (colourOrder c)) +
      (4 * (R.card : ℝ) * ‖A‖ *
        (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ T k ⊆ L), ‖place (T k) (h k)‖) *
        Real.exp ((4 * v * |b| * Real.exp (2 * μ * r)) * |t| - μ * d)) * |t| := by
  exact (norm_dual_trotterCircuit_sub_le_restrict c hh t hn hRL hA).trans
    (add_le_add_right (norm_heisenbergEvolution_localFamilyInside_sub_le_graphDistance
      hh G r hDiam v hCard b hBudget hA μ hμ d hd t) _)

/-- **Boundary form.** When the simulated region contains the circuit light cone, the full
Trotter circuit approximates the full Hamiltonian evolution up to the product-formula error of
the restricted family and a truncation error carried by the terms crossing the boundary of the
simulated region only. -/
theorem norm_dual_trotterCircuit_sub_le_restrict_boundary
    (t : ℝ) {n : ℕ} (hn : 0 < n)
    (hRL : (Geometry.ofSupports T).neighbourhood^[n * m] R ⊆ L) :
    ‖(trotterCircuit c h t n).dual KrausGate.ev A -
      heisenbergEvolution (∑ k, place (T k) (h k)) t A‖ ≤
      2 * ‖A‖ * (t ^ 2 / (2 * n) *
        commSum (fun k ↦ place (T k) (localFamilyInside h L k)) (colourOrder c)) +
      (4 * (R.card : ℝ) * ‖A‖ *
        (∑ k ∈ Finset.univ.filter (fun k ↦ ¬ T k ⊆ L ∧ ¬ Disjoint (T k) L),
          ‖place (T k) (h k)‖) *
        Real.exp ((4 * v * |b| * Real.exp (2 * μ * r)) * |t| - μ * d)) * |t| := by
  have hR : R ⊆ L := by
    refine subset_trans ?_ hRL
    induction n * m with
    | zero => exact subset_rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans (Geometry.subset_neighbourhood _ _)
  let Φ : Interaction X T := ⟨fun k ↦ place (T k) (h k),
    fun k ↦ place_mem_supportedOperators (h k)⟩
  refine (norm_dual_trotterCircuit_sub_le_restrict c hh t hn hRL hA).trans
    (add_le_add_right ?_ _)
  rw [sum_place_localFamilyInside, norm_sub_rev]
  exact norm_heisenbergEvolution_sub_spatial_truncation_le_boundary G Φ
    (fun k ↦ isHermitian_place (hh k)) r hDiam v hCard b hBudget L R hR hA μ hμ d hd t

end QuantumCircuit
