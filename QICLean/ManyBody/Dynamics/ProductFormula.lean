/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProductFormula
import QICLean.Analysis.SpectralFilter.MatrixFilter
import QICLean.ManyBody.Dynamics.HeisenbergEvolution
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Sites.Placement

/-!
# Product formulas for an interaction

For an interaction `Φ` with Hermitian terms `h_k` and an ordering `order` of its indices, the
first-order (Lie–Trotter) propagator with `n` steps is
`(∏_{k ∈ order} e^{-i (t/n) h_k})^n`, the head of `order` applied first, and the second-order
(Strang) propagator repeats the symmetric step. Both approximate the propagator
`e^{-itH} = Matrix.hermitianUnitaryPath H (-t)` of the Hamiltonian `H = ∑_k h_k`. For Hermitian
terms the exponentials are unitary, so the errors of `ProductFormula` hold with `M = 1`:

* `‖U_1 - e^{-itH}‖ ≤ t²/(2n) ∑_{i<j} ‖[h_i, h_j]‖`;
* `‖U_2 - e^{-itH}‖ ≤ |t|³/(2n²) ∑_{i<j} ‖[h_i, h_j]‖ ∑_k ‖h_k‖`,

the sums running over the positions of `order`. In the Heisenberg picture the error at most
doubles, times `‖A‖`.

Each factor `e^{c h_k}` is the placement of the exponential of a matrix on the support of `h_k`
(`ManyBody.Interaction.exp_smul_term_eq_place`).

## Main definitions

* `ManyBody.Interaction.localTerm` — a matrix on the support whose placement is the term.
* `ManyBody.Interaction.lieTrotter`, `ManyBody.Interaction.strangTrotter` — the propagators.

## Main results

* `ManyBody.Interaction.lieTrotter_mem_unitary`, `ManyBody.Interaction.strangTrotter_mem_unitary`.
* `ManyBody.Interaction.norm_lieTrotter_sub_le`, `ManyBody.Interaction.norm_strangTrotter_sub_le`.
* `ManyBody.Interaction.norm_lieTrotter_heisenberg_sub_le`,
  `ManyBody.Interaction.norm_strangTrotter_heisenberg_sub_le`.
-/

open Matrix ProductFormula SpectralFilter
open scoped Matrix.Norms.L2Operator

namespace ManyBody

section Unitary

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A unitary matrix has operator norm at most one. -/
private theorem norm_le_one_of_mem_unitary {U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ)) :
    ‖U‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial (Matrix n n ℂ) with hE | hE
  · rw [Subsingleton.elim U 0, norm_zero]
    exact zero_le_one
  · exact (CStarRing.norm_of_mem_unitary hU).le

/-- Conjugating by two unitaries: `‖U† A U - W† A W‖ ≤ 2 ‖A‖ ‖U - W‖`. -/
private theorem norm_conj_sub_conj_le {U W : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    (hW : W ∈ unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    ‖Uᴴ * A * U - Wᴴ * A * W‖ ≤ 2 * ‖A‖ * ‖U - W‖ := by
  have hsplit : Uᴴ * A * U - Wᴴ * A * W = Uᴴ * A * (U - W) + (U - W)ᴴ * A * W := by
    rw [conjTranspose_sub]
    noncomm_ring
  have hU1 : ‖Uᴴ‖ ≤ 1 := (l2_opNorm_conjTranspose U).trans_le (norm_le_one_of_mem_unitary hU)
  have hW1 := norm_le_one_of_mem_unitary hW
  rw [hsplit]
  calc ‖Uᴴ * A * (U - W) + (U - W)ᴴ * A * W‖
      ≤ ‖Uᴴ‖ * ‖A‖ * ‖U - W‖ + ‖(U - W)ᴴ‖ * ‖A‖ * ‖W‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)))
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))))
    _ ≤ 1 * ‖A‖ * ‖U - W‖ + ‖U - W‖ * ‖A‖ * 1 := by
        rw [l2_opNorm_conjTranspose (U - W)]
        exact add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hU1
          (norm_nonneg _)) (norm_nonneg _)) (mul_le_mul_of_nonneg_left hW1 (by positivity))
    _ = 2 * ‖A‖ * ‖U - W‖ := by ring

end Unitary

namespace Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} {T : κ → Finset V}

/-! ### Local terms -/

/-- A matrix on the configurations of the support `T k` whose placement is the term `k` (chosen;
unique when the configurations of the system are nonempty). -/
noncomputable def localTerm (Φ : Interaction X T) (k : κ) :
    Matrix (RegionConfig X (T k)) (RegionConfig X (T k)) ℂ :=
  Classical.choose (exists_eq_place_of_mem_supportedOperators (Φ.mem k))

theorem place_localTerm (Φ : Interaction X T) (k : κ) :
    place (T k) (Φ.localTerm k) = Φ.term k :=
  (Classical.choose_spec (exists_eq_place_of_mem_supportedOperators (Φ.mem k))).symm

/-- The exponential of a multiple of a term is placed on its support. -/
theorem exp_smul_term_eq_place (Φ : Interaction X T) (k : κ) (c : ℂ) :
    NormedSpace.exp (c • Φ.term k) = place (T k) (NormedSpace.exp (c • Φ.localTerm k)) := by
  rw [place_exp, place_smul, place_localTerm]

/-! ### The propagators -/

/-- The first-order (Lie–Trotter) propagator `(∏_{k ∈ order} e^{-i (t/n) h_k})^n`, the head of
`order` applied first. It approximates `Matrix.hermitianUnitaryPath Φ.hamiltonian (-t)`. -/
noncomputable def lieTrotter (Φ : Interaction X T) (order : List κ) (t : ℝ) (n : ℕ) :
    Matrix (Config X) (Config X) ℂ :=
  lie (fun k ↦ Complex.I • Φ.term k) order ((-t : ℝ) : ℂ) n

/-- The second-order (Strang) propagator: `n` symmetric steps, each forward through `order` for
the time `t/(2n)` and back. -/
noncomputable def strangTrotter (Φ : Interaction X T) (order : List κ) (t : ℝ) (n : ℕ) :
    Matrix (Config X) (Config X) ℂ :=
  strang (fun k ↦ Complex.I • Φ.term k) order ((-t : ℝ) : ℂ) n

private theorem cast_neg_div (t : ℝ) (n : ℕ) :
    ((-t : ℝ) : ℂ) / n = ((-t / n : ℝ) : ℂ) := by
  push_cast
  ring

/-- The first-order propagator is a power of an ordered product of the unitary paths of the
terms. -/
theorem lieTrotter_eq (Φ : Interaction X T) (order : List κ) (t : ℝ) (n : ℕ) :
    Φ.lieTrotter order t n =
      (order.map fun k ↦ hermitianUnitaryPath (Φ.term k) (-t / n)).reverse.prod ^ n := by
  simp only [lieTrotter, lie, step, cast_neg_div]
  rfl

variable {Φ : Interaction X T}

theorem isHermitian_gen (hH : ∀ k, (Φ.term k).IsHermitian) :
    ∀ l : List κ, (gen Φ.term l).IsHermitian
  | [] => isHermitian_zero
  | a :: l => by
    rw [gen_cons]
    exact (hH a).add (isHermitian_gen hH l)

private theorem step_mem_unitary (hH : ∀ k, (Φ.term k).IsHermitian) (l : List κ) (r : ℝ) :
    step (fun k ↦ Complex.I • Φ.term k) l (r : ℂ) ∈ unitary (Matrix (Config X) (Config X) ℂ) := by
  induction l with
  | nil => exact one_mem _
  | cons a l ih =>
    rw [step_cons]
    exact mul_mem ih (hermitianUnitaryPath_mem_unitary (hH a) r)

theorem lieTrotter_mem_unitary (hH : ∀ k, (Φ.term k).IsHermitian) (order : List κ) (t : ℝ)
    (n : ℕ) : Φ.lieTrotter order t n ∈ unitary (Matrix (Config X) (Config X) ℂ) := by
  rw [lieTrotter, lie, cast_neg_div]
  exact pow_mem (step_mem_unitary hH order _) n

theorem strangTrotter_mem_unitary (hH : ∀ k, (Φ.term k).IsHermitian) (order : List κ) (t : ℝ)
    (n : ℕ) : Φ.strangTrotter order t n ∈ unitary (Matrix (Config X) (Config X) ℂ) := by
  have hz : ((-t : ℝ) : ℂ) / n / 2 = ((-t / n / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [strangTrotter, strang, symmStep, hz]
  exact pow_mem (mul_mem (step_mem_unitary hH _ _) (step_mem_unitary hH _ _)) n

/-- For Hermitian terms and a real time the exponentials of the partial sums are unitary, so
the bound hypothesis of the product formulas holds with `M = 1`. -/
private theorem expBound_one (hH : ∀ k, (Φ.term k).IsHermitian) (order : List κ) (r : ℝ) :
    ExpBound (fun k ↦ Complex.I • Φ.term k) order (r : ℂ) 1 := by
  intro l _ s _
  have e : s • ((r : ℂ) • (Complex.I • gen Φ.term l)) =
      ((s * r : ℝ) : ℂ) • (Complex.I • gen Φ.term l) := by
    rw [← Complex.coe_smul s, smul_smul, Complex.ofReal_mul]
  rw [gen_smul, e]
  exact norm_le_one_of_mem_unitary (hermitianUnitaryPath_mem_unitary (isHermitian_gen hH l) _)

/-! ### Error bounds -/

/-- **First-order Trotter error.** For Hermitian terms and an ordering of all indices,
`‖U_1 - e^{-itH}‖ ≤ t²/(2n) ∑_{i<j} ‖[h_i, h_j]‖`. -/
theorem norm_lieTrotter_sub_le [Fintype κ] (hH : ∀ k, (Φ.term k).IsHermitian)
    {order : List κ} (ho : order.Perm Finset.univ.toList) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Φ.lieTrotter order t n - hermitianUnitaryPath Φ.hamiltonian (-t)‖ ≤
      t ^ 2 / (2 * n) * commSum Φ.term order := by
  have hM := expBound_one hH order (-t / n)
  rw [← cast_neg_div] at hM
  have h := norm_lie_sub_exp_le _ hn hM le_rfl
  simp only [one_pow, commSum_smul, Complex.norm_I, one_mul, gen_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_neg, sq_abs] at h
  rw [lieTrotter, hamiltonian, ← gen_eq_sum _ ho]
  exact h.trans_eq (by ring)

/-- **Second-order Trotter error.** For Hermitian terms and an ordering of all indices,
`‖U_2 - e^{-itH}‖ ≤ |t|³/(2n²) ∑_{i<j} ‖[h_i, h_j]‖ ∑_k ‖h_k‖`. -/
theorem norm_strangTrotter_sub_le [Fintype κ] (hH : ∀ k, (Φ.term k).IsHermitian)
    {order : List κ} (ho : order.Perm Finset.univ.toList) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Φ.strangTrotter order t n - hermitianUnitaryPath Φ.hamiltonian (-t)‖ ≤
      |t| ^ 3 / (2 * n ^ 2) * commSum Φ.term order * normSum Φ.term order := by
  have hM := expBound_one hH order (-t / n)
  rw [← cast_neg_div] at hM
  have h := norm_strang_sub_exp_le _ hn hM le_rfl
  simp only [one_pow, commSum_smul, normSum_smul, Complex.norm_I, one_mul, gen_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_neg] at h
  rw [strangTrotter, hamiltonian, ← gen_eq_sum _ ho]
  exact h.trans_eq (by ring)

private theorem heisenbergEvolution_eq_conj [Fintype κ] (hH : ∀ k, (Φ.term k).IsHermitian)
    (t : ℝ) (A : Matrix (Config X) (Config X) ℂ) :
    heisenbergEvolution Φ.hamiltonian t A =
      (hermitianUnitaryPath Φ.hamiltonian (-t))ᴴ * A * hermitianUnitaryPath Φ.hamiltonian (-t) := by
  rw [hermitianUnitaryPath_conjTranspose (isHermitian_hamiltonian hH), neg_neg]
  rfl

/-- **First-order Trotter error, Heisenberg picture.**
`‖U_1† A U_1 - e^{itH} A e^{-itH}‖ ≤ 2 ‖A‖ t²/(2n) ∑_{i<j} ‖[h_i, h_j]‖`. -/
theorem norm_lieTrotter_heisenberg_sub_le [Fintype κ] (hH : ∀ k, (Φ.term k).IsHermitian)
    {order : List κ} (ho : order.Perm Finset.univ.toList) (t : ℝ) {n : ℕ} (hn : 0 < n)
    (A : Matrix (Config X) (Config X) ℂ) :
    ‖(Φ.lieTrotter order t n)ᴴ * A * Φ.lieTrotter order t n -
        heisenbergEvolution Φ.hamiltonian t A‖ ≤
      2 * ‖A‖ * (t ^ 2 / (2 * n) * commSum Φ.term order) := by
  rw [heisenbergEvolution_eq_conj hH]
  exact (norm_conj_sub_conj_le (lieTrotter_mem_unitary hH order t n)
    (hermitianUnitaryPath_mem_unitary (isHermitian_hamiltonian hH) (-t)) A).trans
    (mul_le_mul_of_nonneg_left (norm_lieTrotter_sub_le hH ho t hn) (by positivity))

/-- **Second-order Trotter error, Heisenberg picture.**
`‖U_2† A U_2 - e^{itH} A e^{-itH}‖ ≤ 2 ‖A‖ |t|³/(2n²) ∑_{i<j} ‖[h_i, h_j]‖ ∑_k ‖h_k‖`. -/
theorem norm_strangTrotter_heisenberg_sub_le [Fintype κ] (hH : ∀ k, (Φ.term k).IsHermitian)
    {order : List κ} (ho : order.Perm Finset.univ.toList) (t : ℝ) {n : ℕ} (hn : 0 < n)
    (A : Matrix (Config X) (Config X) ℂ) :
    ‖(Φ.strangTrotter order t n)ᴴ * A * Φ.strangTrotter order t n -
        heisenbergEvolution Φ.hamiltonian t A‖ ≤
      2 * ‖A‖ * (|t| ^ 3 / (2 * n ^ 2) * commSum Φ.term order * normSum Φ.term order) := by
  rw [heisenbergEvolution_eq_conj hH]
  exact (norm_conj_sub_conj_le (strangTrotter_mem_unitary hH order t n)
    (hermitianUnitaryPath_mem_unitary (isHermitian_hamiltonian hH) (-t)) A).trans
    (mul_le_mul_of_nonneg_left (norm_strangTrotter_sub_le hH ho t hn) (by positivity))

end Interaction

end ManyBody
