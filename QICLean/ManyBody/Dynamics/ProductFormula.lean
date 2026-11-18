/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.HermitianProductFormula
import QICLean.ManyBody.Dynamics.HeisenbergEvolution
import QICLean.ManyBody.Dynamics.Interaction

/-!
# Product formulas for an interaction

For an interaction `Φ` with Hermitian terms `h_k` and an order `order` listing every index once,
the product formulas `ProductFormula.lieEvolution Φ.term order t n` and
`ProductFormula.strangEvolution Φ.term order t n` approximate the evolution
`e^{-itH} = Matrix.hermitianUnitaryPath H (-t)` under the Hamiltonian `H = ∑_k h_k`:

* `‖U_1 - e^{-itH}‖ ≤ t²/(2n) ∑_{i<j} ‖[h_i, h_j]‖`;
* `‖U_2 - e^{-itH}‖ ≤ |t|³/(2n²) ∑_{i<j} ‖[h_i, h_j]‖ ∑_k ‖h_k‖`,

the sums running over the positions of `order`. In the Heisenberg picture the error at most
doubles, times `‖A‖`.

## Main results

* `ManyBody.Interaction.norm_lieEvolution_sub_hamiltonian_le`,
  `ManyBody.Interaction.norm_strangEvolution_sub_hamiltonian_le`.
* `ManyBody.Interaction.norm_lieEvolution_heisenberg_sub_le`,
  `ManyBody.Interaction.norm_strangEvolution_heisenberg_sub_le`.
-/

open Matrix ProductFormula
open scoped Matrix.Norms.L2Operator

namespace ManyBody

namespace Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} {T : κ → Finset V}

/-! ### Error bounds against the Hamiltonian -/

variable [Fintype κ] {Φ : Interaction X T}

/-- **First-order Trotter error.** For Hermitian terms and an order listing every index once,
`‖U_1 - e^{-itH}‖ ≤ t²/(2n) ∑_{i<j} ‖[h_i, h_j]‖`. -/
theorem norm_lieEvolution_sub_hamiltonian_le (hH : ∀ k, (Φ.term k).IsHermitian)
    {order : List κ} (ho : order.Perm Finset.univ.toList) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖lieEvolution Φ.term order t n - hermitianUnitaryPath Φ.hamiltonian (-t)‖ ≤
      t ^ 2 / (2 * n) * commSum Φ.term order := by
  rw [hamiltonian, ← gen_eq_sum _ ho]
  exact norm_lieEvolution_sub_le hH order t hn

/-- **Second-order Trotter error.** For Hermitian terms and an order listing every index once,
`‖U_2 - e^{-itH}‖ ≤ |t|³/(2n²) ∑_{i<j} ‖[h_i, h_j]‖ ∑_k ‖h_k‖`. -/
theorem norm_strangEvolution_sub_hamiltonian_le (hH : ∀ k, (Φ.term k).IsHermitian)
    {order : List κ} (ho : order.Perm Finset.univ.toList) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖strangEvolution Φ.term order t n - hermitianUnitaryPath Φ.hamiltonian (-t)‖ ≤
      |t| ^ 3 / (2 * n ^ 2) * commSum Φ.term order * normSum Φ.term order := by
  rw [hamiltonian, ← gen_eq_sum _ ho]
  exact norm_strangEvolution_sub_le hH order t hn

/-- **First-order Trotter error, Heisenberg picture.**
`‖U_1† A U_1 - e^{itH} A e^{-itH}‖ ≤ 2 ‖A‖ t²/(2n) ∑_{i<j} ‖[h_i, h_j]‖`. -/
theorem norm_lieEvolution_heisenberg_sub_le (hH : ∀ k, (Φ.term k).IsHermitian)
    {order : List κ} (ho : order.Perm Finset.univ.toList) (t : ℝ) {n : ℕ} (hn : 0 < n)
    (A : Matrix (Config X) (Config X) ℂ) :
    ‖(lieEvolution Φ.term order t n)ᴴ * A * lieEvolution Φ.term order t n -
        heisenbergEvolution Φ.hamiltonian t A‖ ≤
      2 * ‖A‖ * (t ^ 2 / (2 * n) * commSum Φ.term order) := by
  rw [heisenbergEvolution, hamiltonian, ← gen_eq_sum _ ho]
  exact norm_lieEvolution_conj_sub_le hH order t hn A

/-- **Second-order Trotter error, Heisenberg picture.**
`‖U_2† A U_2 - e^{itH} A e^{-itH}‖ ≤ 2 ‖A‖ |t|³/(2n²) ∑_{i<j} ‖[h_i, h_j]‖ ∑_k ‖h_k‖`. -/
theorem norm_strangEvolution_heisenberg_sub_le (hH : ∀ k, (Φ.term k).IsHermitian)
    {order : List κ} (ho : order.Perm Finset.univ.toList) (t : ℝ) {n : ℕ} (hn : 0 < n)
    (A : Matrix (Config X) (Config X) ℂ) :
    ‖(strangEvolution Φ.term order t n)ᴴ * A * strangEvolution Φ.term order t n -
        heisenbergEvolution Φ.hamiltonian t A‖ ≤
      2 * ‖A‖ * (|t| ^ 3 / (2 * n ^ 2) * commSum Φ.term order * normSum Φ.term order) := by
  rw [heisenbergEvolution, hamiltonian, ← gen_eq_sum _ ho]
  exact norm_strangEvolution_conj_sub_le hH order t hn A

end Interaction

end ManyBody
