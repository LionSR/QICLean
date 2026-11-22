/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Exponential.HermitianProductFormula
import QICLean.ManyBody.Dynamics.HeisenbergEvolution
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Sites.ProductForm

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
* `ManyBody.Interaction.exists_productForm_lie_card_index`,
  `ManyBody.Interaction.exists_productForm_lie_card_index_eq`,
  `ManyBody.Interaction.hasProductForm_lie`: for every complex `z`, every order and every number
  of steps, `lie Φ.term order z n` has a matrix product form with `|X j|^{2 n c_j}` index values
  at `j` (Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1077). The supported factors
  and the index counts are moved from TNLean (`e113e005`) `TNLean/Lattice/TrotterIndexCount.lean`
  and `ProductForm.lean`.
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

/-! ### The matrix product form of the product formula -/

section ProductForm

variable {near : V → V → Prop}

omit [Fintype κ] in
/-- **The Trotter product in matrix product form.** Let every term `h_k` act on a region
near a centre `c k`. For every order of the indices, with repetitions allowed, every complex
`z` and every number of steps `n`, the product formula `lie Φ.term order z n` has a product
form whose index set at a site `j` has `|X j|^{2 n c_j}` values, where `c_j` counts the
entries of `order` whose support contains `j`. Real and imaginary time are the cases
`z = -it` and `z = -β`. Hastings, arXiv:cond-mat/0508554v3, eq. `mpf`, lines 1024–1077. -/
theorem exists_productForm_lie_card_index (Φ : Interaction X T) (c : κ → V)
    (hc : ∀ k j, j ∈ T k → near (c k) j) (order : List κ) (z : ℂ) (n : ℕ) :
    ∃ P : ProductForm X near (lie Φ.term order z n), ∀ j,
      Fintype.card (P.Index j) =
        Fintype.card (X j) ^ (2 * n * order.countP (fun k ↦ decide (j ∈ T k))) := by
  rw [lie, step, ← List.map_reverse]
  obtain ⟨P, hP⟩ := exists_productForm_list_prod_card_index
    (fun k ↦ NormedSpace.exp ((z / n) • Φ.term k)) T c hc
    (fun k ↦ exp_mem_supportedOperators (SMulMemClass.smul_mem _ (Φ.mem k))) order.reverse
  refine ⟨P.pow n, fun j ↦ ?_⟩
  rw [ProductForm.card_index_pow, hP, List.countP_reverse, ← pow_mul]
  ring_nf

/-- For an order listing every index once, the index set of the Trotter product at a site `j`
has `|X j|^{2 n c_j}` values, with `c_j` the number of terms whose support contains `j`.
Hastings, arXiv:cond-mat/0508554v3, lines 1069–1077. -/
theorem exists_productForm_lie_card_index_eq (Φ : Interaction X T) (c : κ → V)
    (hc : ∀ k j, j ∈ T k → near (c k) j) {order : List κ} (horder : order.Nodup)
    (hall : ∀ k, k ∈ order) (z : ℂ) (n : ℕ) :
    ∃ P : ProductForm X near (lie Φ.term order z n), ∀ j,
      Fintype.card (P.Index j) =
        Fintype.card (X j) ^ (2 * n * (Finset.univ.filter fun k ↦ j ∈ T k).card) := by
  classical
  obtain ⟨P, hP⟩ := exists_productForm_lie_card_index Φ c hc order z n
  refine ⟨P, fun j ↦ ?_⟩
  have huniv : order.toFinset = Finset.univ :=
    Finset.eq_univ_of_forall fun k ↦ List.mem_toFinset.mpr (hall k)
  rw [hP, ← horder.card_eq_countP (P := fun k ↦ j ∈ T k), huniv]

omit [Fintype κ] in
/-- The Trotter product of an interaction whose terms act near their centres has a matrix
product form with those coefficient neighbourhoods.
Hastings, arXiv:cond-mat/0508554v3, lines 1053–1077. -/
theorem hasProductForm_lie (Φ : Interaction X T) (c : κ → V)
    (hc : ∀ k j, j ∈ T k → near (c k) j) (order : List κ) (z : ℂ) (n : ℕ) :
    HasProductForm X near (lie Φ.term order z n) :=
  ⟨(exists_productForm_lie_card_index Φ c hc order z n).choose⟩

end ProductForm

end Interaction

end ManyBody
