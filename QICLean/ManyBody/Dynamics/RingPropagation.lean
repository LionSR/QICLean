/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.GraphPropagation
import QICLean.ManyBody.Sites.Lattice.RingDistance

/-!
# The Lieb–Robinson bound on the ring

Let `H = ∑_j h_j` on the ring of `N` sites, with Hermitian terms `h_j` supported on the bonds
`{j, j + 1}` and of operator norm at most one. For operators `A` and `B` supported on disjoint
nonempty sets `X` and `Y`, every `a ≥ 0` and every time `t`,
`‖[e^{itH} A e^{-itH}, B]‖ ≤ 2 ‖A‖ ‖B‖ |X| e^{-a d(X, Y)} (e^{8 e^a |t|} - 1)`, where `d(X, Y)` is
the distance of the two sets on the ring (`ManyBody.ringSupportDistance`). The constants do not
depend on `N` or on the dimension of the sites; distinct bonds are counted separately, also on a
ring of two sites.

This is the cycle-graph case of the graph estimate
`ManyBody.norm_heisenberg_commutator_le_graphDistance_of_disjoint`: two bonds of at most two
sites meet each site, each of diameter at most one, so the site budget
`∑_{j ∋ x} |T_j| ‖h_j‖ e^{a diam T_j}` is at most `4 e^a`, and the distance of the sets on the
ring is at most the cycle-graph distance of any two of their sites.

Moved from TNLean, `TNLean/MPS/Preparation/FiniteRingLiebRobinson.lean` at commit `49b78ed821`
(Apache-2.0). Changes: the theorem is renamed from
`MPSPreparation.norm_heisenberg_commutator_le_exp_abs_of_disjoint`; the support of the term
`h_j` is the bond `{j, j + 1}` in place of the cell of the ring geometry of circuits, which is
that bond; the sites carry any finite type in place of `Fin d`.

## Main results

* `ManyBody.norm_heisenberg_commutator_le_ringSupportDistance` — the Lieb–Robinson bound on the
  ring.

## References

* Hastings–Koma, arXiv:math-ph/0507008, Appendix A, Theorem A.2.
-/

namespace ManyBody

open NormedSpace Fin.CommRing
open scoped Matrix.Norms.L2Operator

variable {N : ℕ} [NeZero N]

/-- A bond `{j, j + 1}` has cycle-graph diameter at most one. -/
private theorem edist_le_one_of_mem_bond (j : Fin N) :
    ∀ x ∈ ({j, j + 1} : Finset (Fin N)), ∀ z ∈ ({j, j + 1} : Finset (Fin N)),
      (SimpleGraph.cycleGraph N).edist x z ≤ ((1 : ℕ) : ℕ∞) := by
  have hj : (SimpleGraph.cycleGraph N).edist j (j + 1) ≤ 1 := by
    by_cases hjj : j = j + 1
    · rw [← hjj, SimpleGraph.edist_self]
      exact zero_le_one
    · refine (SimpleGraph.edist_eq_one_iff_adj.mpr ?_).le
      refine SimpleGraph.cycleGraph_adj'.mpr (Or.inr ?_)
      have hN : 1 < N := by
        by_contra hN
        exact hjj (Subsingleton.elim (h := Fin.subsingleton_iff_le_one.mpr (by omega)) _ _)
      simp [Nat.mod_eq_of_lt hN]
  intro x hx z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hz
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
  · simp
  · simpa using hj
  · simpa [SimpleGraph.edist_comm] using hj
  · simp

/-- The site budget on the ring: at most two bonds of at most two sites meet a site, each of
norm at most one and of diameter one. -/
private theorem sum_bond_budget_le (k : Fin N → ℝ) (hk0 : ∀ j, 0 ≤ k j)
    (hk : ∀ j, k j ≤ 1) (a : ℝ) (x : Fin N) :
    ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ ({j, j + 1} : Finset (Fin N))),
        (({j, j + 1} : Finset (Fin N)).card : ℝ) * k j * Real.exp (a * ((1 : ℕ) : ℝ)) ≤
      4 * Real.exp a := by
  classical
  have hsub : Finset.univ.filter (fun j ↦ x ∈ ({j, j + 1} : Finset (Fin N))) ⊆ {x, x - 1} := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hj ⊢
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by ring)
  have hterm : ∀ j, (({j, j + 1} : Finset (Fin N)).card : ℝ) * k j *
      Real.exp (a * ((1 : ℕ) : ℝ)) ≤ 2 * Real.exp a := by
    intro j
    have hcard : (({j, j + 1} : Finset (Fin N)).card : ℝ) ≤ 2 := by
      exact_mod_cast Finset.card_le_two
    simp only [Nat.cast_one, mul_one]
    have := mul_le_mul hcard (hk j) (hk0 j) (by norm_num)
    nlinarith [Real.exp_pos a]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ ({j, j + 1} : Finset (Fin N))),
          2 * Real.exp a := Finset.sum_le_sum fun j _ ↦ hterm j
    _ = (Finset.univ.filter (fun j ↦ x ∈ ({j, j + 1} : Finset (Fin N)))).card *
          (2 * Real.exp a) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) * (2 * Real.exp a) := by
      gcongr
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_le_two
    _ = 4 * Real.exp a := by ring

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The Lieb–Robinson bound on the ring.** Let `h_j` be Hermitian, supported on the bond
`{j, j + 1}` and of operator norm at most one, and let `A`, `B` be supported on disjoint
nonempty sets `X`, `Y`. For every `a ≥ 0` and every time `t`,
`‖[e^{itH} A e^{-itH}, B]‖ ≤ 2 ‖A‖ ‖B‖ |X| e^{-a d(X, Y)} (e^{8 e^a |t|} - 1)` with
`H = ∑_j h_j`. Hastings–Koma, arXiv:math-ph/0507008, Appendix A, Theorem A.2, for the
nearest-neighbour interactions of the ring. -/
theorem norm_heisenberg_commutator_le_ringSupportDistance
    (h : Fin N → Matrix (Fin N → α) (Fin N → α) ℂ)
    (hHerm : ∀ j, (h j).IsHermitian)
    (hSupport : ∀ j, h j ∈ supportedOperators (fun _ ↦ α) {j, j + 1})
    (hNorm : ∀ j, ‖h j‖ ≤ 1)
    (A B : Matrix (Fin N → α) (Fin N → α) ℂ)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ supportedOperators (fun _ ↦ α) X)
    (hB : B ∈ supportedOperators (fun _ ↦ α) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ‖(exp (t • (Complex.I • ∑ j, h j)) * A *
        exp ((-t) • (Complex.I • ∑ j, h j))) * B -
      B * (exp (t • (Complex.I • ∑ j, h j)) * A *
        exp ((-t) • (Complex.I • ∑ j, h j)))‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card *
        Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
        (Real.exp ((8 * Real.exp a) * |t|) - 1) := by
  classical
  let Φ : Interaction (fun _ : Fin N ↦ α) (fun j : Fin N ↦ ({j, j + 1} : Finset _)) :=
    ⟨h, hSupport⟩
  have hBound := norm_heisenberg_commutator_le_graphDistance_of_disjoint
    (SimpleGraph.cycleGraph N) Φ hHerm (fun _ ↦ 1) (fun j ↦ edist_le_one_of_mem_bond j)
    a ha (4 * Real.exp a)
    (sum_bond_budget_le (fun j ↦ ‖h j‖) (fun j ↦ norm_nonneg _) hNorm a) X
    hA Y hB
    (Finset.disjoint_coe.mp hXY) (ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)
    (fun x hx y hy ↦ ringSupportDistance_le_edist _ _ hX hY hx hy) t
  refine hBound.trans_eq ?_
  rw [show 2 * (4 * Real.exp a) = 8 * Real.exp a by ring]
  ring_nf

end ManyBody
