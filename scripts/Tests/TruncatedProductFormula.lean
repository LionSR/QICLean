import QICLean.Circuit.Simulation.TruncatedProductFormula

/-! Kernel audit and boundary regressions for the finite circuit truncation estimates. -/
open Matrix ManyBody ProductFormula QuantumCircuit
open scoped Matrix.Norms.L2Operator

#print axioms QuantumCircuit.sum_place_localFamilyInside
#print axioms QuantumCircuit.norm_heisenbergEvolution_localFamilyInside_sub_le_graphDistance
#print axioms QuantumCircuit.norm_dual_trotterCircuit_localFamilyInside_sub_le_graphDistance
#print axioms QuantumCircuit.norm_dual_trotterCircuit_sub_le_restrict_graphDistance

section General

variable {S κ : Type} [Fintype S] [DecidableEq S] [Fintype κ] [DecidableEq κ]
  {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  {T : κ → Finset S}
  (h : (k : κ) → Matrix (RegionConfig X (T k)) (RegionConfig X (T k)) ℂ)

-- Empty simulation region keeps exactly the empty-support terms, not necessarily nothing.
omit [DecidableEq κ] [∀ s, Fintype (X s)] in
example : (∑ k, place (T k) (localFamilyInside h ∅ k)) =
    ∑ k ∈ Finset.univ.filter (fun k ↦ T k = ∅), place (T k) (h k) := by
  simpa using sum_place_localFamilyInside h ∅

omit [DecidableEq κ] [∀ s, Fintype (X s)] in
example (hne : ∀ k, (T k).Nonempty) :
    (∑ k, place (T k) (localFamilyInside h ∅ k)) = 0 := by
  rw [sum_place_localFamilyInside]
  simp [fun k ↦ (hne k).ne_empty]

variable {h} (hh : ∀ k, (h k).IsHermitian) (G : SimpleGraph S)
  (r : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, G.edist x y ≤ r)
  (v : ℕ) (hCard : ∀ k, (T k).card ≤ v) (b : ℝ)
  (hBudget : ∀ x, ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ T k), ‖place (T k) (h k)‖ ≤ b)
  {R L : Finset S} {A : Matrix (Config X) (Config X) ℂ}
  (hA : A ∈ supportedOperators X R) (μ : ℝ) (hμ : 0 ≤ μ) (d : ℕ)
  (hd : ∀ x ∈ R, ∀ z ∉ L, (d : ℕ∞) + r ≤ G.edist x z)
  {m : ℕ} (c : (overlapGraph T).Coloring (Fin m))

-- The restricted circuit at zero time is exactly the identity on A, for any n > 0.
include hh hDiam hCard hBudget hA hμ hd in
example {n : ℕ} (hn : 0 < n) :
    (trotterCircuit c (localFamilyInside h L) 0 n).dual KrausGate.ev A = A := by
  have hb := norm_dual_trotterCircuit_localFamilyInside_sub_le_graphDistance
    hh G r hDiam v hCard b hBudget hA μ hμ d hd c 0 hn
  have he : heisenbergEvolution (∑ k, place (T k) (h k)) 0 A = A := by
    simp [heisenbergEvolution, hermitianUnitaryPath]
  rw [he] at hb
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using hb) (norm_nonneg _)))

-- Full retention removes the entire truncation term; test both signs at one Trotter step.
include hh hDiam hCard hBudget hA in
example (t : ℝ) (ht : t = 1 ∨ t = -1) :
    ‖(trotterCircuit c h t 1).dual KrausGate.ev A -
      heisenbergEvolution (∑ k, place (T k) (h k)) t A‖ ≤
      ‖A‖ * commSum (fun k ↦ place (T k) (h k)) (colourOrder c) := by
  have hb := norm_dual_trotterCircuit_sub_le_restrict_graphDistance
    hh G r hDiam v hCard b hBudget hA 0 (by norm_num) 0
    (L := Finset.univ) (by simp) c t (n := 1) (by norm_num) (by simp)
  rcases ht with rfl | rfl <;>
    norm_num [localFamilyInside] at hb ⊢ <;> nlinarith

end General

namespace DeletedTermRegression

private abbrev X : Bool → Type := fun _ ↦ Bool
private abbrev T : Unit → Finset Bool := fun _ ↦ {true}

-- A genuine one-qubit projection, with eigenvalues 0 and 1, at either site.
private noncomputable def projection (s : Bool) :
    Matrix (RegionConfig X {s}) (RegionConfig X {s}) ℂ :=
  diagonal fun q ↦ if q ⟨s, by simp⟩ then 1 else 0

private theorem projection_hermitian (s : Bool) : (projection s).IsHermitian := by
  apply isHermitian_diagonal_iff.mpr
  intro q
  split_ifs <;> simp

private noncomputable def terms (_ : Unit) := projection true
private noncomputable def observable := place (X := X) {false} (projection false)
private noncomputable def deleted := place (X := X) {true} (projection true)

private theorem deleted_mass_pos :
    0 < ∑ k ∈ Finset.univ.filter (fun k ↦ ¬ T k ⊆ {false}), ‖place (T k) (terms k)‖ := by
  have hp : projection true ≠ 0 := by
    intro he
    have hentry := congrArg (fun M ↦ M (fun _ ↦ true) (fun _ ↦ true)) he
    simp [projection] at hentry
  simpa [T, terms, norm_place] using norm_pos_iff.mpr hp

private def colouring : (overlapGraph T).Coloring (Fin 1) :=
  SimpleGraph.Coloring.mk (fun _ ↦ 0) (by
    intro a b hab
    exact (hab.ne (Subsingleton.elim a b)).elim)

private theorem range_zero : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k,
    (⊥ : SimpleGraph Bool).edist x y ≤ (0 : ℕ) := by
  simp [T]

private theorem site_budget : ∀ x,
    ∑ k ∈ Finset.univ.filter (fun k ↦ x ∈ T k), ‖place (T k) (terms k)‖ ≤ ‖deleted‖ := by
  intro x
  cases x <;> simp [T, terms, deleted]

-- The sites are distinct components, so every finite distance bound is admissible.
private theorem exterior_distance (d : ℕ) : ∀ x ∈ ({false} : Finset Bool),
    ∀ z ∉ ({false} : Finset Bool), (d : ℕ∞) + (0 : ℕ) ≤ (⊥ : SimpleGraph Bool).edist x z := by
  intro x hx z hz
  simp only [Finset.mem_singleton] at hx hz
  subst x
  rw [SimpleGraph.edist_bot_of_ne (Ne.symm hz)]
  exact le_top

-- Negative time with an actually nonzero discarded mass, not full retention.
private theorem negative_time_nonzero_deleted :
    0 < ∑ k ∈ Finset.univ.filter (fun k ↦ ¬ T k ⊆ {false}), ‖place (T k) (terms k)‖ ∧
    ‖(trotterCircuit colouring (localFamilyInside terms {false}) (-1) 1).dual KrausGate.ev
        observable - heisenbergEvolution (∑ k, place (T k) (terms k)) (-1) observable‖ ≤
      4 * ‖observable‖ * ‖deleted‖ * Real.exp (4 * ‖deleted‖ - 1) := by
  refine ⟨deleted_mass_pos, ?_⟩
  have hb := norm_dual_trotterCircuit_localFamilyInside_sub_le_graphDistance
    (h := terms) (T := T) (X := X) (fun _ ↦ projection_hermitian true)
    (⊥ : SimpleGraph Bool) 0 range_zero 1
    (by simp) ‖deleted‖ site_budget
    (place_mem_supportedOperators (projection false)) 1 (by norm_num) 1
    (exterior_distance 1) colouring (-1) (n := 1) (by norm_num)
  simpa [T, terms, observable, deleted, localFamilyInside, commSum, colourOrder,
    colourClass, colouring,
    SimpleGraph.Coloring.mk,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hb

-- On this disconnected finite graph, the comparison theorem forces exact equality
-- on the other component, even though the deleted Hamiltonian is nonzero.
private theorem disconnected_evolution (t : ℝ) :
    0 < ∑ k ∈ Finset.univ.filter (fun k ↦ ¬ T k ⊆ {false}), ‖place (T k) (terms k)‖ ∧
    heisenbergEvolution (∑ k, place (T k) (localFamilyInside terms {false} k)) t observable =
      heisenbergEvolution (∑ k, place (T k) (terms k)) t observable := by
  refine ⟨deleted_mass_pos, ?_⟩
  let error := ‖heisenbergEvolution
    (∑ k, place (T k) (localFamilyInside terms {false} k)) t observable -
      heisenbergEvolution (∑ k, place (T k) (terms k)) t observable‖
  have hb (d : ℕ) : error ≤
      (4 * ‖observable‖ * ‖deleted‖ * |t|) * Real.exp (4 * ‖deleted‖ * |t| - d) := by
    have hbound := norm_heisenbergEvolution_localFamilyInside_sub_le_graphDistance
      (fun _ ↦ projection_hermitian true) (⊥ : SimpleGraph Bool) 0 range_zero 1
      (by simp) ‖deleted‖ site_budget
      (place_mem_supportedOperators (projection false)) 1 (by norm_num) d
      (exterior_distance d) t
    simpa [error, T, terms, observable, deleted, localFamilyInside, abs_of_nonneg (norm_nonneg _),
      mul_right_comm] using hbound
  have hlim : Filter.Tendsto
      (fun d : ℕ ↦ (4 * ‖observable‖ * ‖deleted‖ * |t|) *
        Real.exp (4 * ‖deleted‖ * |t| - d)) Filter.atTop (nhds 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
      ((4 * ‖observable‖ * ‖deleted‖ * |t|) * Real.exp (4 * ‖deleted‖ * |t|))
    simpa [sub_eq_add_neg, Real.exp_add, mul_assoc] using h
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (ge_of_tendsto' hlim hb) (norm_nonneg _)))

#print axioms negative_time_nonzero_deleted
#print axioms disconnected_evolution

end DeletedTermRegression
