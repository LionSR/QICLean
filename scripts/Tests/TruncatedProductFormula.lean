import QICLean.Circuit.Simulation.TruncatedProductFormula

/-! Kernel audit and boundary regressions for the finite circuit truncation estimates. -/
open Matrix ManyBody ProductFormula QuantumCircuit
open scoped Matrix.Norms.L2Operator

#print axioms QuantumCircuit.sum_place_localFamilyInside
#print axioms QuantumCircuit.norm_heisenbergEvolution_localFamilyInside_sub_le_graphDistance
#print axioms QuantumCircuit.norm_dual_trotterCircuit_localFamilyInside_sub_le_graphDistance
#print axioms QuantumCircuit.norm_dual_trotterCircuit_sub_le_restrict_graphDistance

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
