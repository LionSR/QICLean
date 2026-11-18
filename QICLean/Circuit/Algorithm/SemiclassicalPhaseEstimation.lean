/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Algorithm.PhaseEstimation

/-!
# Semiclassical phase estimation

The inverse Fourier transform followed by a measurement can be replaced by measurements of the
qubits one at a time, each preceded by a phase correction chosen from the earlier outcomes
(Griffiths–Niu, *Semiclassical Fourier transform for quantum computation*, PRL 76 (1996) 3228;
Nielsen–Chuang, §5.2). After the preparation, the control qubit `j` carries
`(|0⟩ + e^{2πiφ 2^{t-1-j}} |1⟩)/√2`. The qubits are measured in the order `0, 1, …, t - 1`: the
qubit `j` gets the phase gate `diag(1, e^{-2πiθ})`, with `θ = ∑_{i < j} bᵢ / 2^{j-i+1}` from the
outcomes `bᵢ` of the qubits measured before it, then the Hadamard gate, and is measured. The
outcome of the qubit `j` is the bit of the estimate `k` at the site `t - 1 - j`.

This is a circuit with classical feedback: the layer measuring the qubit `j` depends on the
outcomes of the earlier layers. Its outcomes have the distribution of the coherent circuit, so
the success probability and the number of calls are those of phase estimation; the circuit has
no two-qubit gates after the calls.

## Main definitions

* `QuantumCircuit.PhaseEstimation.correction` — the phase correction from the earlier outcomes.
* `QuantumCircuit.PhaseEstimation.measureQubit` — the corrected measurement of one qubit.
* `QuantumCircuit.PhaseEstimation.semiclassical` — the circuit, with its readout
  `semiclassicalReadout`.

## Main results

* `QuantumCircuit.PhaseEstimation.semiclassical_outcomeProb_eq` — the outcome `k` has the
  probability `|αₖ|²` of the coherent circuit.
* `QuantumCircuit.PhaseEstimation.semiclassical_accurate_prob_ge` — the success probability.
* `QuantumCircuit.PhaseEstimation.queryCount_semiclassical` — the number of calls.
-/

open Matrix ManyBody Complex
open QuantumCircuit.Qubit (Q encode hadamard controlled)

namespace QuantumCircuit

namespace PhaseEstimation

variable (t m : ℕ)

/-- The phase correction `θ = ∑_{i < j} bᵢ / 2^{j-i+1}` of the qubit `j`, from the outcomes `b`
of the qubits measured before it. -/
noncomputable def correction (b : Fin t → Fin 2) (j : Fin t) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· < j), ((b i : ℕ) : ℝ) / 2 ^ ((j : ℕ) - i + 1)

/-- The measurement of a qubit after the phase gate `diag(1, e^{-2πiθ})` and the Hadamard gate:
the outcome `c` has the operator `|c⟩⟨c| H diag(1, e^{-2πiθ})`. -/
noncomputable def correctedMeasure (θ : ℝ) : KrausFamily (Fin 2) (Fin 2) :=
  ⟨Fin 2, fun c ↦ Matrix.single c c 1 * hadamard *
    diagonal fun x : Fin 2 ↦ exp (-(2 * Real.pi * I * θ * ((x : ℕ) : ℂ)))⟩

/-- The corrected measurement of the control qubit `j`. -/
noncomputable def measureQubit (j : Fin t) (θ : ℝ) :
    Layer (geometry t) (Gate t m) (system t m) (system t m) :=
  Layer.single (.inl (.inl j)) (.inl ⟨Fin 2, fun c ↦ ((correctedMeasure θ).op c).submatrix
    (siteEquiv (system t m) (.inl j)) (siteEquiv (system t m) (.inl j))⟩)

/-- The outcome of the corrected measurement of a qubit. -/
def qubitOutcome {j : Fin t} {θ : ℝ} (i : (measureQubit t m j θ).Index) : Fin 2 :=
  i.1 ⟨.inl (.inl j), Finset.mem_singleton_self _⟩

/-- The corrected measurements of the qubits of `l` in order, after the outcomes `b`. -/
noncomputable def measureFrom :
    List (Fin t) → (Fin t → Fin 2) → Circuit (geometry t) (Gate t m) (system t m) (system t m)
  | [], _ => .done _
  | j :: l, b => .step (measureQubit t m j (correction t b j)) fun i ↦
      measureFrom l (Function.update b j (qubitOutcome t m i))

/-- The outcomes along a branch of `measureFrom l b`, with `b` at the qubits outside `l`. -/
noncomputable def outcomesFrom :
    (l : List (Fin t)) → (b : Fin t → Fin 2) → (measureFrom t m l b).Index → Fin t → Fin 2
  | [], b, _ => b
  | j :: l, b, p =>
    outcomesFrom l (Function.update b j (qubitOutcome t m
      (p : Σ i : (measureQubit t m j (correction t b j)).Index,
        (measureFrom t m l (Function.update b j (qubitOutcome t m i))).Index).1)) p.2

/-- Semiclassical phase estimation: the preparation, then the corrected measurements of the
qubits `0, 1, …, t - 1`. -/
noncomputable abbrev semiclassical : Circuit (geometry t) (Gate t m) (system t m) (system t m) :=
  (prepare t m).comp (measureFrom t m (List.finRange t) 0)

/-- The measured integer: the outcome of the qubit `j` is the bit at the site `t - 1 - j`. -/
noncomputable def semiclassicalReadout (p : (semiclassical t m).Index) : Fin (2 ^ t) :=
  encode t fun s ↦ outcomesFrom t m (List.finRange t) 0 ((prepare t m).compIndexEquiv _ p).2 s.rev

variable {t m}

/-! ### Branches -/

/-- The index of the corrected measurement with the outcome `c`. -/
private def outcomeIndex {j : Fin t} {θ : ℝ} (c : Fin 2) : (measureQubit t m j θ).Index :=
  (fun x ↦ by
    obtain ⟨y, hy⟩ := x
    obtain rfl := Finset.mem_singleton.mp hy
    exact c, fun _ ↦ ())

private theorem qubitOutcome_outcomeIndex {j : Fin t} {θ : ℝ} (c : Fin 2) :
    qubitOutcome t m (outcomeIndex (t := t) (m := m) (j := j) (θ := θ) c) = c :=
  rfl

private theorem outcomeIndex_qubitOutcome {j : Fin t} {θ : ℝ} (i : (measureQubit t m j θ).Index) :
    outcomeIndex (qubitOutcome t m i) = i := by
  refine Prod.ext (funext fun x ↦ ?_) (funext fun _ ↦ rfl)
  obtain ⟨y, hy⟩ := x
  obtain rfl := Finset.mem_singleton.mp hy
  rfl

/-- The outcomes outside `l` are those before. -/
private theorem outcomesFrom_of_notMem : ∀ (l : List (Fin t)) (b : Fin t → Fin 2)
    (p : (measureFrom t m l b).Index) (i : Fin t), i ∉ l → outcomesFrom t m l b p i = b i
  | [], _, _, _, _ => rfl
  | j :: l, b, ⟨q, r⟩, i, hi => by
    rw [List.mem_cons, not_or] at hi
    change outcomesFrom t m l _ r i = b i
    rw [outcomesFrom_of_notMem l _ r i hi.2, Function.update_of_ne hi.1]

private theorem outcomesFrom_injective : ∀ (l : List (Fin t)), l.Nodup → ∀ (b : Fin t → Fin 2),
    Function.Injective (outcomesFrom t m l b)
  | [], _, _, _, _, _ => rfl
  | j :: l, hl, b, ⟨q, r⟩, ⟨q', r'⟩, h => by
    rw [List.nodup_cons] at hl
    have hj := congrFun h j
    change outcomesFrom t m l _ r j = outcomesFrom t m l _ r' j at hj
    rw [outcomesFrom_of_notMem l _ r j hl.1, outcomesFrom_of_notMem l _ r' j hl.1,
      Function.update_self, Function.update_self] at hj
    obtain rfl : q = q' := by
      rw [← outcomeIndex_qubitOutcome q, ← outcomeIndex_qubitOutcome q', hj]
    obtain rfl := outcomesFrom_injective l hl.2 _ h
    rfl

/-- The branch with the outcomes `B` on `l`. -/
private noncomputable def branchOf (B : Fin t → Fin 2) :
    (l : List (Fin t)) → (b : Fin t → Fin 2) → (measureFrom t m l b).Index
  | [], _ => ()
  | j :: l, b => ⟨outcomeIndex (B j), branchOf B l (Function.update b j (B j))⟩

private theorem outcomesFrom_branchOf (B : Fin t → Fin 2) : ∀ (l : List (Fin t))
    (b : Fin t → Fin 2) (i : Fin t),
    outcomesFrom t m l b (branchOf B l b) i = if i ∈ l then B i else b i
  | [], _, i => by simp [outcomesFrom]
  | j :: l, b, i => by
    change outcomesFrom t m l _ (branchOf B l _) i = _
    rw [outcomesFrom_branchOf B l _ i]
    change (if i ∈ l then B i else Function.update b j (B j) i) = _
    by_cases hi : i ∈ l
    · simp [hi]
    · by_cases hij : i = j
      · subst hij; simp
      · simp [hi, hij]

private theorem outcomesFrom_bijective :
    Function.Bijective (outcomesFrom t m (List.finRange t) 0) := by
  refine ⟨outcomesFrom_injective _ (List.nodup_finRange t) 0, fun B ↦ ⟨branchOf B _ 0, ?_⟩⟩
  funext i
  rw [outcomesFrom_branchOf]
  simp

/-! ### The state along a branch -/

/-- The product state `∏ᵢ Fᵢ(xᵢ)` of the control register. -/
private def prodState (F : Fin t → Fin 2 → ℂ) (x : Config (Q t)) : ℂ :=
  ∏ i, F i (x i)

private theorem prodState_eq (F : Fin t → Fin 2 → ℂ) (j : Fin t) (x : Config (Q t)) :
    prodState F x = F j (x j) * ∏ i ∈ Finset.univ.erase j, F i (x i) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

/-- The matrix `H diag(1, e^{-2πiθ})` of the corrected measurement before the projection. -/
private noncomputable def correctedHadamard (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  hadamard * diagonal fun x : Fin 2 ↦ exp (-(2 * Real.pi * I * θ * ((x : ℕ) : ℂ)))

/-- The amplitude `∑_y (H D_θ)(c, y) G(y)` of the outcome `c` on a qubit in the state `G`. -/
private noncomputable def beta (θ : ℝ) (c : Fin 2) (G : Fin 2 → ℂ) : ℂ :=
  ∑ y, correctedHadamard θ c y * G y

/-- The corrected measurement with outcome `c` projects the qubit `j` of a product state onto
`|c⟩`, with the amplitude `beta`. -/
private theorem measureQubit_mulVec {ev : Interpretation (Oracle (Fin 2 × Fin m))} (j : Fin t)
    (θ : ℝ) (i : (measureQubit t m j θ).Index) (u : Fin m → ℂ) (F : Fin t → Fin 2 → ℂ) :
    (measureQubit t m j θ).kraus (Interpretation.sum KrausGate.ev ev) i *ᵥ
      registerState u (prodState F) =
      registerState u (prodState (Function.update F j fun y ↦
        if y = qubitOutcome t m i then beta θ (qubitOutcome t m i) (F j) else 0)) := by
  have hk : (measureQubit t m j θ).kraus (Interpretation.sum KrausGate.ev ev) i =
      place {Sum.inl j} (((correctedMeasure θ).op (qubitOutcome t m i)).submatrix
        (siteEquiv (system t m) (.inl j)) (siteEquiv (system t m) (.inl j))) :=
    Layer.kraus_single _ _ _ i
  rw [hk, qubitGate_mulVec]
  congr 1
  funext x
  rw [prodState_eq _ j, Function.update_self]
  have hrest : ∀ b : Fin 2, ∏ a ∈ Finset.univ.erase j, F a (Function.update x j b a) =
      ∏ a ∈ Finset.univ.erase j, Function.update F j
        (fun y ↦ if y = qubitOutcome t m i then beta θ (qubitOutcome t m i) (F j) else 0) a
          (x a) := fun b ↦
    Finset.prod_congr rfl fun a hi ↦ by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
        Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hV : ∀ b, (correctedMeasure θ).op (qubitOutcome t m i) (x j) b =
      if x j = qubitOutcome t m i then correctedHadamard θ (qubitOutcome t m i) b else 0 := by
    intro b
    change ((Matrix.single (qubitOutcome t m i) (qubitOutcome t m i) (1 : ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) * Qubit.hadamard * diagonal fun x : Fin 2 ↦
        exp (-(2 * Real.pi * I * θ * ((x : ℕ) : ℂ)))) (x j) b = _
    rw [Matrix.mul_assoc]
    split_ifs with h
    · rw [h, Matrix.single_mul_apply_same, one_mul]
      rfl
    · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _
  simp only [hV, prodState_eq _ j, Function.update_self, hrest, ite_mul, zero_mul]
  split_ifs with h
  · rw [beta, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  · simp

/-- Semiclassical phase estimation has the outcome distribution of phase estimation: on the
input `|0…0⟩ ⊗ u` for an eigenvector `U u = e^{2πiφ} u` of norm `1`, the outcome `k` has the
probability `|αₖ|²` (Griffiths–Niu; Nielsen–Chuang, eq. (5.24)). -/
theorem semiclassical_outcomeProb_eq {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ}
    (hu : star u ⬝ᵥ u = 1) {φ : ℝ} (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u)
    (k : Fin (2 ^ t)) :
    (semiclassical t m).outcomeProb (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
      (semiclassicalReadout t m) (vecMulVec (input t m u) (star (input t m u))) k =
      ‖amplitude t φ k‖ ^ 2 := by
  sorry

/-- Semiclassical phase estimation with `t = n + ⌈log₂(2 + 1/(2ε))⌉` control qubits returns an
estimate within `2^{-n}` of `φ` modulo `1` with probability at least `1 - ε`. -/
theorem semiclassical_accurate_prob_ge (U : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → ℂ)
    (hu : star u ⬝ᵥ u = 1) (φ : ℝ) (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) (ht : t = n + ⌈Real.logb 2 (2 + 1 / (2 * ε))⌉₊) :
    1 - ε ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ t) ↦
        |(k : ℝ) / 2 ^ t - φ - round ((k : ℝ) / 2 ^ t - φ)| ≤ 1 / 2 ^ n),
      (semiclassical t m).outcomeProb
        (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
        (semiclassicalReadout t m) (vecMulVec (input t m u) (star (input t m u))) k := by
  simp only [semiclassical_outcomeProb_eq hu huφ]
  exact one_sub_le_sum_norm_sq_amplitude φ n hε ht

/-- Semiclassical phase estimation calls the oracle `2^t - 1` times. -/
theorem queryCount_semiclassical : (semiclassical t m).queryCount = 2 ^ t - 1 := by
  have h : ∀ (l : List (Fin t)) (b : Fin t → Fin 2), (measureFrom t m l b).total
      (fun _ _ L ↦ L.cellCost fun _ _ _ g ↦ Oracle.callCount g) = 0 := by
    intro l
    induction l with
    | nil => exact fun _ ↦ rfl
    | cons j l ih =>
      intro b
      change (measureQubit t m j (correction t b j)).cellCost _ +
        Finset.univ.sup (fun i ↦ (measureFrom t m l _).total _) = 0
      rw [show (measureQubit t m j (correction t b j)).cellCost
          (fun _ _ _ g ↦ Oracle.callCount g) = 0 from Layer.cellCost_single _ _ _, zero_add]
      exact Nat.eq_zero_of_le_zero (Finset.sup_le fun _ _ ↦ (ih _).le)
  rw [Circuit.queryCount, Circuit.total_comp_of_isUnbranched _ isUnbranched_prepare
    ⟨nonempty_unique_index_prepare.some.default⟩, h, add_zero, ← Circuit.queryCount,
    queryCount_prepare]

end PhaseEstimation

end QuantumCircuit
