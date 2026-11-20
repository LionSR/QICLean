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
Nielsen–Chuang, §5.2). Griffiths and Niu show this for every input state; here it is proved for
the input of phase estimation, `|0…0⟩ ⊗ u` with an eigenvector `u`, where the control register
is a product state after the calls. After the preparation, the control qubit `j` carries
`(|0⟩ + e^{2πiφ 2^{t-1-j}} |1⟩)/√2`. The qubits are measured in the order `0, 1, …, t - 1`: the
qubit `j` gets the phase gate `diag(1, e^{-2πiθ})`, with `θ = ∑_{i < j} bᵢ / 2^{j-i+1}` from the
outcomes `bᵢ` of the qubits measured before it, then the Hadamard gate, and is measured. The
outcome of the qubit `j` is the bit of the estimate `k` at the site `t - 1 - j`.

This is a circuit with classical feedback: the layer measuring the qubit `j` depends on the
outcomes of the earlier layers. It is the first circuit here whose continuation `next i` in
`Circuit.step` depends on the outcome `i`. On the eigenvector input its outcomes have the
distribution of the coherent circuit, so the success probability and the number of calls are
those of phase estimation; the circuit has no two-qubit gates after the calls.

**Scope restriction (eigenvector input):** `semiclassical_outcomeProb_eq` and
`semiclassical_accurate_prob_ge` assume the input `|0…0⟩ ⊗ u` with `U u = e^{2πiφ} u`, while
Griffiths and Niu prove that the semiclassical measurements reproduce the outcome distribution
of the coherent circuit for every input. Documented in
`docs/paper-gaps/gn96_semiclassical_general_input_scope.tex`, with the elimination by deferred
measurement, an identity of instruments valid on every input.

The proof follows a branch. After the preparation the control register is the product state
`∏ⱼ 2^{-1/2} (|0⟩ + e^{2πiφ 2^{t-1-j}} |1⟩)`. The corrected measurement of the qubit `j` with
the outcome `bⱼ` keeps a product state, the qubit `j` replaced by `βⱼ |bⱼ⟩` with
`βⱼ = (1 + (-1)^{bⱼ} e^{-2πiθⱼ} e^{2πiφ 2^{t-1-j}})/2`. Writing `k = ∑ⱼ bⱼ 2^j` for the readout,
`k/2^{j+1} ≡ bⱼ/2 + θⱼ` modulo `1`, so `βⱼ = (1 + z^{2^{t-1-j}})/2` with `z = e^{2πi(φ - k/2^t)}`,
and `∏ⱼ βⱼ = 2^{-t} ∑_{l < 2^t} z^l = αₖ`. The outcomes of the branches are the bit strings,
each once.

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
open QuantumCircuit.Qubit (encode hadamard controlled)

namespace QuantumCircuit

namespace PhaseEstimation

variable (t m : ℕ)

/-- The phase correction `θ = ∑_{i < j} bᵢ / 2^{j-i+1}` of the qubit `j`, from the outcomes `b`
of the qubits measured before it. -/
noncomputable def correction (b : Fin t → Fin 2) (j : Fin t) : ℝ :=
  ∑ i ∈ Finset.univ.filter (· < j), ((b i : ℕ) : ℝ) / 2 ^ ((j : ℕ) - i + 1)

/-- The phase gate `diag(1, e^{-2πiθ})` followed by the Hadamard gate. -/
noncomputable def correctedHadamard (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  hadamard * diagonal fun x : Fin 2 ↦ exp (-(2 * Real.pi * I * θ * ((x : ℕ) : ℂ)))

/-- The measurement of a qubit after the phase gate `diag(1, e^{-2πiθ})` and the Hadamard gate:
the outcome `c` has the operator `|c⟩⟨c| H diag(1, e^{-2πiθ})`. -/
noncomputable def correctedMeasure (θ : ℝ) : KrausFamily (Fin 2) (Fin 2) :=
  ⟨Fin 2, fun c ↦ Matrix.single c c 1 * correctedHadamard θ⟩

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
private def prodState (F : Fin t → Fin 2 → ℂ) (x : Config (Qudits (Fin t) 2)) : ℂ :=
  ∏ i, F i (x i)

private theorem prodState_eq (F : Fin t → Fin 2 → ℂ) (j : Fin t) (x : Config (Qudits (Fin t) 2)) :
    prodState F x = F j (x j) * ∏ i ∈ Finset.univ.erase j, F i (x i) :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ j)).symm

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
      Matrix (Fin 2) (Fin 2) ℂ) * correctedHadamard θ) (x j) b = _
    split_ifs with h
    · rw [h, Matrix.single_mul_apply_same, one_mul]
    · exact Matrix.single_mul_apply_of_ne _ _ _ _ _ h _
  simp only [hV, prodState_eq _ j, Function.update_self, hrest, ite_mul, zero_mul]
  split_ifs with h
  · rw [beta, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  · simp

/-- The factors of the product state at the end of a branch of `measureFrom l b`. -/
private noncomputable def finalFactors :
    (l : List (Fin t)) → (b : Fin t → Fin 2) → (Fin t → Fin 2 → ℂ) →
      (measureFrom t m l b).Index → Fin t → Fin 2 → ℂ
  | [], _, F, _ => F
  | j :: l, b, F, p =>
    let q := (p : Σ i : (measureQubit t m j (correction t b j)).Index,
      (measureFrom t m l (Function.update b j (qubitOutcome t m i))).Index)
    finalFactors l (Function.update b j (qubitOutcome t m q.1))
      (Function.update F j fun y ↦ if y = qubitOutcome t m q.1 then
        beta (correction t b j) (qubitOutcome t m q.1) (F j) else 0) q.2

private theorem kraus_measureFrom_mulVec {ev : Interpretation (Oracle (Fin 2 × Fin m))}
    (u : Fin m → ℂ) : ∀ (l : List (Fin t)) (b : Fin t → Fin 2) (F : Fin t → Fin 2 → ℂ)
      (p : (measureFrom t m l b).Index),
      (measureFrom t m l b).kraus (Interpretation.sum KrausGate.ev ev) p *ᵥ
        registerState u (prodState F) = registerState u (prodState (finalFactors l b F p))
  | [], _, F, _ => by
    change (1 : Matrix _ _ ℂ) *ᵥ _ = _
    rw [one_mulVec]
    rfl
  | j :: l, b, F, ⟨q, r⟩ => by
    change ((measureFrom t m l _).kraus _ r * (measureQubit t m j _).kraus _ q) *ᵥ _ = _
    rw [← mulVec_mulVec, measureQubit_mulVec, kraus_measureFrom_mulVec u l _ _ r]
    rfl

/-- The correction of the qubit `j` reads only the outcomes of the qubits before it. -/
private theorem correction_congr {b b' : Fin t → Fin 2} {j : Fin t}
    (h : ∀ i < j, b i = b' i) : correction t b j = correction t b' j :=
  Finset.sum_congr rfl fun i hi ↦ by rw [h i (Finset.mem_filter.mp hi).2]

/-- Along a branch measuring the qubits of `l` in increasing order, the factor of a measured
qubit is its outcome with the amplitude of its corrected measurement. -/
private theorem finalFactors_eq : ∀ (l : List (Fin t)), l.Pairwise (· < ·) →
    ∀ (b : Fin t → Fin 2) (F : Fin t → Fin 2 → ℂ) (p : (measureFrom t m l b).Index),
      (∀ i ∉ l, finalFactors l b F p i = F i) ∧ ∀ i ∈ l, finalFactors l b F p i = fun y ↦
        if y = outcomesFrom t m l b p i then
          beta (correction t (outcomesFrom t m l b p) i) (outcomesFrom t m l b p i) (F i) else 0
  | [], _, _, _, _ => ⟨fun _ _ ↦ rfl, fun _ h ↦ absurd h (List.not_mem_nil)⟩
  | j :: l, hl, b, F, ⟨q, r⟩ => by
    rw [List.pairwise_cons] at hl
    have hjl : j ∉ l := fun h ↦ lt_irrefl j (hl.1 j h)
    obtain ⟨ih1, ih2⟩ := finalFactors_eq l hl.2 (Function.update b j (qubitOutcome t m q))
      (Function.update F j fun y ↦ if y = qubitOutcome t m q then
        beta (correction t b j) (qubitOutcome t m q) (F j) else 0) r
    have hB : ∀ i ∉ l, outcomesFrom t m l (Function.update b j (qubitOutcome t m q)) r i =
        Function.update b j (qubitOutcome t m q) i := outcomesFrom_of_notMem l _ r
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
    · rw [List.mem_cons, not_or] at hi
      change finalFactors l _ _ r i = F i
      rw [ih1 i hi.2, Function.update_of_ne hi.1]
    · change finalFactors l _ _ r i = fun y ↦ if y = outcomesFrom t m l _ r i then
        beta (correction t (outcomesFrom t m l _ r) i) (outcomesFrom t m l _ r i) (F i) else 0
      rcases List.mem_cons.mp hi with rfl | hi
      · have hc : correction t b i = correction t (outcomesFrom t m l _ r) i :=
          correction_congr fun i' hi' ↦ by
            rw [hB i' fun h ↦ lt_asymm hi' (hl.1 i' h), Function.update_of_ne hi'.ne]
        rw [ih1 i hjl, Function.update_self, hB i hjl, Function.update_self,
          show beta (correction t b i) (qubitOutcome t m q) (F i) =
            beta (correction t (outcomesFrom t m l _ r) i) (qubitOutcome t m q) (F i) from
            congrArg (fun θ ↦ beta θ (qubitOutcome t m q) (F i)) hc]
      · rw [ih2 i hi, Function.update_of_ne (hl.1 i hi).ne']

/-! ### The probabilities -/

/-- The factor of the qubit `i` after the preparation:
`2^{-1/2} (|0⟩ + e^{2πiφ 2^{t-1-i}} |1⟩)`. -/
private noncomputable def preparedFactor (φ : ℝ) (i : Fin t) (y : Fin 2) : ℂ :=
  invSqrtTwo * exp (2 * Real.pi * I * φ) ^ ((y : ℕ) * 2 ^ (t - 1 - (i : ℕ)))

private theorem prepared_eq (φ : ℝ) (x : Config (Qudits (Fin t) 2)) :
    invSqrtTwo ^ t * exp (2 * Real.pi * I * φ) ^ (encode t x : ℕ) =
      prodState (preparedFactor φ) x := by
  rw [prodState, Qudit.encode_apply]
  simp only [preparedFactor, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow_eq_pow_sum]

/-- `∑_{j < 2^t} z^j = ∏_{s < t} (1 + z^{2^s})`. -/
private theorem geom_sum_two_pow (z : ℂ) (t : ℕ) :
    ∑ j ∈ Finset.range (2 ^ t), z ^ j = ∏ s ∈ Finset.range t, (1 + z ^ 2 ^ s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, mul_two, Finset.sum_range_add, Finset.prod_range_succ, ← ih]
    simp only [pow_add, ← Finset.mul_sum]
    ring

/-- The digits of `k = ∑ B_{i'} 2^{i'}` around the position `i`. -/
private theorem digits_split (t : ℕ) (B : Fin t → Fin 2) (i : Fin t) :
    ∑ i', ((B i' : ℕ) : ℝ) * 2 ^ (i' : ℕ) =
      2 ^ ((i : ℕ) + 1) * ((∑ i' ∈ Finset.univ.filter (i < ·),
        (B i' : ℕ) * 2 ^ ((i' : ℕ) - i - 1) : ℕ) : ℝ) + 2 ^ (i : ℕ) * ((B i : ℕ) : ℝ) +
        2 ^ ((i : ℕ) + 1) * ∑ i' ∈ Finset.univ.filter (· < i),
          ((B i' : ℕ) : ℝ) / 2 ^ ((i : ℕ) - i' + 1) := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (i < ·)]
  have hrest : Finset.univ.filter (fun i' : Fin t ↦ ¬ i < i') =
      insert i (Finset.univ.filter (· < i)) := by
    ext i'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, not_lt]
    exact ⟨fun h ↦ (eq_or_lt_of_le h), fun h ↦ h.elim (fun e ↦ e ▸ le_rfl) le_of_lt⟩
  rw [hrest, Finset.sum_insert (by simp)]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  have h1 : ∀ i' ∈ Finset.univ.filter (fun i' : Fin t ↦ i < i'),
      ((B i' : ℕ) : ℝ) * 2 ^ (i' : ℕ) =
        2 ^ ((i : ℕ) + 1) * (((B i' : ℕ) : ℝ) * 2 ^ ((i' : ℕ) - i - 1)) := by
    intro i' hi'
    have := (Finset.mem_filter.mp hi').2
    have hle : (i : ℕ) + 1 ≤ i' := this
    rw [mul_left_comm, ← pow_add, show (i : ℕ) + 1 + ((i' : ℕ) - i - 1) = i' by omega]
  have h2 : ∀ i' ∈ Finset.univ.filter (fun i' : Fin t ↦ i' < i),
      ((B i' : ℕ) : ℝ) * 2 ^ (i' : ℕ) =
        2 ^ ((i : ℕ) + 1) * (((B i' : ℕ) : ℝ) / 2 ^ ((i : ℕ) - i' + 1)) := by
    intro i' hi'
    have := (Finset.mem_filter.mp hi').2
    have hle : (i' : ℕ) < i := this
    have hp : (2 : ℝ) ^ ((i : ℕ) + 1) = 2 ^ (i' : ℕ) * 2 ^ ((i : ℕ) - i' + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hp]
    field_simp
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
  ring

private theorem beta_preparedFactor (θ φ : ℝ) (c : Fin 2) (i : Fin t) :
    beta θ c (preparedFactor φ i) = 2⁻¹ * (1 + (-1) ^ (c : ℕ) *
      exp (-(2 * Real.pi * I * θ)) * exp (2 * Real.pi * I * φ) ^ 2 ^ (t - 1 - (i : ℕ))) := by
  simp only [beta, correctedHadamard, Fin.sum_univ_two, mul_diagonal, Qubit.hadamard_apply,
    preparedFactor, Fin.val_zero, Fin.val_one, mul_zero, pow_zero, Nat.cast_zero, Nat.cast_one,
    mul_one, zero_mul, neg_zero, Complex.exp_zero, one_mul]
  linear_combination (1 + (-1) ^ (c : ℕ) * exp (-(2 * Real.pi * I * θ)) *
    exp (2 * Real.pi * I * φ) ^ 2 ^ (t - 1 - (i : ℕ))) * invSqrtTwo_mul_self

/-- The phase of the qubit `i` after the corrections is that of `z^{2^{t-1-i}}`,
`z = e^{2πi(φ - k/2^t)}`, because `k/2^{i+1} ≡ bᵢ/2 + θᵢ` modulo `1`. -/
private theorem phase_eq (φ : ℝ) (B : Fin t → Fin 2) (i : Fin t) :
    (-1) ^ (B i : ℕ) * exp (-(2 * Real.pi * I * correction t B i)) *
      exp (2 * Real.pi * I * φ) ^ 2 ^ (t - 1 - (i : ℕ)) =
      exp (2 * Real.pi * I * (φ - (encode t fun s ↦ B s.rev : ℕ) / 2 ^ t)) ^
        2 ^ (t - 1 - (i : ℕ)) := by
  set k : ℕ := ((encode t fun s ↦ B s.rev : Fin (2 ^ t)) : ℕ)
  set M : ℕ := ∑ i' ∈ Finset.univ.filter (i < ·), (B i' : ℕ) * 2 ^ ((i' : ℕ) - i - 1)
  have hk : (k : ℝ) = ∑ i', ((B i' : ℕ) : ℝ) * 2 ^ (i' : ℕ) := by
    have := Qudit.encode_apply (n := t) fun s ↦ B s.rev
    simp only [k]
    rw [this]
    push_cast
    refine Fintype.sum_equiv Fin.revPerm _ _ fun s ↦ ?_
    simp only [Fin.revPerm_apply, Fin.val_rev]
    congr 2
    omega
  have hi : (i : ℕ) < t := i.2
  have hw : (2 : ℝ) ^ (t - 1 - (i : ℕ)) * k / 2 ^ t =
      M + ((B i : ℕ) : ℝ) / 2 + correction t B i := by
    have h2t : (2 : ℝ) ^ t = 2 ^ (t - 1 - (i : ℕ)) * 2 ^ ((i : ℕ) + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hk, digits_split t B i, h2t, correction]
    field_simp
    ring
  have hw' : (2 : ℂ) ^ (t - 1 - (i : ℕ)) * k / 2 ^ t =
      M + ((B i : ℕ) : ℂ) / 2 + correction t B i := by
    have := congrArg (fun x : ℝ ↦ (x : ℂ)) hw
    push_cast at this
    exact this
  have hB : exp (Real.pi * I * ((B i : ℕ) : ℂ)) = (-1) ^ (B i : ℕ) := by
    rcases Fin.exists_fin_two.mp ⟨B i, rfl⟩ with h | h <;> rw [h] <;> simp [Complex.exp_pi_mul_I]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  push_cast
  rw [show (2 : ℂ) ^ (t - 1 - (i : ℕ)) * (2 * Real.pi * I * (φ - k / 2 ^ t)) =
      2 ^ (t - 1 - (i : ℕ)) * (2 * Real.pi * I * φ) -
        2 * Real.pi * I * (2 ^ (t - 1 - (i : ℕ)) * k / 2 ^ t) by ring, hw',
    Complex.exp_sub, show 2 * Real.pi * I * (M + ((B i : ℕ) : ℂ) / 2 + correction t B i) =
      M * (2 * Real.pi * I) + Real.pi * I * ((B i : ℕ) : ℂ) +
        2 * Real.pi * I * correction t B i by ring, Complex.exp_add, Complex.exp_add,
    Complex.exp_nat_mul_two_pi_mul_I, hB, Complex.exp_neg]
  rcases Fin.exists_fin_two.mp ⟨B i, rfl⟩ with h | h <;> rw [h] <;> field_simp <;> norm_num

/-- The product of the amplitudes of the corrected measurements is the amplitude of the
readout. -/
private theorem prod_beta (φ : ℝ) (B : Fin t → Fin 2) :
    ∏ i, beta (correction t B i) (B i) (preparedFactor φ i) =
      amplitude t φ (encode t fun s ↦ B s.rev) := by
  set z := exp (2 * Real.pi * I * (φ - (encode t fun s ↦ B s.rev : ℕ) / 2 ^ t))
  rw [amplitude_eq_geom_sum, geom_sum_two_pow, ← Finset.prod_range_reflect,
    ← Fin.prod_univ_eq_prod_range (fun s ↦ 1 + z ^ 2 ^ (t - 1 - s)),
    show ((2 : ℂ) ^ t)⁻¹ = ∏ _i : Fin t, (2 : ℂ)⁻¹ by simp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [beta_preparedFactor, phase_eq]

private theorem prob_semiclassical {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ}
    (hu : star u ⬝ᵥ u = 1) {φ : ℝ} (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u)
    (p : (semiclassical t m).Index) :
    (semiclassical t m).prob (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
      (vecMulVec (input t m u) (star (input t m u))) p =
      ‖amplitude t φ (semiclassicalReadout t m p)‖ ^ 2 := by
  rw [Circuit.prob_vecMulVec, Circuit.kraus_comp, ← mulVec_mulVec, kraus_prepare_mulVec huφ,
    show (fun x ↦ invSqrtTwo ^ t * exp (2 * Real.pi * I * φ) ^ (encode t x : ℕ)) =
      prodState (preparedFactor φ) from funext (prepared_eq φ), kraus_measureFrom_mulVec,
    sum_norm_sq_registerState hu, semiclassicalReadout, ← prod_beta]
  generalize ((prepare t m).compIndexEquiv _ p).2 = q
  obtain ⟨-, h⟩ := finalFactors_eq (List.finRange t) (List.pairwise_lt_finRange t) 0
    (preparedFactor φ) q
  simp only [prodState, norm_prod, ← Finset.prod_pow]
  rw [← Fintype.prod_sum fun i y ↦
    ‖finalFactors (List.finRange t) 0 (preparedFactor φ) q i y‖ ^ 2]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [h i (List.mem_finRange i)]
  simp only [apply_ite (fun z : ℂ ↦ ‖z‖ ^ 2), norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  rw [Finset.sum_ite_eq']
  simp

private theorem semiclassicalReadout_bijective :
    Function.Bijective (semiclassicalReadout t m) := by
  obtain ⟨hu⟩ := nonempty_unique_index_prepare (t := t) (m := m)
  have h₁ : Function.Bijective fun p : (semiclassical t m).Index ↦
      ((prepare t m).compIndexEquiv _ p).2 :=
    (((prepare t m).compIndexEquiv _).trans (Equiv.uniqueProd _ _)).bijective
  have h₂ : Function.Bijective fun B : Fin t → Fin 2 ↦ fun s : Fin t ↦ B s.rev :=
    (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin 2))).bijective
  exact (encode t).bijective.comp (h₂.comp (outcomesFrom_bijective.comp h₁))

/-- Semiclassical phase estimation has the outcome distribution of phase estimation: on the
input `|0…0⟩ ⊗ u` for an eigenvector `U u = e^{2πiφ} u` of norm `1`, the outcome `k` has the
probability `|αₖ|²` (Griffiths–Niu; Nielsen–Chuang, eq. (5.24)). -/
theorem semiclassical_outcomeProb_eq {U : Matrix (Fin m) (Fin m) ℂ} {u : Fin m → ℂ}
    (hu : star u ⬝ᵥ u = 1) {φ : ℝ} (huφ : U *ᵥ u = exp (2 * Real.pi * I * φ) • u)
    (k : Fin (2 ^ t)) :
    (semiclassical t m).outcomeProb (Interpretation.sum KrausGate.ev (Oracle.ev (controlled U)))
      (semiclassicalReadout t m) (vecMulVec (input t m u) (star (input t m u))) k =
      ‖amplitude t φ k‖ ^ 2 :=
  Circuit.outcomeProb_of_bijective _ _ semiclassicalReadout_bijective
    (f := fun k ↦ ‖amplitude t φ k‖ ^ 2) (prob_semiclassical hu huφ) k

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
      (fun _ _ L ↦ L.cellCost fun _ _ _ g ↦ Oracle.callCount g) = 0 := fun l b ↦ by
    refine Circuit.queryCount_eq_zero ?_
    induction l generalizing b with
    | nil => trivial
    | cons j l ih => exact ⟨Layer.cellCost_single _ _ _, fun _ ↦ ih _⟩
  rw [Circuit.queryCount, Circuit.total_comp_of_isUnbranched _ isUnbranched_prepare
    ⟨nonempty_unique_index_prepare.some.default⟩, h, add_zero, ← Circuit.queryCount,
    queryCount_prepare]

end PhaseEstimation

end QuantumCircuit
