/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import QICLean.Circuit.Protocol.GHZ

/-!
# Weighted GHZ vectors and separated correlations

In the GHZ-type vector `|χ⟩ = ∑ⱼ αⱼ |j⟩^{⊗ι}`, an operator supported on a region that leaves one
site unobserved has no matrix element between two different constant configurations, so its
expectation is the classical average `∑ⱼ |αⱼ|² ⟨j…j|A|j…j⟩` of its expectations in the branches.
For the weighted binary GHZ vector `a|0…0⟩ + b|1…1⟩` with `|a|² + |b|² = 1`, the connected
correlation of operators on disjoint regions that leave one site unobserved is
`|a|² |b|² (A₀ - A₁)(B₀ - B₁)`, with `A_s = ⟨s…s|A|s…s⟩`, of modulus at most `4 |a|² |b|²` for
unitary operators. After a unitary circuit of depth `T` the same bound holds for operators whose
`T`-fold neighbourhoods are disjoint and leave one site unobserved: the circuit moves the
operators inside these neighbourhoods. A weighted GHZ vector with `|a|² |b|²` bounded away from
`1/4` therefore cannot be carried close to the balanced one by a shallow circuit.

The expectation `⟨ψ|A|ψ⟩` is written `star ψ ⬝ᵥ (A *ᵥ ψ)`.

## Main results

* `QuantumCircuit.norm_ghzState_sq` — `‖χ‖² = ∑ⱼ |αⱼ|²`.
* `QuantumCircuit.dotProduct_ghzState_diagonal_mulVec`,
  `QuantumCircuit.dotProduct_ghzState_mulVec_of_mem_supportedOperators` — the classical
  expectations of diagonal operators and of operators leaving a site unobserved.
* `QuantumCircuit.covariance_ghzState_two`, `QuantumCircuit.norm_covariance_ghzState_two_le` —
  the separated correlations of a weighted binary GHZ vector.
* `QuantumCircuit.norm_covariance_mulVec_ghzState_two_le` — the same bound after a unitary
  circuit of depth `T`.

The declarations restate `TNLean/Circuit/WeightedGHZ.lean` at commit `414a18fb88` (Apache-2.0).
The changes: any finite set of sites in place of a chain, and any finite basis for the
expectations, which are written `star ψ ⬝ᵥ (A *ᵥ ψ)`; the shallow circuits are
`QuantumCircuit.IsUnitaryCircuit` on any geometry whose cells have positive cost, with the
separation of the observables stated as disjoint `T`-fold neighbourhoods; the binary
decomposition, the norm and the scaling of the binary vector are the cases `β = Fin 2` of
`QuantumCircuit.ghzState_eq_sum`, `QuantumCircuit.norm_ghzState_sq` and
`QuantumCircuit.ghzState_smul`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), Supplemental Material, proof of Theorem 1
  (connected correlations of vectors prepared by circuits of depth `T`).
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), Example 1 (the GHZ state needs a depth growing
  with the system size).
-/

open Matrix ManyBody

namespace QuantumCircuit

section Expectation

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

/-- The expectation in `|χ⟩` of an operator with no matrix element between two different
constant configurations is the classical average of its branch expectations. -/
private theorem dotProduct_ghzState_mulVec (α : β → ℂ) {A : Matrix (ι → β) (ι → β) ℂ}
    (hA : ∀ i j, i ≠ j → A (fun _ ↦ i) (fun _ ↦ j) = 0) :
    star (ghzState α) ⬝ᵥ (A *ᵥ ghzState α) =
      ∑ j, star (α j) * α j * A (fun _ ↦ j) (fun _ ↦ j) := by
  rw [ghzState_eq_sum, star_sum, mulVec_sum, sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dotProduct_sum, Finset.sum_eq_single i]
  · rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, ← Pi.single_star, star_one,
      single_dotProduct, mulVec_single, one_mul]
    simp only [MulOpposite.op_one, one_smul, col_apply, smul_eq_mul, Complex.star_def]
    ring
  · intro j _ hj
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, ← Pi.single_star, star_one,
      single_dotProduct, mulVec_single]
    simp [hA i j (Ne.symm hj)]
  · simp

/-- The expectation in `|χ⟩` of a diagonal operator is the average of its values at the constant
configurations, weighted by `|αⱼ|²`. -/
theorem dotProduct_ghzState_diagonal_mulVec [Nonempty ι] (α : β → ℂ) (f : (ι → β) → ℂ) :
    star (ghzState α) ⬝ᵥ (diagonal f *ᵥ ghzState α) =
      ∑ j, star (α j) * α j * f (fun _ ↦ j) := by
  rw [dotProduct_ghzState_mulVec α fun i j hij ↦
    diagonal_apply_ne _ fun h ↦ hij (congrFun h (Classical.arbitrary ι))]
  simp

/-- **Classical expectations in a GHZ-type vector.** If `A` is supported on a region that leaves
a site unobserved, its expectation in `|χ⟩` is `∑ⱼ |αⱼ|² ⟨j…j|A|j…j⟩`: the unobserved site removes
the matrix elements between different branches. -/
theorem dotProduct_ghzState_mulVec_of_mem_supportedOperators {S : Finset ι} (α : β → ℂ)
    {A : Matrix (ι → β) (ι → β) ℂ} (hA : A ∈ supportedOperators (fun _ : ι ↦ β) S)
    (hS : ∃ k, k ∉ S) :
    star (ghzState α) ⬝ᵥ (A *ᵥ ghzState α) =
      ∑ j, star (α j) * α j * A (fun _ ↦ j) (fun _ ↦ j) :=
  let ⟨_, hk⟩ := hS
  dotProduct_ghzState_mulVec α fun _ _ hij ↦ apply_eq_zero_of_mem_supportedOperators hA hk hij

/-- The squared norm of `|χ⟩` on a nonempty set of sites is `∑ⱼ |αⱼ|²`. -/
theorem norm_ghzState_sq [Nonempty ι] (α : β → ℂ) :
    ‖(WithLp.toLp 2 (ghzState α) : EuclideanSpace ℂ (ι → β))‖ ^ 2 = ∑ j, ‖α j‖ ^ 2 := by
  have h := dotProduct_ghzState_diagonal_mulVec (ι := ι) α fun _ ↦ 1
  rw [diagonal_one, one_mulVec] at h
  rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
    dotProduct_comm, h]
  simp only [mul_one, Complex.star_def, Complex.conj_mul']
  norm_cast

end Expectation

/-! ### Weighted binary GHZ vectors -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The two constant binary configurations differ on a nonempty set of sites. -/
private theorem const_zero_ne_one [Nonempty ι] :
    (fun _ : ι ↦ (0 : Fin 2)) ≠ fun _ ↦ 1 :=
  fun h ↦ zero_ne_one (congrFun h (Classical.arbitrary ι))

/-- The expectation in `a|0…0⟩ + b|1…1⟩` of an operator leaving a site unobserved. -/
private theorem dotProduct_ghzState_two_mulVec {S : Finset ι} (a b : ℂ)
    {A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ} (hA : A ∈ supportedOperators (fun _ : ι ↦ Fin 2) S)
    (hS : ∃ k, k ∉ S) :
    star (ghzState ![a, b]) ⬝ᵥ (A *ᵥ ghzState ![a, b]) =
      star a * a * A (fun _ ↦ 0) (fun _ ↦ 0) + star b * b * A (fun _ ↦ 1) (fun _ ↦ 1) := by
  rw [dotProduct_ghzState_mulVec_of_mem_supportedOperators _ hA hS, Fin.sum_univ_two]
  rfl

/-- **Separated correlations in a weighted binary GHZ vector.** For `|a|² + |b|² = 1` and
operators `A`, `B` on disjoint regions that leave a site unobserved, the connected correlation
in `a|0…0⟩ + b|1…1⟩` is `|a|² |b|² (A₀ - A₁)(B₀ - B₁)`, with `A_s = ⟨s…s|A|s…s⟩`. -/
theorem covariance_ghzState_two {S S' : Finset ι} (hSS' : Disjoint S S')
    (hcover : ∃ k, k ∉ S ∪ S') {a b : ℂ} (hab : star a * a + star b * b = 1)
    {A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : A ∈ supportedOperators (fun _ : ι ↦ Fin 2) S)
    (hB : B ∈ supportedOperators (fun _ : ι ↦ Fin 2) S') :
    star (ghzState ![a, b]) ⬝ᵥ ((A * B) *ᵥ ghzState ![a, b]) -
        (star (ghzState ![a, b]) ⬝ᵥ (A *ᵥ ghzState ![a, b])) *
          (star (ghzState ![a, b]) ⬝ᵥ (B *ᵥ ghzState ![a, b])) =
      star a * a * (star b * b) * (A (fun _ ↦ 0) (fun _ ↦ 0) - A (fun _ ↦ 1) (fun _ ↦ 1)) *
        (B (fun _ ↦ 0) (fun _ ↦ 0) - B (fun _ ↦ 1) (fun _ ↦ 1)) := by
  have hAu : A ∈ supportedOperators (fun _ : ι ↦ Fin 2) (S ∪ S') :=
    supportedOperators_mono Finset.subset_union_left hA
  have hBu : B ∈ supportedOperators (fun _ : ι ↦ Fin 2) (S ∪ S') :=
    supportedOperators_mono Finset.subset_union_right hB
  have hAB (c : ι → Fin 2) : (A * B) c c = A c c * B c c := by
    rw [mul_apply_of_mem_supportedOperators_of_disjoint hA hB hSS']
    simp only [ite_self]
  rw [dotProduct_ghzState_two_mulVec a b (mul_mem hAu hBu) hcover,
    dotProduct_ghzState_two_mulVec a b hAu hcover, dotProduct_ghzState_two_mulVec a b hBu hcover,
    hAB, hAB]
  linear_combination
    -(star a * a * A (fun _ ↦ 0) (fun _ ↦ 0) * B (fun _ ↦ 0) (fun _ ↦ 0) +
      star b * b * A (fun _ ↦ 1) (fun _ ↦ 1) * B (fun _ ↦ 1) (fun _ ↦ 1)) * hab

/-- **The correlation bound for a weighted binary GHZ vector.** For `|a|² + |b|² = 1` and unitary
operators `A`, `B` on disjoint regions that leave a site unobserved, the connected correlation in
`a|0…0⟩ + b|1…1⟩` has modulus at most `4 |a|² |b|²`. -/
theorem norm_covariance_ghzState_two_le {S S' : Finset ι} (hSS' : Disjoint S S')
    (hcover : ∃ k, k ∉ S ∪ S') {a b : ℂ} (hab : star a * a + star b * b = 1)
    {A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hA : A ∈ supportedOperators (fun _ : ι ↦ Fin 2) S)
    (hB : B ∈ supportedOperators (fun _ : ι ↦ Fin 2) S')
    (hAu : A ∈ unitaryGroup (ι → Fin 2) ℂ) (hBu : B ∈ unitaryGroup (ι → Fin 2) ℂ) :
    ‖star (ghzState ![a, b]) ⬝ᵥ ((A * B) *ᵥ ghzState ![a, b]) -
        (star (ghzState ![a, b]) ⬝ᵥ (A *ᵥ ghzState ![a, b])) *
          (star (ghzState ![a, b]) ⬝ᵥ (B *ᵥ ghzState ![a, b]))‖ ≤ 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have hdiff (C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (hC : C ∈ unitaryGroup (ι → Fin 2) ℂ) :
      ‖C (fun _ ↦ 0) (fun _ ↦ 0) - C (fun _ ↦ 1) (fun _ ↦ 1)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      linarith [entry_norm_bound_of_unitary hC (fun _ ↦ 0) (fun _ ↦ 0),
        entry_norm_bound_of_unitary hC (fun _ ↦ 1) (fun _ ↦ 1)])
  rw [covariance_ghzState_two hSS' hcover hab hA hB]
  simp only [norm_mul, norm_star]
  calc
    _ ≤ ‖a‖ * ‖a‖ * (‖b‖ * ‖b‖) * 2 * 2 := by
      gcongr
      · exact hdiff A hAu
      · exact hdiff B hBu
    _ = 4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by ring

/-- **The correlation bound after a shallow circuit.** On a geometry whose cells have positive
cost, let `U` be a unitary circuit of depth at most `T`, and let `A`, `B` be unitary operators on
regions whose `T`-fold neighbourhoods are disjoint and leave a site unobserved. For
`|a|² + |b|² = 1`, the connected correlation of `A` and `B` in `U (a|0…0⟩ + b|1…1⟩)` has modulus
at most `4 |a|² |b|²`: the circuit moves `A` and `B` into the neighbourhoods.

Source: arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (the light cone of a
circuit of depth `T`); arXiv:2103.13367, Example 1. -/
theorem norm_covariance_mulVec_ghzState_two_le {Γ : Geometry ι} [Fintype Γ.Cell]
    (hpos : ∀ c, 0 < Γ.cost c) {T : ℕ} {U A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ}
    (hU : IsUnitaryCircuit Γ T U) {R R' : Finset ι}
    (hRR' : Disjoint (Γ.neighbourhood^[T] R) (Γ.neighbourhood^[T] R'))
    (hcover : ∃ k, k ∉ Γ.neighbourhood^[T] R ∪ Γ.neighbourhood^[T] R')
    (hA : A ∈ supportedOperators (fun _ : ι ↦ Fin 2) R)
    (hB : B ∈ supportedOperators (fun _ : ι ↦ Fin 2) R')
    (hAu : A ∈ unitaryGroup (ι → Fin 2) ℂ) (hBu : B ∈ unitaryGroup (ι → Fin 2) ℂ)
    {a b : ℂ} (hab : star a * a + star b * b = 1) :
    ‖star (U *ᵥ ghzState ![a, b]) ⬝ᵥ ((A * B) *ᵥ (U *ᵥ ghzState ![a, b])) -
        (star (U *ᵥ ghzState ![a, b]) ⬝ᵥ (A *ᵥ (U *ᵥ ghzState ![a, b]))) *
          (star (U *ᵥ ghzState ![a, b]) ⬝ᵥ (B *ᵥ (U *ᵥ ghzState ![a, b])))‖ ≤
      4 * ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  have hconj (C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (ψ : (ι → Fin 2) → ℂ) :
      star (U *ᵥ ψ) ⬝ᵥ (C *ᵥ (U *ᵥ ψ)) = star ψ ⬝ᵥ ((Uᴴ * C * U) *ᵥ ψ) := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  have hunit : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU.mem_unitaryGroup
  have hAB : Uᴴ * (A * B) * U = (Uᴴ * A * U) * (Uᴴ * B * U) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc U Uᴴ, hunit, Matrix.one_mul]
  have hUu : Uᴴ ∈ unitaryGroup (ι → Fin 2) ℂ := by
    rw [← star_eq_conjTranspose]
    exact Unitary.star_mem hU.mem_unitaryGroup
  rw [hconj, hconj, hconj, hAB]
  exact norm_covariance_ghzState_two_le hRR' hcover hab
    (hU.conjTranspose_mul_mul_mem_supportedOperators hpos hA)
    (hU.conjTranspose_mul_mul_mem_supportedOperators hpos hB)
    (mul_mem (mul_mem hUu hAu) hU.mem_unitaryGroup) (mul_mem (mul_mem hUu hBu) hU.mem_unitaryGroup)

end QuantumCircuit
