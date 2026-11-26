/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.Hermitian.OrthogonalProjection
import QICLean.Channel.Basic
import QICLean.Channel.Semigroup.CPClosure
import QICLean.Channel.Dilation.Stinespring
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import QICLean.Algebra.Unitary.MatrixGramUnitary

/-!
# POVMs, instruments, and the Naimark dilation (Wolf Section 2.1, Theorem 2.6 / Neumark)

This file defines positive operator-valued measures (POVMs) on `M_D(ℂ)`,
quantum instruments, and proves the **Naimark extension theorem**: every
finite-outcome POVM can be realised as a projective measurement on a
larger (dilated) Hilbert space via an isometry (Wolf Eq. (2.16)).

## Main definitions

* `POVM D n` — a family of `n` positive-semidefinite `D × D` operators
  summing to the identity (resolution of identity).
* `POVM.naimarkKraus` — a Kraus-type square root `M i` with `E i = (M i)ᴴ * M i`,
  obtained from `CStarAlgebra.nonneg_iff_eq_star_mul_self`.
* `POVM.naimarkIsometry` — the isometry `V : ℂ^D → ℂ^D ⊗ ℂ^n` built from
  the Kraus square roots via the Stinespring pattern.
* `POVM.naimarkProjection i` — the orthogonal projector
  `P_i = 1_D ⊗ |i⟩⟨i|` on the dilated space.
* `Instrument D n` — a family of CP maps whose sum is trace-preserving.

## Main results

* `POVM.naimarkIsometry_isometry` — `Vᴴ * V = 𝟙`.
* `POVM.naimarkProjection_sum_eq_one` — `∑ᵢ P_i = 𝟙` on the dilation.
* `POVM.naimarkProjection_mul_self` — `P_i * P_i = P_i`.
* `POVM.naimarkProjection_hermitian` — `P_iᴴ = P_i`.
* `POVM.naimarkProjection_orthogonal` — `P_i * P_j = 0` for `i ≠ j`.
* `POVM.naimark_recovers_povm` — `Vᴴ * P_i * V = E_i` (main Naimark identity).
* `POVM.exists_naimark_dilation` — the existential form of Wolf Theorem 2.6.
* `POVM.ofPSDResolutionOfIdentity` — converse direction: every isometry together
  with a PSD resolution of identity on the dilated space yields a POVM via
  `E_i := Vᴴ P_i V`.
* `projectivePOVM_pinching` — Wolf Eq. (8.56), the projective pinching inequality.
* `POVM.exists_orthonormal_basis_restriction`,
  `POVM.exists_orthonormal_basis_restriction_of_rank_one`: sharp rank-one Naimark extension (Wolf
  lines 480--499).

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 2.6
  (Neumark's theorem) and Chapter 8, Eq. (8.56)][Wolf2012QChannels]
-/

section Basic

open scoped Matrix MatrixOrder ComplexOrder
open Matrix Finset BigOperators

variable {D n : ℕ}

/-! ### Positive operator-valued measures -/

/-- A **POVM** with `n` outcomes on `M_D(ℂ)`:
a family of positive-semidefinite operators summing to the identity. -/
structure POVM (D n : ℕ) where
  /-- The `n` positive-semidefinite effect operators. -/
  ops : Fin n → Matrix (Fin D) (Fin D) ℂ
  /-- Each effect operator is positive semidefinite. -/
  posSemidef : ∀ i, (ops i).PosSemidef
  /-- Resolution of the identity: the effects sum to `𝟙`. -/
  sum_eq_one : ∑ i, ops i = (1 : Matrix (Fin D) (Fin D) ℂ)

namespace POVM

variable (E : POVM D n)

/-- The Kraus-type square root of each POVM effect: an operator `M i`
satisfying `E i = (M i)ᴴ * M i`, chosen by `CStarAlgebra.nonneg_iff_eq_star_mul_self`. -/
noncomputable def naimarkKraus (i : Fin n) : Matrix (Fin D) (Fin D) ℂ :=
  Classical.choose
    (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (E.posSemidef i).nonneg)

/-- Defining property of `naimarkKraus`: `E i = (M i)ᴴ * M i`. -/
theorem naimarkKraus_spec (i : Fin n) :
    E.ops i = (E.naimarkKraus i)ᴴ * E.naimarkKraus i := by
  have h := Classical.choose_spec
    (CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (E.posSemidef i).nonneg)
  simpa [naimarkKraus, Matrix.star_eq_conjTranspose] using h

/-- `∑ᵢ (M i)ᴴ * M i = 𝟙` — the normalization condition on the Kraus square roots,
equivalent to the resolution of the identity for the POVM. -/
theorem sum_naimarkKraus_conjTranspose_mul :
    ∑ i, (E.naimarkKraus i)ᴴ * E.naimarkKraus i =
      (1 : Matrix (Fin D) (Fin D) ℂ) := by
  have : ∑ i, (E.naimarkKraus i)ᴴ * E.naimarkKraus i = ∑ i, E.ops i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    exact (E.naimarkKraus_spec i).symm
  rw [this, E.sum_eq_one]

/-! ### Naimark isometry -/

/-- The **Naimark isometry** `V : ℂ^D → ℂ^D ⊗ ℂ^n` attached to the POVM,
built from the Kraus square roots via the Stinespring pattern:
`V (k, i) j = (M i)_{k, j}`. -/
noncomputable def naimarkIsometry :
    Matrix (Fin D × Fin n) (Fin D) ℂ :=
  stinespringV E.naimarkKraus

/-- `Vᴴ * V = 𝟙`: the Naimark isometry is indeed an isometry. -/
theorem naimarkIsometry_isometry :
    (E.naimarkIsometry)ᴴ * E.naimarkIsometry =
      (1 : Matrix (Fin D) (Fin D) ℂ) := by
  rw [naimarkIsometry, stinespringV_conjTranspose_mul]
  exact E.sum_naimarkKraus_conjTranspose_mul

/-! ### Naimark projective measurement -/

/-- The `i`-th **Naimark projector** on the dilated space
`ℂ^D ⊗ ℂ^n`: `P_i = 𝟙_D ⊗ |i⟩⟨i|`, defined entrywise by
`P_i ((a, b), (c, d)) = δ_{a, c} · δ_{b, i} · δ_{d, i}`. -/
noncomputable def naimarkProjection (i : Fin n) :
    Matrix (Fin D × Fin n) (Fin D × Fin n) ℂ :=
  fun (p : Fin D × Fin n) (q : Fin D × Fin n) =>
    if p.1 = q.1 ∧ p.2 = i ∧ q.2 = i then 1 else 0

@[simp]
theorem naimarkProjection_apply (i : Fin n)
    (a c : Fin D) (b d : Fin n) :
    naimarkProjection (D := D) i (a, b) (c, d) =
      if a = c ∧ b = i ∧ d = i then 1 else 0 := rfl

/-- Naimark projectors are Hermitian. -/
theorem naimarkProjection_hermitian (i : Fin n) :
    (naimarkProjection (D := D) i)ᴴ = naimarkProjection i := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.conjTranspose_apply, naimarkProjection_apply]
  by_cases hca : c = a
  · by_cases hdi : d = i
    · by_cases hbi : b = i
      · subst hca hdi hbi; simp
      · simp [hdi, hbi]
    · by_cases hbi : b = i
      · simp [hdi, hbi]
      · simp [hdi, hbi]
  · have hac : a ≠ c := fun h => hca h.symm
    simp [hca, hac]

/-- Naimark projectors are idempotent: `P_i * P_i = P_i`. -/
theorem naimarkProjection_mul_self (i : Fin n) :
    naimarkProjection (D := D) i * naimarkProjection i =
      naimarkProjection i := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, naimarkProjection_apply, Fintype.sum_prod_type]
  by_cases hbi : b = i
  · by_cases hdi : d = i
    · rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single i]
        · by_cases hac : a = c
          · subst hac; simp [hbi, hdi]
          · simp [hac, hbi, hdi]
        · intro b' _ hb'i
          simp [hb'i]
        · intro h; exact absurd (Finset.mem_univ i) h
      · intro a' _ ha'a
        refine Finset.sum_eq_zero ?_
        intro b' _
        simp [Ne.symm ha'a]
      · intro h; exact absurd (Finset.mem_univ a) h
    · have hfalse : ¬(a = c ∧ b = i ∧ d = i) := fun ⟨_, _, h⟩ => hdi h
      rw [ite_eq_right hfalse]
      refine Finset.sum_eq_zero fun a' _ => ?_
      refine Finset.sum_eq_zero fun b' _ => ?_
      by_cases hb'i : b' = i
      · simp [hb'i, hdi]
      · simp [hb'i]
  · have hfalse : ¬(a = c ∧ b = i ∧ d = i) := fun ⟨_, h, _⟩ => hbi h
    rw [ite_eq_right hfalse]
    refine Finset.sum_eq_zero fun a' _ => ?_
    refine Finset.sum_eq_zero fun b' _ => ?_
    simp [hbi]

/-- Distinct Naimark projectors are orthogonal: `P_i * P_j = 0` if `i ≠ j`. -/
theorem naimarkProjection_orthogonal (i j : Fin n) (hij : i ≠ j) :
    naimarkProjection (D := D) i * naimarkProjection j = 0 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.mul_apply, naimarkProjection_apply, Fintype.sum_prod_type,
    Matrix.zero_apply]
  refine Finset.sum_eq_zero ?_
  intro a' _
  refine Finset.sum_eq_zero ?_
  intro b' _
  -- Either the first factor vanishes (b' ≠ i) or the second vanishes (b' ≠ j);
  -- these two conditions can never both fail because i ≠ j.
  by_cases hb'i : b' = i
  · have hb'j : b' ≠ j := hb'i ▸ hij
    simp [hb'j]
  · simp [hb'i]

/-- The Naimark projectors sum to the identity: `∑ᵢ P_i = 𝟙`. -/
theorem naimarkProjection_sum_eq_one :
    ∑ i : Fin n, naimarkProjection (D := D) i =
      (1 : Matrix (Fin D × Fin n) (Fin D × Fin n) ℂ) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  rw [Matrix.sum_apply]
  simp only [naimarkProjection_apply]
  by_cases hbd : b = d
  · subst hbd
    by_cases hac : a = c
    · subst hac
      rw [Finset.sum_eq_single b]
      · simp
      · intro j _ hjb
        simp [Ne.symm hjb]
      · intro h
        exact absurd (Finset.mem_univ b) h
    · rw [Matrix.one_apply_ne (by simp [hac])]
      refine Finset.sum_eq_zero ?_
      intro j _
      simp [hac]
  · rw [Matrix.one_apply_ne (by simp [hbd])]
    refine Finset.sum_eq_zero ?_
    intro j _
    by_cases hbj : b = j
    · by_cases hdj : d = j
      · exact absurd (hbj.trans hdj.symm) hbd
      · simp [hbj, hdj]
    · simp [hbj]

/-! ### Naimark theorem: `Vᴴ * P_i * V = E_i` -/

/-- **Wolf Theorem 2.6 (Naimark / Neumark)**: every POVM `{E_i}` on `ℂ^D` arises
as `E_i = Vᴴ * P_i * V` for an isometry `V : ℂ^D → ℂ^D ⊗ ℂ^n` and a projective
measurement `{P_i}` on the dilated space. -/
theorem naimark_recovers_povm (i : Fin n) :
    (E.naimarkIsometry)ᴴ * naimarkProjection (D := D) i *
        E.naimarkIsometry = E.ops i := by
  rw [E.naimarkKraus_spec i]
  ext k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    naimarkIsometry, stinespringV_apply,
    naimarkProjection_apply, Fintype.sum_prod_type]
  -- LHS: ∑ q1, ∑ q2, (∑ p1, ∑ p2, star(K p2 p1 k) *
  --                                  [p1=q1 ∧ p2=i ∧ q2=i]) * K q2 q1 l
  -- RHS: ∑ a, star(K i a k) * K i a l
  refine Finset.sum_congr rfl ?_
  intro q1 _
  rw [Finset.sum_eq_single i]
  · -- q2 = i: peel inner p1 = q1, then p2 = i.
    rw [Finset.sum_eq_single q1]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro p2 _ hp2; simp [hp2]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro p1 _ hp1
      refine Finset.sum_eq_zero fun p2 _ => ?_
      simp [hp1]
    · intro h; exact absurd (Finset.mem_univ q1) h
  · -- q2 ≠ i: the inner sum is 0, so the product with `K q2 q1 l` is 0.
    intro q2 _ hq2
    have hinner : (∑ p1 : Fin D, ∑ p2 : Fin n,
        star (E.naimarkKraus p2 p1 k) *
          (if p1 = q1 ∧ p2 = i ∧ q2 = i then (1 : ℂ) else 0)) = 0 := by
      refine Finset.sum_eq_zero fun p1 _ => ?_
      refine Finset.sum_eq_zero fun p2 _ => ?_
      rw [ite_eq_right (fun h => hq2 h.2.2)]
      ring
    rw [hinner, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Existential form of Wolf Theorem 2.6**: Naimark dilation exists for every POVM.
The witnesses `(P i)` form a full projective measurement on the dilation: each is
self-adjoint and idempotent, pairwise orthogonal, and they sum to the identity. -/
theorem exists_naimark_dilation :
    ∃ (r : ℕ) (V : Matrix (Fin D × Fin r) (Fin D) ℂ)
      (P : Fin n → Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Vᴴ * V = 1 ∧
      (∀ i, P i * P i = P i) ∧
      (∀ i, (P i)ᴴ = P i) ∧
      (∀ i j, i ≠ j → P i * P j = 0) ∧
      (∑ i, P i = 1) ∧
      (∀ i, Vᴴ * P i * V = E.ops i) :=
  ⟨n, E.naimarkIsometry, naimarkProjection, E.naimarkIsometry_isometry,
    naimarkProjection_mul_self, naimarkProjection_hermitian,
    naimarkProjection_orthogonal,
    naimarkProjection_sum_eq_one, E.naimark_recovers_povm⟩

end POVM

/-! ### Converse: PSD resolutions of identity on a dilation give POVMs -/

namespace POVM

/-- **Converse of Naimark (PSD resolution of identity)**: given an isometry
`V : ℂ^D → ℂ^d'` and a family of positive semidefinite operators `{P_i}` on the
dilated space summing to the identity, the pulled-back operators
`E_i := Vᴴ * P_i * V` form a POVM. A projective measurement on the dilation is
a special case (see `POVM.naimark_recovers_povm` for the canonical Naimark
instance); the statement here requires only the PSD/sum-to-one structure that
the proof actually uses. -/
noncomputable def ofPSDResolutionOfIdentity {D n d' : ℕ}
    (V : Matrix (Fin d') (Fin D) ℂ) (hV : Vᴴ * V = 1)
    (P : Fin n → Matrix (Fin d') (Fin d') ℂ)
    (hPsum : ∑ i, P i = 1)
    (hPpos : ∀ i, (P i).PosSemidef) :
    POVM D n where
  ops i := Vᴴ * P i * V
  posSemidef i := by
    -- Vᴴ * (P i) * V = Vᴴ * (P i) * (Vᴴᴴ); apply PSD-sandwich with B := Vᴴ.
    have := (hPpos i).mul_mul_conjTranspose_same (B := Vᴴ)
    simpa [Matrix.mul_assoc] using this
  sum_eq_one := by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hPsum, Matrix.mul_one]
    exact hV

end POVM

/-! ### Quantum instruments -/

/-- A **quantum instrument** with `n` outcomes: a family of completely positive
maps whose sum is a quantum channel (trace-preserving). The `i`-th component
implements the (unnormalised) post-measurement update for outcome `i`. -/
structure Instrument (D n : ℕ) where
  /-- The `n` completely-positive component maps. -/
  maps : Fin n → Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ
  /-- Each component map is completely positive. -/
  cp : ∀ i, IsCPMap (maps i)
  /-- The sum of the component maps is trace-preserving. -/
  tp : IsTracePreservingMap (∑ i, maps i)

namespace Instrument

variable (I : Instrument D n)

/-- The overall quantum channel `∑ᵢ Φᵢ` obtained by averaging over outcomes. -/
noncomputable def total :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ i, I.maps i

/-- The average map of an instrument is a quantum channel (CPTP). -/
theorem total_isChannel : IsChannel I.total := by
  refine ⟨?_, I.tp⟩
  exact Finset.isCPMap_sum (n := Fin D) Finset.univ I.maps (fun i _ => I.cp i)

/-- The (unnormalised) **post-measurement state update** after outcome `i`:
`ρ ↦ Φ_i(ρ)`. The physical normalised state is `Φ_i(ρ) / tr(Φ_i(ρ))`
(see `Instrument.probability` and `Instrument.posteriorState`). -/
noncomputable def update (i : Fin n) (rho : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  I.maps i rho

/-- The probability of observing outcome `i` in state `ρ`: `tr(Φ_i(ρ))`. -/
noncomputable def probability (i : Fin n) (rho : Matrix (Fin D) (Fin D) ℂ) :
    ℂ :=
  Matrix.trace (I.maps i rho)

/-- **Conservation of probability**: for any state `ρ`, the outcome probabilities
sum to `tr(ρ)`. -/
theorem sum_probability (rho : Matrix (Fin D) (Fin D) ℂ) :
    ∑ i, I.probability i rho = Matrix.trace rho := by
  simp only [probability, ← Matrix.trace_sum]
  have : (∑ i, I.maps i) rho = ∑ i, I.maps i rho := by
    simp [Finset.sum_apply]
  rw [← this, I.tp rho]

/-- Outcome probabilities are non-negative real numbers (in `ℂ` with
`ComplexOrder`): for any PSD state `ρ`, `0 ≤ I.probability i rho`. -/
theorem probability_nonneg (i : Fin n) {rho : Matrix (Fin D) (Fin D) ℂ}
    (hrho : rho.PosSemidef) : 0 ≤ I.probability i rho :=
  ((I.cp i).isPositiveMap rho hrho).trace_nonneg

/-- The physical **post-measurement state** after outcome `i`: the component
update normalised by the outcome probability. Only meaningful when the
probability is nonzero. -/
noncomputable def posteriorState (i : Fin n)
    (rho : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  (I.probability i rho)⁻¹ • I.maps i rho

end Instrument

/-! ### Projective pinching inequality (Wolf Eq. (8.56)) -/

/-- Algebraic identity behind the projective pinching inequality:
`∑_{i,j} (P_i - P_j) ρ (P_i - P_j) = 2 (k T(ρ) - ρ)` where `T(ρ) = ∑_i P_i ρ P_i`. -/
private lemma pinching_difference_identity {D k : ℕ}
    (ρ : Matrix (Fin D) (Fin D) ℂ)
    (P : Fin k → Matrix (Fin D) (Fin D) ℂ)
    (hPsum : ∑ i : Fin k, P i = 1) :
    (∑ i : Fin k, ∑ j : Fin k, (P i - P j) * ρ * (P i - P j)) =
      (2 : ℂ) • ((k : ℂ) • (∑ i : Fin k, P i * ρ * P i) - ρ) := by
  have h_cross : (∑ i : Fin k, ∑ j : Fin k, P i * ρ * P j) = ρ := by
    calc
      _ = (∑ i : Fin k, P i * ρ) * (∑ j : Fin k, P j) := by
        simpa only [Matrix.mul_assoc] using
          (Finset.sum_mul_sum Finset.univ Finset.univ (fun i ↦ P i * ρ) P).symm
      _ = ((∑ i : Fin k, P i) * ρ) * (∑ j : Fin k, P j) := by
        congr 1
        exact (Finset.sum_mul Finset.univ P ρ).symm
      _ = ρ := by rw [hPsum, Matrix.one_mul, Matrix.mul_one]
  have h_cross' : (∑ i : Fin k, ∑ j : Fin k, P j * ρ * P i) = ρ := by
    rw [Finset.sum_comm]
    exact h_cross
  have h_diag :
      (∑ i : Fin k, ∑ _j : Fin k, P i * ρ * P i) =
        (k : ℂ) • (∑ i : Fin k, P i * ρ * P i) := by
    simp only [Finset.sum_const, Finset.card_fin]
    simp_rw [← Nat.cast_smul_eq_nsmul ℂ k]
    rw [Finset.smul_sum]
  have h_diag' :
      (∑ _i : Fin k, ∑ j : Fin k, P j * ρ * P j) =
        (k : ℂ) • (∑ i : Fin k, P i * ρ * P i) := by
    rw [Finset.sum_comm]; exact h_diag
  calc
    (∑ i : Fin k, ∑ j : Fin k, (P i - P j) * ρ * (P i - P j)) =
        ∑ i : Fin k, ∑ j : Fin k,
          (P i * ρ * P i + P j * ρ * P j - P i * ρ * P j - P j * ρ * P i) := by
      refine Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => ?_
      noncomm_ring
    _ = (∑ i : Fin k, ∑ _j : Fin k, P i * ρ * P i) +
          (∑ _i : Fin k, ∑ j : Fin k, P j * ρ * P j) -
          (∑ i : Fin k, ∑ j : Fin k, P i * ρ * P j) -
          (∑ i : Fin k, ∑ j : Fin k, P j * ρ * P i) := by
      simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by rw [h_diag, h_diag', h_cross, h_cross']; module

/-- **Wolf Eq. (8.56): projective pinching inequality.**
Let `ρ` be a density operator on `M_D(ℂ)` and `{P_i}_{i = 1,…,k}` a
projective POVM (each `P_i` is an orthogonal projection and they sum to
the identity).  Define the pinching map `T(ρ) := ∑_i P_i ρ P_i`.
Then `ρ ≤ k · T(ρ)` in the PSD order.

Source: M. Wolf, *Quantum Channels & Operations: Guided Tour*, Eq. (8.56);
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`, lines 681–700. -/
theorem projectivePOVM_pinching {D k : ℕ}
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ_dm : ρ ∈ densityMatrices D)
    (P : Fin k → Matrix (Fin D) (Fin D) ℂ)
    (hPproj : ∀ i, IsOrthogonalProjection (P i))
    (hPsum : ∑ i : Fin k, P i = 1) :
    ρ ≤ (k : ℂ) • (∑ i : Fin k, P i * ρ * P i) := by
  rw [Matrix.le_iff]
  have hρ_psd : ρ.PosSemidef := hρ_dm.1
  have hPherm : ∀ i, (P i).IsHermitian := fun i => (hPproj i).1
  have h_identity := pinching_difference_identity ρ P hPsum
  have h_diff : (k : ℂ) • (∑ i : Fin k, P i * ρ * P i) - ρ = (2⁻¹ : ℂ) •
      (∑ i : Fin k, ∑ j : Fin k, (P i - P j) * ρ * (P i - P j)) := by
    calc
      (k : ℂ) • (∑ i : Fin k, P i * ρ * P i) - ρ =
          (2⁻¹ : ℂ) •
            ((2 : ℂ) • ((k : ℂ) • (∑ i : Fin k, P i * ρ * P i) - ρ)) := by
        simp
      _ = (2⁻¹ : ℂ) • (∑ i : Fin k, ∑ j : Fin k,
          (P i - P j) * ρ * (P i - P j)) := by rw [h_identity]
  rw [h_diff]
  -- Each summand is PSD
  have h_summand_psd : ∀ i j : Fin k,
      ((P i - P j) * ρ * (P i - P j)).PosSemidef := by
    intro i j
    have h_diff_herm : (P i - P j).IsHermitian := (hPherm i).sub (hPherm j)
    have h := hρ_psd.mul_mul_conjTranspose_same (P i - P j)
    simpa [h_diff_herm.eq] using h
  -- Sum of PSD matrices is PSD
  have h_sum_psd : (∑ i : Fin k, ∑ j : Fin k,
      (P i - P j) * ρ * (P i - P j)).PosSemidef :=
    Matrix.posSemidef_sum (Finset.univ : Finset (Fin k)) (fun i _ =>
      Matrix.posSemidef_sum (Finset.univ : Finset (Fin k)) (fun j _ => h_summand_psd i j))
  -- (1/2) · (PSD sum) is PSD because 2⁻¹ ≥ 0 in ℂ
  refine h_sum_psd.smul ?_
  have h_half_nonneg : (0 : ℂ) ≤ (2⁻¹ : ℂ) := by
    have h : (0 : ℝ) ≤ 1/2 := by norm_num
    convert RCLike.ofReal_nonneg.mpr h using 1
    norm_num
  exact h_half_nonneg

end Basic

section RankOneNaimark

/-!
## Sharp rank-one Naimark extension (Wolf lines 480--499)

This file proves the sharp rank-one form of Naimark's theorem for POVM
effects, following Wolf, *Quantum Channels & Operations*, lines 480--499
of `Notes/WolfNoteTexSource/ch02_representations.tex`.

Given `n` vectors `ψᵢ ∈ ℂᵈ` with the rank-one resolution of the identity
`∑ᵢ |ψᵢ⟩⟨ψᵢ| = 1_d`, the resolution forces `d ≤ n`, and there exists an
orthonormal basis `{φᵢ}ᵢ₌₁ⁿ` of `ℂⁿ` such that each `ψᵢ` is the restriction
of `φᵢ` to the first `d` coordinates.

### Ambient dimension

`POVM.exists_naimark_dilation` dilates a general POVM onto
`ℂ^D ⊗ ℂ^n` (dimension `D·n`).  The source asserts the sharper
`n`-dimensional ambient space for rank-one effects.  The present theorem
(`exists_orthonormal_basis_restriction`) provides the `n × n` unitary
extension directly, without the tensor-product factor.

### Main results

* `exists_orthonormal_basis_restriction` — the sharp rank-one extension:
  from `ψᵢ` on `ℂᵈ` with `∑ |ψᵢ⟩⟨ψᵢ| = 1`, derive `d ≤ n` and obtain a
  unitary `U ∈ U(n)` whose rows restrict to `ψᵢ`.
* `exists_orthonormal_basis_restriction_of_rank_one` — the rank-one POVM
  corollary: given a `POVM d n` with an explicit decomposition
  `E_i = |ψᵢ⟩⟨ψᵢ|`, apply the sharp extension.

### References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*,
  Theorem "Neumark's theorem", lines 480--499][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder
open Matrix Finset

namespace POVM

variable {d n : ℕ}

section rankOneNaimarkSharp

/-- Given a family `ψᵢ : Fin d → ℂ` of `n` vectors satisfying the
resolution of identity `∑_i |ψᵢ⟩⟨ψᵢ| = 1_d`, the `n×d` matrix
`Ψ i j := ψ i j` satisfies `Ψᴴ * Ψ = 1_d`. -/
private lemma gram_eq_one_of_vecMulVec_sum_eq_one (ψ : Fin n → (Fin d → ℂ))
    (h_sum : ∑ i : Fin n, Matrix.vecMulVec (ψ i) (star (ψ i)) = 1) :
    ((Matrix.of fun (i : Fin n) (j : Fin d) => ψ i j)ᴴ *
      (Matrix.of fun (i : Fin n) (j : Fin d) => ψ i j)) = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
  have h_entry := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M j k) h_sum
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.one_apply,
    Pi.star_apply] at h_entry
  calc
    (∑ i : Fin n, star (ψ i j) * ψ i k)
        = (∑ i : Fin n, star (ψ i j * star (ψ i k))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_mul, star_star, mul_comm]
    _ = star (∑ i : Fin n, ψ i j * star (ψ i k)) := by
      simp
    _ = star (if j = k then (1 : ℂ) else 0) := by rw [h_entry]
    _ = if j = k then (1 : ℂ) else 0 := by split <;> simp

/-- **Sharp rank-one Naimark extension** (Wolf, *Quantum Channels & Operations*,
Theorem "Neumark's theorem", lines 480--499).

Given `n` vectors `ψᵢ : Fin d → ℂ` (`i = 1,…,n`) forming a rank-one resolution
of the identity `∑ᵢ |ψᵢ⟩⟨ψᵢ| = 1_d` on `ℂᵈ`, one has `d ≤ n`, and there
exists a unitary `U ∈ U(n)` such that each `ψᵢ` is the restriction of the
`i`-th row of `U` to the first `d` coordinates.

In coordinates: `ψ i j = (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j)`.
The rows `φᵢ j := U i j` form an orthonormal basis of `ℂⁿ` (because `U`
is unitary) and each `ψᵢ` is the restriction of `φᵢ` to the embedded
subspace `ℂᵈ ⊂ ℂⁿ`.

The ambient dimension of this extension is `n` (the number of outcomes),
in contrast to `POVM.exists_naimark_dilation` which constructs an isometry
onto `ℂ^D ⊗ ℂ^n` of dimension `D·n`. -/
theorem exists_orthonormal_basis_restriction (ψ : Fin n → (Fin d → ℂ))
    (h_sum : ∑ i : Fin n, Matrix.vecMulVec (ψ i) (star (ψ i)) = 1) :
    ∃ (hd : d ≤ n) (U : Matrix.unitaryGroup (Fin n) ℂ),
      (∀ i j, (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j) = ψ i j) := by
  let Ψ : Matrix (Fin n) (Fin d) ℂ := Matrix.of fun i j => ψ i j
  have hΨGram : Ψᴴ * Ψ = 1 := by
    dsimp [Ψ]
    exact gram_eq_one_of_vecMulVec_sum_eq_one ψ h_sum
  have hinj : Function.Injective (Matrix.mulVecLin Ψ) := by
    rw [← LinearMap.ker_eq_bot,
      ← Matrix.ker_mulVecLin_conjTranspose_mul_self Ψ, hΨGram]
    simp
  have hd : d ≤ n := by
    simpa using LinearMap.finrank_le_finrank_of_injective hinj
  let J : Matrix (Fin n) (Fin d) ℂ :=
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE hd)
  have hJGram : Jᴴ * J = 1 := by
    rw [show Jᴴ = (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hd) id by
      simp [J]]
    change
      (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hd) (Equiv.refl (Fin n)) *
          (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Equiv.refl (Fin n)) (Fin.castLE hd) = 1
    rw [Matrix.submatrix_mul_equiv]
    simpa only [Matrix.one_mul] using
      Matrix.submatrix_one (α := ℂ) (Fin.castLE hd) (Fin.castLE_injective hd)
  obtain ⟨U, hU⟩ :=
    Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq Ψ J (hΨGram.trans hJGram.symm)
  have hUJ :
      (U : Matrix (Fin n) (Fin n) ℂ) * J =
        (U : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE hd) := by
    simpa [J] using
      Matrix.mul_submatrix_one (Equiv.refl (Fin n)) (Fin.castLE hd)
        (U : Matrix (Fin n) (Fin n) ℂ)
  have h_restrict (i : Fin n) (j : Fin d) :
      (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j) = ψ i j := by
    simpa [Ψ] using
      (congrArg (fun M ↦ M i j) (hU.trans hUJ)).symm
  exact ⟨hd, U, h_restrict⟩

end rankOneNaimarkSharp

/-! ### The rank-one POVM corollary -/

/-- **Rank-one POVM corollary**: start from a `POVM d n` whose effects are
explicitly given as rank-one `|ψᵢ⟩⟨ψᵢ|`.  The POVM axioms guarantee the resolution
`∑ᵢ |ψᵢ⟩⟨ψᵢ| = 1`, so `exists_orthonormal_basis_restriction` applies and
yields the sharp `n`-dimensional orthonormal-basis extension recorded in
Wolf lines 480--499.

This specializes the general POVM structure to the vector-level
hypotheses of the sharp theorem.  Unlike `exists_naimark_dilation`,
whose ambient Hilbert space is `ℂ^D ⊗ ℂ^n` (dimension `D·n`), this
corollary gives the source's assertion of an `n`-dimensional ambient
space under the rank-one hypothesis. -/
theorem exists_orthonormal_basis_restriction_of_rank_one
    (E : POVM d n) (ψ : Fin n → (Fin d → ℂ))
    (h_ops : ∀ i, E.ops i = Matrix.vecMulVec (ψ i) (star (ψ i))) :
    ∃ (hd : d ≤ n) (U : Matrix.unitaryGroup (Fin n) ℂ),
      (∀ i j, (U : Matrix (Fin n) (Fin n) ℂ) i (Fin.castLE hd j) = ψ i j) := by
  have h_sum : ∑ i : Fin n, Matrix.vecMulVec (ψ i) (star (ψ i)) = 1 := by
    calc
      ∑ i : Fin n, Matrix.vecMulVec (ψ i) (star (ψ i))
          = ∑ i : Fin n, E.ops i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h_ops i]
      _ = 1 := E.sum_eq_one
  exact exists_orthonormal_basis_restriction ψ h_sum

end POVM

end RankOneNaimark
