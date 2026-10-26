/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Channel.SchmidtThreshold
import QICLean.Channel.TrimmingEnergy
import QICLean.Channel.TrimmedWitness
import QICLean.Entropy.CutEnvironment

/-!
# Trimming a viable subspace cut by cut

Arad, Landau, Vazirani and Vidick reduce the Schmidt rank of a viable subspace by trimming it
collectively, cut by cut (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition
`def:trimming`, lines 642–656). Let `S ⊆ H_A` have the orthonormal basis `u_1, …, u_s` and form
`ψ = ∑_i u_i ⊗ |i⟩ ∈ H_A ⊗ ℂ^s`. Cut by cut from the left, `P^j` projects onto the left Schmidt
vectors of the partially trimmed `ψ` with Schmidt coefficient at least `ξ`, and
`Trim_ξ(S)` is the span of `(P^1 ⊗ 1) ⋯ (P^m ⊗ 1) u_i`.

Here `H_A = ℂ^σ` with `σ = SiteConfig n` the configurations of a finite set of sites, and the
cuts are a monotone family of regions `D 0 ⊆ D 1 ⊆ ⋯`; the cut `j` puts the sites of `D j` on the
left. For a chain `H_A = H_A^1 ⊗ ⋯ ⊗ H_A^ℓ`, `D j` is the first `j + 1` factors and there are
`m = ℓ - 1` cuts. The target `T` lives in `ℂ^{σ × β}`, the environment `H_B = ℂ^β` sitting on
the right of every cut.

## The projections

`trimProj D ξ u j` is `(P^1 ⊗ 1) ⋯ (P^j ⊗ 1)` with the source's order of the factors, and
`trimStep D ξ u j` is the projection `P^{j+1}` of the cut `D j`, the spectral projection onto
`[ξ², ∞)` of the left marginal of the partially trimmed `ψ`. Because a spectral projection with a
positive threshold lies in the range of the vector it is computed from, the projections are
nested: `trimProj (j + 1)` is the lift of `trimStep j` (`trimProj_succ_eq_localLift`), and
`trimProj j` decreases in `j` (`trimProj_mul_trimProj_of_le`).

## Lemma `lem:trimming`

`isCloseTo_prodExt_trimSubspace`: if `S` is `δ`-viable for `T` and every vector of `T` has
Schmidt rank at most `b` across each of the `m` cuts, then `Trim_ξ(S)` is
`(δ + 2 ξ √(m b))`-viable for `T`. The proof is the source's telescoping: the part of `u` removed
at the cut `j` pairs with `t` to at most `ξ √b ‖u‖ ‖w_j‖`, where the `w_j` are the orthogonal
pieces of `t` removed at the successive cuts, and `∑_j ‖w_j‖ ≤ √m ‖t‖`.

`schmidtRank_cutVector_trimmed_le`: every spanning vector `trimProj m u_i` has Schmidt rank at
most `s / ξ²` across each cut (the second statement of the lemma; its running time is out of
scope).

**Local fix (the constant of Lemma `lem:trimming`):** the source states
`δ' ≤ δ + √(ℓ b s) ξ`. Its argument gives, per cut, a pairing with a vector of Schmidt rank at most
`b`, and after squaring the overlap the bound `δ + 2 √((ℓ - 1) b) ξ` proved here; the printed
bound does not follow from the printed argument. The two bounds are not comparable in general:
the factor `s` disappears and a factor `2` appears. The later uses of the lemma choose `ξ`
polynomially small so that the trimming error is below a fixed constant, and a constant factor
in the error is absorbed by rescaling `ξ`. Documented in
`docs/paper-gaps/alvv16_trimming_constant.tex`.

## Main definitions

* `Entropy.stackVector`: the vector `ψ = ∑_i u_i ⊗ |i⟩`.
* `Entropy.trimProj`, `Entropy.trimStep`: the projections of the trimming.
* `Entropy.trimSubspace`: the trimmed subspace `Trim_ξ(S)`.

## Main results

* `Entropy.trimProj_succ_eq_localLift`, `Entropy.trimProj_mul_trimProj_of_le`: nesting.
* `Entropy.isCloseTo_prodExt_trimSubspace`: Lemma `lem:trimming`, viability.
* `Entropy.schmidtRank_cutVector_trimmed_le`: Lemma `lem:trimming`, the Schmidt ranks.

## References

* I. Arad, Z. Landau, U. Vazirani, T. Vidick, *Rigorous RG algorithms and area laws for low
  energy eigenstates in 1D*, arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`: Definition
  `def:trimming`, lines 642–656; Lemma `lem:trimming` and its proof, lines 660–697.
-/

open Matrix Module
open scoped InnerProductSpace ComplexOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-- A projection fixing a bipartite vector fixes its threshold projections: if
`(M ⊗ 1) ψ = ψ` and `b > 0`, then `M P = P` for the spectral projection `P` of the left marginal
onto `[b, ∞)`. Indeed `P = ρ g(ρ)` with `g t = t⁻¹` on `[b, ∞)`, and `M ρ = ρ`. -/
theorem mul_spectralProjectionGE_leftMarginal_of_leftApply_eq {M : Matrix m m ℂ}
    {ψ : EuclideanSpace ℂ (m × n)} (hM : leftApply M ψ = ψ) {b : ℝ} (hb : 0 < b) :
    M * spectralProjectionGE (leftMarginal ψ) b = spectralProjectionGE (leftMarginal ψ) b := by
  set C := schmidtCoeffMatrix (WithLp.ofLp ψ)
  have hMC : M * C = C := by
    have h := congrArg (fun v ↦ schmidtCoeffMatrix (WithLp.ofLp v)) hM
    simpa only [schmidtCoeffMatrix_ofLp_leftApply] using h
  have hsa : IsSelfAdjoint (leftMarginal ψ) := (posSemidef_leftMarginal ψ).isHermitian
  have hcont : ContinuousOn (fun t : ℝ ↦ if b ≤ t then t⁻¹ else 0)
      (spectrum ℝ (leftMarginal ψ)) := by
    rw [continuousOn_iff_continuous_domRestrict]; fun_prop
  have hfac : spectralProjectionGE (leftMarginal ψ) b =
      leftMarginal ψ * cfc (fun t : ℝ ↦ if b ≤ t then t⁻¹ else 0) (leftMarginal ψ) := by
    conv_rhs => lhs; rw [← cfc_id' ℝ (leftMarginal ψ) hsa]
    rw [← cfc_mul (fun t : ℝ ↦ t) _ _ (by fun_prop) hcont]
    unfold spectralProjectionGE
    congr 1
    funext t
    split_ifs with h
    · exact (mul_inv_cancel₀ (by linarith)).symm
    · simp
  rw [hfac, ← Matrix.mul_assoc]
  congr 1
  change M * (C * Cᴴ) = C * Cᴴ
  rw [← Matrix.mul_assoc, hMC]

omit [DecidableEq m] in
/-- `(A ⊗ 1)` is adjoint to `(Aᴴ ⊗ 1)`. -/
theorem inner_leftApply_left (A : Matrix m m ℂ) (x y : EuclideanSpace ℂ (m × n)) :
    inner ℂ (leftApply A x) y = inner ℂ x (leftApply Aᴴ y) := by
  rw [inner_eq_trace_schmidtCoeffMatrix, inner_eq_trace_schmidtCoeffMatrix,
    schmidtCoeffMatrix_ofLp_leftApply, schmidtCoeffMatrix_ofLp_leftApply, conjTranspose_mul,
    Matrix.mul_assoc]

omit [DecidableEq m] in
/-- `(1 ⊗ Q)` is adjoint to `(1 ⊗ Qᴴ)`. -/
theorem inner_rightApply_left {n' : Type*} [Fintype n'] (Q : Matrix n' n ℂ)
    (x : EuclideanSpace ℂ (m × n)) (y : EuclideanSpace ℂ (m × n')) :
    inner ℂ (rightApply Q x) y = inner ℂ x (rightApply Qᴴ y) := by
  rw [inner_eq_trace_schmidtCoeffMatrix, inner_eq_trace_schmidtCoeffMatrix,
    schmidtCoeffMatrix_ofLp_rightApply, schmidtCoeffMatrix_ofLp_rightApply, conjTranspose_mul,
    Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  congr 2

omit [DecidableEq m] in
/-- `‖(1 ⊗ N) y‖² ≤ (∑ |N k l|²) ‖y‖²`, by Cauchy–Schwarz in each entry. -/
theorem norm_rightApply_sq_le {n' : Type*} [Fintype n'] (N : Matrix n' n ℂ)
    (y : EuclideanSpace ℂ (m × n)) :
    ‖rightApply N y‖ ^ 2 ≤ (∑ k, ∑ l, ‖N k l‖ ^ 2) * ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  have hentry (i : m) (k : n') : ‖(rightApply N y) (i, k)‖ ^ 2 ≤
      (∑ l, ‖N k l‖ ^ 2) * ∑ l, ‖y (i, l)‖ ^ 2 := by
    change ‖∑ l, y (i, l) * N k l‖ ^ 2 ≤ _
    calc ‖∑ l, y (i, l) * N k l‖ ^ 2 ≤ (∑ l, ‖y (i, l)‖ * ‖N k l‖) ^ 2 := by
          gcongr
          exact (norm_sum_le _ _).trans (by simp)
      _ ≤ (∑ l, ‖y (i, l)‖ ^ 2) * ∑ l, ‖N k l‖ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = _ := mul_comm _ _
  calc ∑ i, ∑ k, ‖(rightApply N y) (i, k)‖ ^ 2
      ≤ ∑ i, ∑ k, (∑ l, ‖N k l‖ ^ 2) * ∑ l, ‖y (i, l)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k _ ↦ hentry i k
    _ = (∑ k, ∑ l, ‖N k l‖ ^ 2) * ∑ i, ∑ l, ‖y (i, l)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_mul]

omit [Fintype n] [DecidableEq m] in
theorem leftApply_add (A B : Matrix m m ℂ) (x : EuclideanSpace ℂ (m × n)) :
    leftApply (A + B) x = leftApply A x + leftApply B x := by
  ext ⟨i, j⟩
  simp [leftApply, toEuclid, Matrix.add_mul]

omit [Fintype n] [DecidableEq m] in
theorem leftApply_sub (A B : Matrix m m ℂ) (x : EuclideanSpace ℂ (m × n)) :
    leftApply (A - B) x = leftApply A x - leftApply B x := by
  ext ⟨i, j⟩
  simp [leftApply, toEuclid, Matrix.sub_mul]

omit [Fintype n] [DecidableEq m] in
theorem leftApply_zero (x : EuclideanSpace ℂ (m × n)) : leftApply (0 : Matrix m m ℂ) x = 0 := by
  ext ⟨i, j⟩
  simp [leftApply, toEuclid]

omit [Fintype n] in
theorem leftApply_one (x : EuclideanSpace ℂ (m × n)) : leftApply (1 : Matrix m m ℂ) x = x := by
  ext ⟨i, j⟩
  simp [leftApply, toEuclid]

omit [DecidableEq m] in
/-- An orthogonal projection on the first factor does not increase the norm. -/
theorem norm_leftApply_le_of_isHermitian_idem {P : Matrix m m ℂ} (hPh : P.IsHermitian)
    (hPi : P * P = P) (x : EuclideanSpace ℂ (m × n)) : ‖leftApply P x‖ ≤ ‖x‖ := by
  have h : ‖leftApply P x‖ ^ 2 = RCLike.re (inner ℂ x (leftApply P x)) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_leftApply_left, hPh.eq, leftApply_leftApply,
      hPi]
  have h2 : RCLike.re (inner ℂ x (leftApply P x)) ≤ ‖x‖ * ‖leftApply P x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases eq_or_lt_of_le (norm_nonneg (leftApply P x)) with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

end Matrix

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {s : ℕ}

/-- The vector `ψ = ∑_i u_i ⊗ |i⟩` of `ℂ^σ ⊗ ℂ^s` stacking a family of vectors
(arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition `def:trimming`, line 647). -/
def stackVector (u : Fin s → EuclideanSpace ℂ (SiteConfig n)) :
    EuclideanSpace ℂ (SiteConfig n × Fin s) :=
  WithLp.toLp 2 fun p ↦ u p.2 p.1

/-- The product `(P^1 ⊗ 1) ⋯ (P^j ⊗ 1)` of the first `j` trimming projections
(arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition `def:trimming`, lines 647–655). The
projection added at the cut `D j` is the spectral projection onto `[ξ², ∞)` of the left marginal,
across that cut, of the partially trimmed stacked vector: the projection onto its left Schmidt
vectors with Schmidt coefficient at least `ξ`. -/
noncomputable def trimProj (D : ℕ → Finset V) (ξ : ℝ)
    (u : Fin s → EuclideanSpace ℂ (SiteConfig n)) :
    ℕ → Matrix (SiteConfig n) (SiteConfig n) ℂ
  | 0 => 1
  | j + 1 => trimProj D ξ u j * localLift (D j) (spectralProjectionGE
      (leftMarginal (cutEnvVector (D j) (leftApply (trimProj D ξ u j) (stackVector u)))) (ξ ^ 2))

/-- The projection `P^{j+1}` of the cut `D j`: the spectral projection onto `[ξ², ∞)` of the left
marginal of the partially trimmed stacked vector. -/
noncomputable def trimStep (D : ℕ → Finset V) (ξ : ℝ)
    (u : Fin s → EuclideanSpace ℂ (SiteConfig n)) (j : ℕ) :
    Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ :=
  spectralProjectionGE
    (leftMarginal (cutEnvVector (D j) (leftApply (trimProj D ξ u j) (stackVector u)))) (ξ ^ 2)

theorem trimProj_zero (D : ℕ → Finset V) (ξ : ℝ) (u : Fin s → EuclideanSpace ℂ (SiteConfig n)) :
    trimProj D ξ u 0 = 1 :=
  rfl

theorem trimProj_succ (D : ℕ → Finset V) (ξ : ℝ) (u : Fin s → EuclideanSpace ℂ (SiteConfig n))
    (j : ℕ) : trimProj D ξ u (j + 1) = trimProj D ξ u j * localLift (D j) (trimStep D ξ u j) :=
  rfl

/-- The `ξ`-trimmed subspace `Trim_ξ(S)` after `m` cuts: the span of the trimmed basis vectors
(arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition `def:trimming`,
eq. `def-viable-trim`, line 654). -/
noncomputable def trimSubspace (D : ℕ → Finset V) (ξ : ℝ)
    (u : Fin s → EuclideanSpace ℂ (SiteConfig n)) (m : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (SiteConfig n)) :=
  Submodule.span ℂ (Set.range fun i ↦ toEuclideanLin (trimProj D ξ u m) (u i))

theorem trimStep_isStarProjection (D : ℕ → Finset V) (ξ : ℝ)
    (u : Fin s → EuclideanSpace ℂ (SiteConfig n)) (j : ℕ) :
    IsStarProjection (trimStep D ξ u j) :=
  (posSemidef_leftMarginal _).isHermitian.isStarProjection_spectralProjectionGE _

variable {D : ℕ → Finset V} {ξ : ℝ} {u : Fin s → EuclideanSpace ℂ (SiteConfig n)}

/-- The lift of an orthogonal projection is an orthogonal projection. -/
theorem localLift_isHermitian_of_isStarProjection {E : Finset V}
    {P : Matrix (RegionConfig n E) (RegionConfig n E) ℂ} (hP : IsStarProjection P) :
    (localLift E P).IsHermitian := by
  rw [IsHermitian, ← localLift_conjTranspose, hP.isSelfAdjoint.isHermitian.eq]

theorem localLift_mul_self_of_isStarProjection {E : Finset V}
    {P : Matrix (RegionConfig n E) (RegionConfig n E) ℂ} (hP : IsStarProjection P) :
    localLift E P * localLift E P = localLift E P := by
  rw [← localLift_mul, hP.isIdempotentElem.eq]

/-- **Nesting of the trimming projections.** `trimProj` is an orthogonal projection supported
in `D j`, and the next factor lies in its range, so `trimProj (j + 1)` is the lift of the
projection `trimStep j`. -/
theorem trimProj_props (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n) (j : ℕ) :
    (trimProj D ξ u j).IsHermitian ∧ trimProj D ξ u j * trimProj D ξ u j = trimProj D ξ u j ∧
      IsSupportedOn (trimProj D ξ u j) (D j) ∧
      trimProj D ξ u (j + 1) = localLift (D j) (trimStep D ξ u j) := by
  have key : ∀ j, (trimProj D ξ u j).IsHermitian ∧
      trimProj D ξ u j * trimProj D ξ u j = trimProj D ξ u j ∧
      IsSupportedOn (trimProj D ξ u j) (D j) := by
    intro j
    induction j with
    | zero =>
      refine ⟨isHermitian_one, Matrix.mul_one _, ?_⟩
      rw [trimProj_zero, ← localLift_one (D := D 0)]
      exact isSupportedOn_localLift _
    | succ j ih =>
      obtain ⟨hh, hi, hs⟩ := ih
      have heq := trimProj_succ_eq_aux hD hξ σ₀ j hh hi hs
      rw [heq]
      exact ⟨localLift_isHermitian_of_isStarProjection (trimStep_isStarProjection D ξ u j),
        localLift_mul_self_of_isStarProjection (trimStep_isStarProjection D ξ u j),
        (isSupportedOn_localLift _).mono (hD (Nat.le_succ j))⟩
  obtain ⟨hh, hi, hs⟩ := key j
  exact ⟨hh, hi, hs, trimProj_succ_eq_aux hD hξ σ₀ j hh hi hs⟩
where
  /-- The inductive step of the nesting. -/
  trimProj_succ_eq_aux (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n) (j : ℕ)
      (hh : (trimProj D ξ u j).IsHermitian)
      (hi : trimProj D ξ u j * trimProj D ξ u j = trimProj D ξ u j)
      (hs : IsSupportedOn (trimProj D ξ u j) (D j)) :
      trimProj D ξ u (j + 1) = localLift (D j) (trimStep D ξ u j) := by
    obtain ⟨K, hK⟩ := hs.exists_localLift σ₀
    set ψj := leftApply (trimProj D ξ u j) (stackVector u)
    have hfix : leftApply K (cutEnvVector (D j) ψj) = cutEnvVector (D j) ψj := by
      rw [← cutEnvVector_leftApply_of_cutOperator_eq_kronecker_one (D j)
        (X := trimProj D ξ u j) (by rw [hK]; exact cutOperator_localLift K), leftApply_leftApply,
        hi]
    have hKP : K * trimStep D ξ u j = trimStep D ξ u j :=
      mul_spectralProjectionGE_leftMarginal_of_leftApply_eq hfix (by positivity)
    rw [trimProj_succ, hK, ← localLift_mul, hKP]

/-- **The trimming projections decrease.** For `k ≤ j`, `trimProj k * trimProj j = trimProj j`
and `trimProj j * trimProj k = trimProj j`. -/
theorem trimProj_mul_trimProj_of_le (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n)
    {k j : ℕ} (hkj : k ≤ j) :
    trimProj D ξ u k * trimProj D ξ u j = trimProj D ξ u j ∧
      trimProj D ξ u j * trimProj D ξ u k = trimProj D ξ u j := by
  induction j, hkj using Nat.le_induction with
  | base =>
    have := (trimProj_props (u := u) hD hξ σ₀ k).2.1
    exact ⟨this, this⟩
  | succ j hkj ih =>
    obtain ⟨hh, hi, -, hsucc⟩ := trimProj_props (u := u) hD hξ σ₀ j
    obtain ⟨hh', -, -, -⟩ := trimProj_props (u := u) hD hξ σ₀ (j + 1)
    -- `trimProj j * trimProj (j + 1) = trimProj (j + 1)`
    have h1 : trimProj D ξ u j * trimProj D ξ u (j + 1) = trimProj D ξ u (j + 1) := by
      rw [trimProj_succ, ← Matrix.mul_assoc, hi]
    have h2 : trimProj D ξ u (j + 1) * trimProj D ξ u j = trimProj D ξ u (j + 1) := by
      have := congrArg conjTranspose h1
      rwa [conjTranspose_mul, hh.eq, hh'.eq] at this
    constructor
    · rw [← h1, ← Matrix.mul_assoc, ih.1]
    · rw [← h2, Matrix.mul_assoc, ih.2]

/-- The difference of consecutive trimming projections. -/
noncomputable def trimDiff (D : ℕ → Finset V) (ξ : ℝ)
    (u : Fin s → EuclideanSpace ℂ (SiteConfig n)) (j : ℕ) :
    Matrix (SiteConfig n) (SiteConfig n) ℂ :=
  trimProj D ξ u j - trimProj D ξ u (j + 1)

theorem trimDiff_isHermitian (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n) (j : ℕ) :
    (trimDiff D ξ u j).IsHermitian :=
  (trimProj_props hD hξ σ₀ j).1.sub (trimProj_props hD hξ σ₀ (j + 1)).1

theorem trimDiff_mul_self (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n) (j : ℕ) :
    trimDiff D ξ u j * trimDiff D ξ u j = trimDiff D ξ u j := by
  obtain ⟨h1, h2⟩ := trimProj_mul_trimProj_of_le (u := u) hD hξ σ₀ (Nat.le_succ j)
  have hi := (trimProj_props (u := u) hD hξ σ₀ j).2.1
  have hi' := (trimProj_props (u := u) hD hξ σ₀ (j + 1)).2.1
  simp only [trimDiff, Matrix.sub_mul, Matrix.mul_sub, hi, hi', h1, h2]
  abel

/-- `(1 - trimProj j) * trimDiff j = 0`. -/
theorem one_sub_trimProj_mul_trimDiff (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n)
    (j : ℕ) : (1 - trimProj D ξ u j) * trimDiff D ξ u j = 0 := by
  obtain ⟨h1, -⟩ := trimProj_mul_trimProj_of_le (u := u) hD hξ σ₀ (Nat.le_succ j)
  have hi := (trimProj_props (u := u) hD hξ σ₀ j).2.1
  simp only [trimDiff, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, hi, h1]
  abel

/-- `trimDiff j = lift (1 - P^{j+1}) * trimProj j`: the part removed at the cut `D j`. -/
theorem trimDiff_eq (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n) (j : ℕ) :
    trimDiff D ξ u j = localLift (D j) (1 - trimStep D ξ u j) * trimProj D ξ u j := by
  obtain ⟨-, h2⟩ := trimProj_mul_trimProj_of_le (u := u) hD hξ σ₀ (Nat.le_succ j)
  rw [localLift_sub_one_mul, ← (trimProj_props (u := u) hD hξ σ₀ j).2.2.2, h2, trimDiff]
where
  localLift_sub_one_mul :
      localLift (D j) (1 - trimStep D ξ u j) * trimProj D ξ u j =
        trimProj D ξ u j - localLift (D j) (trimStep D ξ u j) * trimProj D ξ u j := by
    rw [show (1 : Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ) - trimStep D ξ u j =
        1 + (-1 : ℂ) • trimStep D ξ u j by rw [neg_one_smul, sub_eq_add_neg],
      localLift_add, localLift_one, localLift_smul, Matrix.add_mul, Matrix.one_mul,
      Matrix.smul_mul, neg_one_smul, sub_eq_add_neg]

variable {β : Type*} [Fintype β] [DecidableEq β]

omit [DecidableEq β] in
/-- The removed pieces of `t` at the successive cuts are orthogonal and together no longer than
`t`: `∑_{j < m} ‖(trimDiff j ⊗ 1) t‖² ≤ ‖t‖²`. -/
theorem sum_norm_leftApply_trimDiff_sq_le (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n)
    (m : ℕ) (t : EuclideanSpace ℂ (SiteConfig n × β)) :
    ∑ j ∈ Finset.range m, ‖leftApply (trimDiff D ξ u j) t‖ ^ 2 ≤ ‖t‖ ^ 2 := by
  have key : ∀ m, ‖leftApply (1 - trimProj D ξ u m) t‖ ^ 2 =
      ∑ j ∈ Finset.range m, ‖leftApply (trimDiff D ξ u j) t‖ ^ 2 := by
    intro m
    induction m with
    | zero => simp [trimProj_zero, leftApply_zero]
    | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hsplit : leftApply (1 - trimProj D ξ u (m + 1)) t =
          leftApply (1 - trimProj D ξ u m) t + leftApply (trimDiff D ξ u m) t := by
        rw [← leftApply_add, trimDiff]
        congr 1
        abel
      have horth : inner ℂ (leftApply (1 - trimProj D ξ u m) t)
          (leftApply (trimDiff D ξ u m) t) = 0 := by
        have hh := (trimProj_props (u := u) hD hξ σ₀ m).1
        rw [inner_leftApply_left, conjTranspose_sub, conjTranspose_one, hh.eq,
          leftApply_leftApply, one_sub_trimProj_mul_trimDiff hD hξ σ₀ m]
        rw [leftApply_zero, inner_zero_right]
      rw [hsplit]
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
      rw [sq, this, sq, sq]
  rw [← key]
  have hh := (trimProj_props (u := u) hD hξ σ₀ m).1
  have hi := (trimProj_props (u := u) hD hξ σ₀ m).2.1
  have hh1 : (1 - trimProj D ξ u m).IsHermitian := isHermitian_one.sub hh
  have hi1 : (1 - trimProj D ξ u m) * (1 - trimProj D ξ u m) = 1 - trimProj D ξ u m := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, hi]
    abel
  gcongr
  exact norm_leftApply_le_of_isHermitian_idem hh1 hi1 t

omit [DecidableEq β] in
/-- A vector of `S ⊗ ℂ^β` in the stacked form: with an orthonormal basis `u_i` of `S`,
`w = ∑_i u_i ⊗ c_i` where `c_i b = ⟪u_i, w (·, b)⟫`, that is `w = (1 ⊗ C) ψ`. -/
theorem eq_rightApply_stackVector {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (bS : OrthonormalBasis (Fin s) ℂ S) {w : EuclideanSpace ℂ (SiteConfig n × β)}
    (hw : w ∈ Submodule.prodExt S β) :
    w = rightApply (Matrix.of fun b i ↦ inner ℂ (bS i : EuclideanSpace ℂ (SiteConfig n))
        (WithLp.toLp 2 fun a ↦ w (a, b))) (stackVector fun i ↦ (bS i : _)) := by
  ext ⟨a, b⟩
  have hrep := bS.sum_repr' ⟨_, hw b⟩
  have h := congrArg (fun x : S ↦ (x : EuclideanSpace ℂ (SiteConfig n)) a) hrep
  simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_inner] at h
  change w (a, b) = ∑ i, (stackVector fun i ↦ (bS i : _)) (a, i) * _
  simp only [stackVector, Matrix.of_apply, transpose_apply]
  rw [← h]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

omit [DecidableEq β] in
/-- The squared Frobenius norm of the coefficients `⟪u_i, w (·, b)⟫` of a vector of `S ⊗ ℂ^β` is
`‖w‖²`. -/
theorem sum_norm_inner_sq_eq {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (bS : OrthonormalBasis (Fin s) ℂ S) {w : EuclideanSpace ℂ (SiteConfig n × β)}
    (hw : w ∈ Submodule.prodExt S β) :
    ∑ b, ∑ i, ‖inner ℂ (bS i : EuclideanSpace ℂ (SiteConfig n))
      (WithLp.toLp 2 fun a ↦ w (a, b))‖ ^ 2 = ‖w‖ ^ 2 := by
  calc ∑ b, ∑ i, ‖inner ℂ (bS i : EuclideanSpace ℂ (SiteConfig n))
        (WithLp.toLp 2 fun a ↦ w (a, b))‖ ^ 2
      = ∑ b, ‖(WithLp.toLp 2 fun a ↦ w (a, b) : EuclideanSpace ℂ (SiteConfig n))‖ ^ 2 := by
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        have h := bS.sum_sq_norm_inner_right (⟨_, hw b⟩ : S)
        rw [show ‖(⟨_, hw b⟩ : S)‖ = ‖(WithLp.toLp 2 fun a ↦ w (a, b) :
          EuclideanSpace ℂ (SiteConfig n))‖ from rfl] at h
        simpa only [Submodule.coe_inner] using h
    _ = ‖w‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq w, Fintype.sum_prod_type, Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ ↦ ?_
        rw [EuclideanSpace.norm_sq_eq]

omit [DecidableEq β] in
/-- **The part removed at one cut** (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, proof of Lemma
`lem:trimming`, lines 666–680). Let `w ∈ S ⊗ ℂ^β` and let `t` have Schmidt rank at most `b` across
the cut `D j`. The part `(trimDiff j ⊗ 1) w` of `w` removed at that cut pairs with `t` to at most
`ξ √b ‖w‖ ‖(trimDiff j ⊗ 1) t‖`. -/
theorem norm_inner_leftApply_trimDiff_le (hD : Monotone D) (hξ : 0 < ξ) (σ₀ : SiteConfig n)
    {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))} (bS : OrthonormalBasis (Fin s) ℂ S)
    {w t : EuclideanSpace ℂ (SiteConfig n × β)} (hw : w ∈ Submodule.prodExt S β) {b : ℕ}
    (j : ℕ) (ht : Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (D j) t)) ≤ b) :
    ‖inner ℂ (leftApply (trimDiff D ξ (fun i ↦ (bS i : _)) j) w) t‖ ≤
      ξ * √b * ‖w‖ * ‖leftApply (trimDiff D ξ (fun i ↦ (bS i : _)) j) t‖ := by
  set u : Fin s → EuclideanSpace ℂ (SiteConfig n) := fun i ↦ (bS i : _) with hu
  set Δ := trimDiff D ξ u j
  set C : Matrix β (Fin s) ℂ := Matrix.of fun b i ↦
    inner ℂ (bS i : EuclideanSpace ℂ (SiteConfig n)) (WithLp.toLp 2 fun a ↦ w (a, b))
  have hΔh : Δ.IsHermitian := trimDiff_isHermitian (u := u) hD hξ σ₀ j
  have hΔi : Δ * Δ = Δ := trimDiff_mul_self (u := u) hD hξ σ₀ j
  have hΔe : Δ = localLift (D j) (1 - trimStep D ξ u j) * trimProj D ξ u j :=
    trimDiff_eq hD hξ σ₀ j
  have hwC : w = rightApply C (stackVector u) := eq_rightApply_stackVector bS hw
  -- move `Δ` onto `t`, and `C` onto the other side
  have h1 : inner ℂ (leftApply Δ w) t =
      inner ℂ (leftApply Δ (stackVector u)) (rightApply Cᴴ (leftApply Δ t)) := by
    rw [← hΔi, ← leftApply_leftApply, inner_leftApply_left, hΔh.eq, hΔi, hwC,
      leftApply_rightApply, inner_rightApply_left]
  -- the part removed from the stacked vector is the discarded part at the cut
  obtain ⟨K, hK⟩ := (trimProj_props (u := u) hD hξ σ₀ j).2.2.1.exists_localLift σ₀
  have hΔeq : Δ = localLift (D j) ((1 - trimStep D ξ u j) * K) := by
    rw [localLift_mul, ← hK]
    exact hΔe
  have h2 : cutEnvVector (D j) (leftApply Δ (stackVector u)) =
      leftApply (1 - trimStep D ξ u j)
        (cutEnvVector (D j) (leftApply (trimProj D ξ u j) (stackVector u))) := by
    rw [hΔe, ← leftApply_leftApply, cutEnvVector_leftApply_localLift]
  -- the rank of the paired vector
  have hrank : Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (D j)
      (rightApply Cᴴ (leftApply Δ t)))) ≤ b := by
    refine (schmidtRank_cutEnvVector_rightApply_le (D j) Cᴴ _).trans ?_
    rw [hΔeq, cutEnvVector_leftApply_localLift]
    exact (schmidtRank_leftApply_le _ _).trans ht
  -- the norm of the paired vector
  have hnorm : ‖rightApply Cᴴ (leftApply Δ t)‖ ≤ ‖w‖ * ‖leftApply Δ t‖ := by
    have h := norm_rightApply_sq_le Cᴴ (leftApply Δ t)
    have hF : ∑ k, ∑ l, ‖Cᴴ k l‖ ^ 2 = ‖w‖ ^ 2 := by
      rw [← sum_norm_inner_sq_eq bS hw, Finset.sum_comm]
      simp only [C, conjTranspose_apply, of_apply, norm_star]
    rw [hF, ← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  rw [h1, ← (cutEnvVector (D j)).inner_map_map, h2]
  calc ‖inner ℂ (leftApply (1 - trimStep D ξ u j) _) _‖
      ≤ √(ξ ^ 2 * b) * ‖cutEnvVector (D j) (rightApply Cᴴ (leftApply Δ t))‖ :=
        norm_inner_leftApply_one_sub_spectralProjectionGE_le _ (sq_nonneg ξ) hrank
    _ = ξ * √b * ‖rightApply Cᴴ (leftApply Δ t)‖ := by
        rw [LinearIsometryEquiv.norm_map, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hξ.le]
    _ ≤ ξ * √b * (‖w‖ * ‖leftApply Δ t‖) := by gcongr
    _ = _ := by ring

omit [DecidableEq β] in
/-- The trimmed vector lies in the trimmed extension: `(trimProj m ⊗ 1) w ∈ Trim_ξ(S) ⊗ ℂ^β`
for `w ∈ S ⊗ ℂ^β`. -/
theorem leftApply_trimProj_mem_prodExt {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))}
    (bS : OrthonormalBasis (Fin s) ℂ S) {w : EuclideanSpace ℂ (SiteConfig n × β)}
    (hw : w ∈ Submodule.prodExt S β) (m : ℕ) :
    leftApply (trimProj D ξ (fun i ↦ (bS i : _)) m) w ∈
      Submodule.prodExt (trimSubspace D ξ (fun i ↦ (bS i : _)) m) β := by
  intro b
  have hrep := bS.sum_repr' ⟨_, hw b⟩
  have hslice : (WithLp.toLp 2 fun a ↦
      leftApply (trimProj D ξ (fun i ↦ (bS i : _)) m) w (a, b) : EuclideanSpace ℂ _) =
      toEuclideanLin (trimProj D ξ (fun i ↦ (bS i : _)) m)
        (WithLp.toLp 2 fun a ↦ w (a, b)) := by
    ext a
    simp [leftApply, toEuclid, mul_apply, mulVec, dotProduct]
  rw [hslice]
  have hcoe := congrArg (fun x : S ↦ (x : EuclideanSpace ℂ (SiteConfig n))) hrep
  simp only [Submodule.coe_sum, Submodule.coe_smul] at hcoe
  rw [← hcoe, map_sum]
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

omit [DecidableEq β] in
/-- **Lemma `lem:trimming`, viability** (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`,
lines 660–697, with the local fix of the module docstring). Let `S ⊆ ℂ^σ` have the orthonormal
basis `u = bS`, let `S ⊗ ℂ^β` be `δ`-close to `T ⊆ ℂ^{σ × β}`, and let every vector of `T` have
Schmidt rank at most `b` across each of the cuts `D 0, …, D (m - 1)`. Then for `ξ > 0` the
trimmed subspace `Trim_ξ(S)` after the `m` cuts satisfies: `Trim_ξ(S) ⊗ ℂ^β` is
`(δ + 2 ξ √(m b))`-close to `T`. -/
theorem isCloseTo_prodExt_trimSubspace (hD : Monotone D) (hξ : 0 < ξ)
    {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))} (bS : OrthonormalBasis (Fin s) ℂ S)
    {T : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n × β))} {δ : ℝ}
    (hT : Submodule.IsCloseTo δ (Submodule.prodExt S β) T) {m b : ℕ}
    (hb : ∀ t ∈ T, ∀ j < m, Matrix.schmidtRank (WithLp.ofLp (cutEnvVector (D j) t)) ≤ b) :
    Submodule.IsCloseTo (δ + 2 * (ξ * √(m * b))) (Submodule.prodExt
      (trimSubspace D ξ (fun i ↦ (bS i : _)) m) β) T := by
  rw [Submodule.isCloseTo_iff] at hT ⊢
  intro t ht
  rcases isEmpty_or_nonempty (SiteConfig n) with hσ | ⟨⟨σ₀⟩⟩
  · have : t = 0 := by ext ⟨a, _⟩; exact isEmptyElim a
    simp [this]
  set u : Fin s → EuclideanSpace ℂ (SiteConfig n) := fun i ↦ (bS i : _)
  set ε := ξ * √(m * b) with hε
  have hε0 : 0 ≤ ε := by positivity
  set K := Submodule.prodExt S β
  set w := K.starProjection t with hwdef
  have hwK : w ∈ K := K.starProjection_apply_mem t
  have hwt : inner ℂ w t = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    have e : inner ℂ w t = inner ℂ (K.starProjection w) t := by
      rw [K.starProjection_eq_self_iff.mpr hwK]
    rw [e, K.inner_starProjection_left_eq_right, ← hwdef, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hwle : ‖w‖ ≤ ‖t‖ := K.norm_starProjection_apply_le t
  have hδw : (1 - δ) * ‖t‖ ^ 2 ≤ ‖w‖ ^ 2 := hT t ht
  -- the trimmed vector and its pairing with `t`
  set Q := trimProj D ξ u m
  set x := leftApply Q w
  have hxmem : x ∈ Submodule.prodExt (trimSubspace D ξ u m) β :=
    leftApply_trimProj_mem_prodExt bS hwK m
  -- telescoping
  have htel : w - x = ∑ j ∈ Finset.range m, leftApply (trimDiff D ξ u j) w := by
    have : ∀ m, w - leftApply (trimProj D ξ u m) w =
        ∑ j ∈ Finset.range m, leftApply (trimDiff D ξ u j) w := by
      intro m
      induction m with
      | zero => simp [trimProj_zero, leftApply_one]
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih, trimDiff, leftApply_sub]
        abel
    exact this m
  have hsum : ‖inner ℂ (w - x) t‖ ≤ ε * ‖w‖ * ‖t‖ := by
    rw [htel, sum_inner]
    calc ‖∑ j ∈ Finset.range m, inner ℂ (leftApply (trimDiff D ξ u j) w) t‖
        ≤ ∑ j ∈ Finset.range m, ξ * √b * ‖w‖ * ‖leftApply (trimDiff D ξ u j) t‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj ↦ ?_)
          exact norm_inner_leftApply_trimDiff_le hD hξ σ₀ bS hwK j
            (hb t ht j (Finset.mem_range.mp hj))
      _ = ξ * √b * ‖w‖ * ∑ j ∈ Finset.range m, ‖leftApply (trimDiff D ξ u j) t‖ := by
          rw [Finset.mul_sum]
      _ ≤ ξ * √b * ‖w‖ * (√m * ‖t‖) := by
          gcongr
          -- Cauchy–Schwarz and orthogonality of the removed pieces
          have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range m) (fun _ ↦ (1 : ℝ))
            (fun j ↦ ‖leftApply (trimDiff D ξ u j) t‖)
          simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one] at hcs
          have horth := sum_norm_leftApply_trimDiff_sq_le (u := u) hD hξ σ₀ m t
          have hsq : (∑ j ∈ Finset.range m, ‖leftApply (trimDiff D ξ u j) t‖) ^ 2 ≤
              (√m * ‖t‖) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
            nlinarith
          exact (pow_le_pow_iff_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
            (by positivity) two_ne_zero).mp hsq
      _ = ε * ‖w‖ * ‖t‖ := by
          rw [hε, Real.sqrt_mul (Nat.cast_nonneg _)]
          ring
  -- the overlap of the trimmed vector
  have hxt : ‖w‖ ^ 2 - ε * ‖w‖ * ‖t‖ ≤ ‖inner ℂ x t‖ := by
    have : inner ℂ x t = ((‖w‖ ^ 2 : ℝ) : ℂ) - inner ℂ (w - x) t := by
      rw [inner_sub_left, hwt]; ring
    rw [this]
    have h := norm_sub_norm_le ((‖w‖ ^ 2 : ℝ) : ℂ) (inner ℂ (w - x) t)
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h
    linarith
  -- the projection onto the trimmed extension
  set K' := Submodule.prodExt (trimSubspace D ξ u m) β
  have hxP : ‖inner ℂ x t‖ ≤ ‖x‖ * ‖K'.starProjection t‖ := by
    rw [← K'.starProjection_eq_self_iff.mpr hxmem, K'.inner_starProjection_left_eq_right,
      K'.starProjection_eq_self_iff.mpr hxmem]
    exact norm_inner_le_norm _ _
  have hxw : ‖x‖ ≤ ‖w‖ := norm_leftApply_le_of_isHermitian_idem
    (trimProj_props (u := u) hD hξ σ₀ m).1 (trimProj_props (u := u) hD hξ σ₀ m).2.1 w
  have hP : ‖w‖ * (‖w‖ - ε * ‖t‖) ≤ ‖w‖ * ‖K'.starProjection t‖ := by
    have := hxt.trans (hxP.trans (mul_le_mul_of_nonneg_right hxw (norm_nonneg _)))
    nlinarith
  have hPn := norm_nonneg (K'.starProjection t)
  have hwn := norm_nonneg w
  have htn := norm_nonneg t
  -- conclude
  rcases eq_or_lt_of_le hwn with hw0 | hwpos
  · rw [← hw0] at hδw
    nlinarith [sq_nonneg ‖t‖]
  · have hge : ‖w‖ - ε * ‖t‖ ≤ ‖K'.starProjection t‖ := le_of_mul_le_mul_left hP hwpos
    rcases le_or_gt (ε * ‖t‖) ‖w‖ with hle | hlt
    · have h2 : (‖w‖ - ε * ‖t‖) ^ 2 ≤ ‖K'.starProjection t‖ ^ 2 :=
        pow_le_pow_left₀ (by linarith) hge 2
      have hint : ε * ‖t‖ * ‖w‖ ≤ ε * ‖t‖ * ‖t‖ :=
        mul_le_mul_of_nonneg_left hwle (mul_nonneg hε0 htn)
      calc (1 - (δ + 2 * ε)) * ‖t‖ ^ 2 = (1 - δ) * ‖t‖ ^ 2 - 2 * (ε * ‖t‖ * ‖t‖) := by ring
        _ ≤ ‖w‖ ^ 2 - 2 * (ε * ‖t‖ * ‖w‖) + (ε * ‖t‖) ^ 2 := by
            nlinarith [sq_nonneg (ε * ‖t‖)]
        _ = (‖w‖ - ε * ‖t‖) ^ 2 := by ring
        _ ≤ _ := h2
    · have h1 : ‖w‖ * ‖w‖ ≤ ‖w‖ * ‖t‖ := mul_le_mul_of_nonneg_left hwle hwn
      have h2 : ‖w‖ * ‖t‖ ≤ ε * ‖t‖ * ‖t‖ := mul_le_mul_of_nonneg_right hlt.le htn
      have h3 : 0 ≤ ε * ‖t‖ * ‖t‖ := by positivity
      calc (1 - (δ + 2 * ε)) * ‖t‖ ^ 2 = (1 - δ) * ‖t‖ ^ 2 - 2 * (ε * ‖t‖ * ‖t‖) := by ring
        _ ≤ ‖w‖ * ‖w‖ - 2 * (ε * ‖t‖ * ‖t‖) := by nlinarith
        _ ≤ 0 := by linarith
        _ ≤ _ := sq_nonneg _

/-- **Lemma `lem:trimming`, Schmidt ranks** (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`,
lines 662–663 and 690–692). Every spanning vector `trimProj m u_i` of `Trim_ξ(S)` has Schmidt
rank at most `s / ξ²` across each cut `D k`, `k < m`: `ξ² · rank ≤ s`. -/
theorem schmidtRank_cutVector_trimmed_le (hD : Monotone D) (hξ : 0 < ξ)
    {S : Submodule ℂ (EuclideanSpace ℂ (SiteConfig n))} (bS : OrthonormalBasis (Fin s) ℂ S)
    {m k : ℕ} (hk : k < m) (i : Fin s) :
    ξ ^ 2 * Matrix.schmidtRank (WithLp.ofLp (cutVector (D k)
      (toEuclideanLin (trimProj D ξ (fun i ↦ (bS i : _)) m)
        ((bS i : S) : EuclideanSpace ℂ (SiteConfig n))))) ≤ s := by
  rcases isEmpty_or_nonempty (SiteConfig n) with hσ | ⟨⟨σ₀⟩⟩
  · have : Matrix.schmidtRank (WithLp.ofLp (cutVector (D k)
        (toEuclideanLin (trimProj D ξ (fun i ↦ (bS i : _)) m)
          ((bS i : S) : EuclideanSpace ℂ (SiteConfig n))))) = 0 := by
      rw [Matrix.schmidtRank, show schmidtCoeffMatrix _ = 0 from by
        ext x y; exact isEmptyElim ((cutEquiv n (D k)).symm (x, y))]
      exact Matrix.rank_zero
    rw [this]; simp
  set u : Fin s → EuclideanSpace ℂ (SiteConfig n) := fun i ↦ (bS i : _)
  set ψ := stackVector u
  set Q := trimProj D ξ u m
  -- the trimmed vector is a slice of the trimmed stacked vector
  have hslice : toEuclideanLin Q (u i) =
      (WithLp.toLp 2 fun a ↦ leftApply Q ψ (a, i) : EuclideanSpace ℂ _) := by
    ext a
    simp [ψ, stackVector, leftApply, toEuclid, mul_apply, Matrix.ofLp_toLpLin, mulVec,
      dotProduct]
  rw [hslice]
  refine le_trans (b := ξ ^ 2 * ((trimStep D ξ u k).rank : ℝ)) ?_ ?_
  · gcongr
    refine (schmidtRank_cutVector_slice_le (D k) _ i).trans ?_
    -- `Q = lift P_k * Q`
    have hQ : Q = localLift (D k) (trimStep D ξ u k) * Q := by
      rw [← (trimProj_props (u := u) hD hξ σ₀ k).2.2.2]
      exact ((trimProj_mul_trimProj_of_le (u := u) hD hξ σ₀ (Nat.succ_le_of_lt hk)).1).symm
    rw [hQ, ← leftApply_leftApply, cutEnvVector_leftApply_localLift, Matrix.schmidtRank,
      schmidtCoeffMatrix_ofLp_leftApply]
    exact rank_mul_le_left _ _
  · have h := mul_rank_spectralProjectionGE_leftMarginal_le
      (cutEnvVector (D k) (leftApply (trimProj D ξ u k) ψ)) (ξ ^ 2)
    rw [LinearIsometryEquiv.norm_map] at h
    refine h.trans ?_
    have hψ : ‖ψ‖ ^ 2 = s := by
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
      have : ∀ i : Fin s, ∑ a, ‖ψ (a, i)‖ ^ 2 = 1 := fun i ↦ by
        have h1 := bS.orthonormal.1 i
        rw [← Submodule.norm_coe, EuclideanSpace.norm_eq] at h1
        rw [← Real.sqrt_eq_one, ← h1]
        rfl
      simp [this]
    rw [← hψ]
    gcongr
    exact norm_leftApply_le_of_isHermitian_idem (trimProj_props (u := u) hD hξ σ₀ k).1
      (trimProj_props (u := u) hD hξ σ₀ k).2.1 ψ

end Entropy
