/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift
import QICLean.Channel.SchmidtTrimming

/-!
# Cut coordinates with an environment factor

A vector of `ℂ^σ ⊗ ℂ^β`, with `σ = SiteConfig n` the configurations of a finite set of sites and
`β` an environment, is cut at a region `D` of the sites into the bipartite form
`ℂ^{σ_D} ⊗ (ℂ^{σ_{Dᶜ}} ⊗ ℂ^β)`: the region `D` on the left, the remaining sites together with the
environment on the right. Arad, Landau, Vazirani and Vidick use these cuts for a viable subspace
`S ⊆ H_A = H_A^1 ⊗ ⋯ ⊗ H_A^ℓ` and a target `T ⊆ H_A ⊗ H_B` (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, Lemma `lem:trimming`, lines 660–697), where the cut `(j : j + 1)` puts
`H_A^1 ⊗ ⋯ ⊗ H_A^j` on the left and the rest of `H_A` together with `H_B` on the right.

An operator supported in `D` acts on the left factor, and one supported outside `D`, or acting on
the environment, acts on the right factor. Neither increases the Schmidt rank across the cut.

## Main definitions

* `Entropy.cutEnvEquiv`: the coordinates `(x, (y, b))` of `(σ, b)`, with `x` the part on `D` and
  `y` the part outside.
* `Entropy.cutEnvVector`: a vector of `ℂ^σ ⊗ ℂ^β` in these coordinates, a linear isometry.

## Main results

* `Entropy.cutEnvVector_leftApply_of_cutOperator_eq_kronecker_one`,
  `Entropy.cutEnvVector_leftApply_localLift`: an operator `K ⊗ 1` acts on the left factor.
* `Entropy.cutEnvVector_leftApply_of_cutOperator_eq_one_kronecker`,
  `Entropy.IsSupportedOn.schmidtRank_cutEnvVector_leftApply_le`: an operator supported outside
  `D` acts on the right factor, and does not increase the Schmidt rank across `D`.
* `Entropy.cutEnvVector_rightApply`, `Entropy.schmidtRank_cutEnvVector_rightApply_le`: an
  operator on the environment acts on the right factor.
* `Entropy.schmidtRank_cutVector_slice_le`: a slice `w (·, b)` has Schmidt rank across `D` at
  most that of `w`.
-/

open Matrix
open scoped Kronecker

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {β : Type*} [Fintype β]

/-- The cut coordinates `(x, (y, b))` of a configuration `(σ, b)` of the sites and the
environment: `x` is the part of `σ` on `D` and `y` the part outside `D`. -/
def cutEnvEquiv (n : V → ℕ) (D : Finset V) (β : Type*) :
    SiteConfig n × β ≃
      ((v : {v // v ∈ D}) → Fin (n v)) × (((v : {v // v ∉ D}) → Fin (n v)) × β) :=
  ((cutEquiv n D).prodCongr (Equiv.refl β)).trans (Equiv.prodAssoc _ _ _)

omit [Fintype V] [Fintype β] in
@[simp]
theorem cutEnvEquiv_symm_apply (D : Finset V) (x : (v : {v // v ∈ D}) → Fin (n v))
    (y : (v : {v // v ∉ D}) → Fin (n v)) (b : β) :
    (cutEnvEquiv n D β).symm (x, (y, b)) = ((cutEquiv n D).symm (x, y), b) :=
  rfl

/-- A vector of `ℂ^σ ⊗ ℂ^β` in the cut coordinates at `D`. -/
noncomputable def cutEnvVector (D : Finset V) :
    EuclideanSpace ℂ (SiteConfig n × β) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ
        (((v : {v // v ∈ D}) → Fin (n v)) × (((v : {v // v ∉ D}) → Fin (n v)) × β)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEnvEquiv n D β)

@[simp]
theorem cutEnvVector_apply (D : Finset V) (w : EuclideanSpace ℂ (SiteConfig n × β))
    (x : (v : {v // v ∈ D}) → Fin (n v)) (y : (v : {v // v ∉ D}) → Fin (n v)) (b : β) :
    cutEnvVector D w (x, (y, b)) = w ((cutEquiv n D).symm (x, y), b) :=
  rfl

/-- **An operator on the region acts on the left factor.** If `X` is `K ⊗ 1` in the cut
coordinates at `D`, then `(X ⊗ 1_β) w` is `(K ⊗ 1) w` in the cut coordinates with environment. -/
theorem cutEnvVector_leftApply_of_cutOperator_eq_kronecker_one (D : Finset V)
    {X : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    {K : Matrix ((v : {v // v ∈ D}) → Fin (n v)) ((v : {v // v ∈ D}) → Fin (n v)) ℂ}
    (h : cutOperator D X = K ⊗ₖ (1 : Matrix _ _ ℂ)) (w : EuclideanSpace ℂ (SiteConfig n × β)) :
    cutEnvVector D (leftApply X w) = leftApply K (cutEnvVector D w) := by
  classical
  ext ⟨x, y, b⟩
  have hX (a : SiteConfig n) : X ((cutEquiv n D).symm (x, y)) a =
      K x ((cutEquiv n D) a).1 * (1 : Matrix _ _ ℂ) y ((cutEquiv n D) a).2 := by
    have := congrFun (congrFun h (x, y)) ((cutEquiv n D) a)
    rwa [cutOperator, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      kroneckerMap_apply] at this
  change ∑ a, X ((cutEquiv n D).symm (x, y)) a * w (a, b) =
    ∑ x', K x x' * w ((cutEquiv n D).symm (x', y), b)
  simp_rw [hX]
  rw [← (cutEquiv n D).symm.sum_comp, Fintype.sum_prod_type]
  simp [one_apply, Finset.sum_ite_eq]

/-- An operator lifted from the region `D` acts on the left factor of the cut at `D`. -/
theorem cutEnvVector_leftApply_localLift (D : Finset V)
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ)
    (w : EuclideanSpace ℂ (SiteConfig n × β)) :
    cutEnvVector D (leftApply (localLift D K) w) = leftApply K (cutEnvVector D w) :=
  cutEnvVector_leftApply_of_cutOperator_eq_kronecker_one D (cutOperator_localLift K) w

variable [DecidableEq β]

/-- **An operator outside the region acts on the right factor.** If `X` is `1 ⊗ K` in the cut
coordinates at `D`, then `(X ⊗ 1_β) w` is `(1 ⊗ (K ⊗ 1_β)) w` in the cut coordinates with
environment. -/
theorem cutEnvVector_leftApply_of_cutOperator_eq_one_kronecker (D : Finset V)
    {X : Matrix (SiteConfig n) (SiteConfig n) ℂ}
    {K : Matrix ((v : {v // v ∉ D}) → Fin (n v)) ((v : {v // v ∉ D}) → Fin (n v)) ℂ}
    (h : cutOperator D X = (1 : Matrix _ _ ℂ) ⊗ₖ K) (w : EuclideanSpace ℂ (SiteConfig n × β)) :
    cutEnvVector D (leftApply X w) =
      rightApply (K ⊗ₖ (1 : Matrix β β ℂ)) (cutEnvVector D w) := by
  classical
  ext ⟨x, y, b⟩
  have hX (a : SiteConfig n) : X ((cutEquiv n D).symm (x, y)) a =
      (1 : Matrix _ _ ℂ) x ((cutEquiv n D) a).1 * K y ((cutEquiv n D) a).2 := by
    have := congrFun (congrFun h (x, y)) ((cutEquiv n D) a)
    rwa [cutOperator, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
      kroneckerMap_apply] at this
  change ∑ a, X ((cutEquiv n D).symm (x, y)) a * w (a, b) =
    ∑ p : ((v : {v // v ∉ D}) → Fin (n v)) × β,
      w ((cutEquiv n D).symm (x, p.1), p.2) * (K ⊗ₖ (1 : Matrix β β ℂ)) (y, b) p
  simp_rw [hX]
  rw [← (cutEquiv n D).symm.sum_comp, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp [one_apply, kroneckerMap_apply, Finset.sum_ite_irrel, Finset.sum_ite_eq, mul_comm]

omit [DecidableEq β] in
/-- **An operator supported outside the region does not increase the Schmidt rank across it.**
-/
theorem IsSupportedOn.schmidtRank_cutEnvVector_leftApply_le (D : Finset V)
    {X : Matrix (SiteConfig n) (SiteConfig n) ℂ} {E : Finset V} (hX : IsSupportedOn X E)
    (hED : Disjoint E D) (w : EuclideanSpace ℂ (SiteConfig n × β)) :
    Matrix.schmidtRank (WithLp.ofLp (cutEnvVector D (leftApply X w))) ≤
      Matrix.schmidtRank (WithLp.ofLp (cutEnvVector D w)) := by
  classical
  rcases isEmpty_or_nonempty ((v : {v // v ∈ D}) → Fin (n v)) with hx | ⟨⟨x₀⟩⟩
  · rw [Matrix.schmidtRank, show schmidtCoeffMatrix (WithLp.ofLp (cutEnvVector D (leftApply X w)))
        = 0 from Subsingleton.elim _ _, Matrix.rank_zero]
    exact Nat.zero_le _
  rw [cutEnvVector_leftApply_of_cutOperator_eq_one_kronecker D
    (hX.cutOperator_eq_one_kronecker hED x₀) w]
  exact schmidtRank_rightApply_le _ _

omit [DecidableEq β] in
/-- **An operator on the environment acts on the right factor.** For `M : β → β'`, the vector
`(1 ⊗ M) w` is `(1 ⊗ (1 ⊗ M)) w` in the cut coordinates at `D`. -/
theorem cutEnvVector_rightApply (D : Finset V) {β' : Type*} [Fintype β']
    (M : Matrix β' β ℂ) (w : EuclideanSpace ℂ (SiteConfig n × β)) :
    cutEnvVector D (rightApply M w) =
      rightApply ((1 : Matrix ((v : {v // v ∉ D}) → Fin (n v))
        ((v : {v // v ∉ D}) → Fin (n v)) ℂ) ⊗ₖ M) (cutEnvVector D w) := by
  classical
  ext ⟨x, y, b⟩
  change ∑ b', w ((cutEquiv n D).symm (x, y), b') * Mᵀ b' b =
    ∑ p : ((v : {v // v ∉ D}) → Fin (n v)) × β,
      w ((cutEquiv n D).symm (x, p.1), p.2) * (1 ⊗ₖ M)ᵀ p (y, b)
  rw [Fintype.sum_prod_type]
  simp [transpose_apply, kroneckerMap_apply, one_apply, Finset.sum_ite_irrel, Finset.sum_ite_eq]

omit [DecidableEq β] in
/-- An operator on the environment does not increase the Schmidt rank across `D`. -/
theorem schmidtRank_cutEnvVector_rightApply_le (D : Finset V) {β' : Type*} [Fintype β']
    (M : Matrix β' β ℂ) (w : EuclideanSpace ℂ (SiteConfig n × β)) :
    Matrix.schmidtRank (WithLp.ofLp (cutEnvVector D (rightApply M w))) ≤
      Matrix.schmidtRank (WithLp.ofLp (cutEnvVector D w)) := by
  rw [cutEnvVector_rightApply]
  exact schmidtRank_rightApply_le _ _

omit [DecidableEq β] in
/-- **A slice has no larger Schmidt rank.** The vector `w (·, b)` of `ℂ^σ` has Schmidt rank
across `D` at most that of `w` across `D`. -/
theorem schmidtRank_cutVector_slice_le (D : Finset V) (w : EuclideanSpace ℂ (SiteConfig n × β))
    (b : β) :
    Matrix.schmidtRank (WithLp.ofLp (cutVector D (WithLp.toLp 2 fun a ↦ w (a, b)))) ≤
      Matrix.schmidtRank (WithLp.ofLp (cutEnvVector D w)) := by
  classical
  let F : Matrix (((v : {v // v ∉ D}) → Fin (n v)) × β) ((v : {v // v ∉ D}) → Fin (n v)) ℂ :=
    Matrix.of fun p y ↦ if p = (y, b) then 1 else 0
  have h : schmidtCoeffMatrix (WithLp.ofLp (cutVector D (WithLp.toLp 2 fun a ↦ w (a, b)))) =
      schmidtCoeffMatrix (WithLp.ofLp (cutEnvVector D w)) * F := by
    ext x y
    rw [mul_apply, Finset.sum_eq_single (y, b)]
    · simp [F]
    · intro p _ hp
      simp [F, hp]
    · simp
  rw [Matrix.schmidtRank, Matrix.schmidtRank, h]
  exact rank_mul_le_left _ _

end Entropy
