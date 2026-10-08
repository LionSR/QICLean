/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.CoherentSymbol
import QICLean.Algebra.MatrixAux

/-!
# Limits of coherent symbols

In the proof of Lemma 6.4 of the area-law paper (*A two-dimensional area law from a global
spectral gap*, `05-replicas.tex`, lines 693–708 and 813–836), the operators `O_k` are
approximated on the symmetric subspace, with arbitrarily small limiting error, by compressed
polynomial words whose symbols approximate `f_θ` uniformly; continuity of `f_θ` follows "as a
uniform limit of the clipped continuous symbols". This file records the corresponding closure
property of coherent symbols, and the bilinear-form bound used to estimate compressions.

## Main declarations

* `TensorPower.HasCoherentSymbol.of_approx` — coherent symbols are closed under limits in
  which the operators converge in limiting norm on `𝒮_k` and the symbols converge uniformly on
  unit vectors.
* `TensorPower.l2_opNorm_symProj_mul_mul_symProj_le` — `‖Π M Π‖ ≤ c` from
  `|⟨u, M z⟩| ≤ c ‖u‖ ‖z‖` on symmetric vectors.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 6.4 (`lem:symbol`), section file `05-replicas.tex`, lines 693–708 and 813–836.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation Filter
open scoped Matrix.Norms.L2Operator

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}

/-- **Compressions from bilinear forms**: if `|⟨u, M z⟩| ≤ c ‖u‖ ‖z‖` for all symmetric
`u, z`, then `‖Π M Π‖ ≤ c`. -/
theorem l2_opNorm_symProj_mul_mul_symProj_le {M : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} {c : ℝ}
    (hc : 0 ≤ c)
    (h : ∀ u z, u ∈ invariantSubspace (copyPerm Ω k) → z ∈ invariantSubspace (copyPerm Ω k) →
      ‖star u ⬝ᵥ (M *ᵥ z)‖ ≤
        c * ‖(EuclideanSpace.equiv _ ℂ).symm u‖ * ‖(EuclideanSpace.equiv _ ℂ).symm z‖) :
    ‖symProj (copyPerm Ω k) * M * symProj (copyPerm Ω k)‖ ≤ c := by
  set P := symProj (copyPerm Ω k)
  have hPv : ∀ v, ‖(EuclideanSpace.equiv _ ℂ).symm (P *ᵥ v)‖ ≤
      ‖(EuclideanSpace.equiv _ ℂ).symm v‖ := fun v => by
    have := (P).l2_opNorm_mulVec ((EuclideanSpace.equiv _ ℂ).symm v)
    refine le_trans (by simpa using this) ?_
    exact mul_le_of_le_one_left (norm_nonneg _) l2_opNorm_symProj_le
  refine l2_opNorm_le_of_forall hc fun v => ?_
  have hPP : P * P = P := symProj_mul_symProj
  have hwdef : (P * M * P) *ᵥ v = P *ᵥ (M *ᵥ (P *ᵥ v)) := by
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  set w := (P * M * P) *ᵥ v
  have hw : P *ᵥ w = w := by
    rw [hwdef, mulVec_mulVec, hPP]
  have key : ∀ y, star w ⬝ᵥ (P *ᵥ y) = star w ⬝ᵥ y := fun y => by
    have h1 : star (P *ᵥ w) = star w ᵥ* Pᴴ := star_mulVec P w
    rw [(isHermitian_symProj (Ω := Ω) (k := k)).eq, hw] at h1
    rw [dotProduct_mulVec, ← h1]
  have hww : star w ⬝ᵥ w = star w ⬝ᵥ (M *ᵥ (P *ᵥ v)) := by
    calc star w ⬝ᵥ w = star w ⬝ᵥ (P *ᵥ (M *ᵥ (P *ᵥ v))) := by
          congr 1
      _ = _ := key _
  have hbd : ‖star w ⬝ᵥ w‖ ≤ c * ‖(EuclideanSpace.equiv _ ℂ).symm w‖ *
      ‖(EuclideanSpace.equiv _ ℂ).symm v‖ := by
    rw [hww]
    refine (h w (P *ᵥ v) (hw ▸ symProj_mulVec_mem _ w) (symProj_mulVec_mem _ v)).trans ?_
    gcongr
    exact hPv v
  have hsq : ‖(EuclideanSpace.equiv _ ℂ).symm w‖ ^ 2 ≤
      c * ‖(EuclideanSpace.equiv _ ℂ).symm w‖ * ‖(EuclideanSpace.equiv _ ℂ).symm v‖ := by
    rw [← re_star_dotProduct_self_eq_norm_sq]
    exact (RCLike.re_le_norm _).trans hbd
  rcases (norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm w)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · nlinarith [norm_nonneg ((EuclideanSpace.equiv _ ℂ).symm v)]

variable {X : ∀ k, Matrix (Fin k → Ω) (Fin k → Ω) ℂ} {f : (Ω → ℂ) → ℂ}

/-- **Limits of coherent symbols** (`05-replicas.tex`, lines 693–708 and 813–836): if `X_k`
commutes with `Π_k`, `X_k Π_k` is uniformly bounded, and for every `ε > 0` some `X'_k` with
coherent symbol `f'` has `|f - f'| ≤ ε` on unit vectors and eventually `‖(X_k - X'_k)Π_k‖ ≤ ε`,
then `X_k` has coherent symbol `f`. Continuity of `f` follows from uniform approximation by
continuous symbols. -/
theorem HasCoherentSymbol.of_approx (hc : ∀ k, Commute (symProj (copyPerm Ω k)) (X k))
    (hb : ∃ M, ∀ k, ‖X k * symProj (copyPerm Ω k)‖ ≤ M)
    (ha : ∀ ε > 0, ∃ (X' : ∀ k, Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (f' : (Ω → ℂ) → ℂ),
      HasCoherentSymbol X' f' ∧ (∀ θ ∈ unitSphere, ‖f θ - f' θ‖ ≤ ε) ∧
        ∀ᶠ k in atTop, ‖(X k - X' k) * symProj (copyPerm Ω k)‖ ≤ ε) :
    HasCoherentSymbol X f where
  commute := hc
  bounded := hb
  continuousOn := by
    have hch : ∀ n : ℕ, ∃ g : (Ω → ℂ) → ℂ, ContinuousOn g unitSphere ∧
        ∀ θ ∈ unitSphere, ‖f θ - g θ‖ ≤ 1 / (n + 1) := fun n => by
      obtain ⟨X', f', hX', hf', -⟩ := ha (1 / (n + 1)) (by positivity)
      exact ⟨f', hX'.continuousOn, hf'⟩
    choose g hg hfg using hch
    refine TendstoUniformlyOn.continuousOn (F := g) (p := atTop) ?_
      (Eventually.of_forall hg).frequently
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn θ hθ
    rw [dist_eq_norm]
    refine (hfg n θ hθ).trans_lt (lt_of_le_of_lt ?_ hN)
    gcongr
  approx ε hε := by
    obtain ⟨X', f', hX', hf', hev⟩ := ha (ε / 2) (by positivity)
    obtain ⟨Y, ψ, hY, hψ, hev'⟩ := hX'.approx (ε / 2) (by positivity)
    refine ⟨Y, ψ, hY, fun θ hθ => ?_, ?_⟩
    · calc ‖f θ - ψ θ‖ = ‖(f θ - f' θ) + (f' θ - ψ θ)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add (hf' θ hθ) (hψ θ hθ))
        _ = ε := by ring
    · filter_upwards [hev, hev'] with k h1 h2
      calc ‖(X k - Y k) * symProj (copyPerm Ω k)‖ =
            ‖(X k - X' k) * symProj (copyPerm Ω k) + (X' k - Y k) * symProj (copyPerm Ω k)‖ := by
            rw [← Matrix.add_mul, sub_add_sub_cancel]
        _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add h1 h2)
        _ = ε := by ring

end TensorPower
