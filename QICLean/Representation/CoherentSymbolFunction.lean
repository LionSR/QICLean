/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.CoherentSymbolLimit
import QICLean.Representation.RegionPowerSymbol
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Continuous functions of sequences with coherent symbols

The last step of the proof of Lemma 6.4 of the area-law paper (*A two-dimensional area law
from a global spectral gap*, `05-replicas.tex`, lines 832–840) passes from the symbol
`|f_θ|²` of `O_k^† O_k` to the symbol `|f_θ|` of `|O_k|`: "Uniform polynomial approximation of
the square root on that interval gives symbols `|f_θ|` for `|O_k|` and `|O_k^†|`, with
arbitrarily small uniform expectation errors. This argument applies whether or not `O_k` is
normal." This file proves the general form: a continuous function of a Hermitian sequence with
a coherent symbol and uniformly bounded spectra has the composed symbol.

## Main declarations

* `TensorPower.HasCoherentSymbol.pow`, `TensorPower.HasCoherentSymbol.aeval`,
  `TensorPower.HasCoherentSymbol.symProj_mul`.
* `TensorPower.HasCoherentSymbol.cfc` — continuous functions of Hermitian sequences.
* `Matrix.IsHermitian.abs_eigenvalues_le` — eigenvalues are bounded by the operator norm.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 6.4 (`lem:symbol`), section file `05-replicas.tex`, lines 832–840.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation Polynomial Filter
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Matrix.IsHermitian

variable {m : Type*} [Fintype m] [DecidableEq m] {A : Matrix m m ℂ}

/-- Eigenvalues of a Hermitian matrix are bounded by its operator norm. -/
theorem abs_eigenvalues_le (hA : A.IsHermitian) (i : m) : |hA.eigenvalues i| ≤ ‖A‖ := by
  have hv := hA.mulVec_eigenvectorBasis i
  have hn : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have h := A.l2_opNorm_mulVec (hA.eigenvectorBasis i)
  rw [hv, hn, mul_one] at h
  have e : (EuclideanSpace.equiv m ℂ).symm (hA.eigenvalues i • (hA.eigenvectorBasis i).ofLp) =
      hA.eigenvalues i • hA.eigenvectorBasis i := rfl
  rwa [e, norm_smul, hn, mul_one, Real.norm_eq_abs] at h

end Matrix.IsHermitian

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
  {X : ∀ k, Matrix (Fin k → Ω) (Fin k → Ω) ℂ} {f : (Ω → ℂ) → ℂ}

/-- The skew operator `𝒟 = |X Π| + |X^† Π| - X - X^†`, with the absolute values taken on the
symmetric subspace (`05-replicas.tex`, line 627). -/
noncomputable def skewOperator (k : ℕ) (Z : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) :
    Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  _root_.cfc Real.sqrt (symProj (copyPerm Ω k) * (Zᴴ * Z)) +
    _root_.cfc Real.sqrt (symProj (copyPerm Ω k) * (Z * Zᴴ)) - Z - Zᴴ

namespace HasCoherentSymbol

theorem pow (hX : HasCoherentSymbol X f) (m : ℕ) :
    HasCoherentSymbol (fun k => X k ^ m) (fun θ => f θ ^ m) := by
  induction m with
  | zero => simpa using const (Ω := Ω) 1
  | succ m ih => simpa [pow_succ] using ih.mul hX

/-- Real polynomials of a sequence with a coherent symbol. -/
theorem aeval (hX : HasCoherentSymbol X f) (p : ℝ[X]) :
    HasCoherentSymbol (fun k => Polynomial.aeval (X k) p)
      (fun θ => Polynomial.aeval (f θ) p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add hq
  | monomial n c =>
    have e1 : ∀ k, Polynomial.aeval (X k) (Polynomial.monomial n c) = (c : ℂ) • X k ^ n :=
        fun k => by
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_one_mul, Complex.coe_smul]
    have e2 : ∀ θ, Polynomial.aeval (f θ) (Polynomial.monomial n c) = (c : ℂ) • f θ ^ n :=
        fun θ => by
      rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_one_mul, Complex.coe_smul]
    simp only [e1, e2]
    exact (hX.pow n).smul (c : ℂ)

/-- Compressing by `Π_k` does not change the coherent symbol. -/
theorem symProj_mul (hX : HasCoherentSymbol X f) :
    HasCoherentSymbol (fun k => symProj (copyPerm Ω k) * X k) f where
  commute k := by
    have hc := hX.commute k
    exact (Commute.refl _).mul_right hc
  bounded := by
    obtain ⟨M, hM⟩ := hX.bounded
    refine ⟨M, fun k => ?_⟩
    rw [Matrix.mul_assoc]
    exact (l2_opNorm_mul _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      l2_opNorm_symProj_le).trans (hM k))
  continuousOn := hX.continuousOn
  approx ε hε := by
    obtain ⟨Y, ψ, hY, hψ, hev⟩ := hX.approx ε hε
    refine ⟨Y, ψ, hY, hψ, ?_⟩
    filter_upwards [hev] with k hk
    have hYc := hY.commute_symProj k
    have h1 : symProj (copyPerm Ω k) * (Y k * symProj (copyPerm Ω k)) =
        Y k * symProj (copyPerm Ω k) := by
      rw [← Matrix.mul_assoc, hYc.eq, Matrix.mul_assoc, symProj_mul_symProj]
    have e : (symProj (copyPerm Ω k) * X k - Y k) * symProj (copyPerm Ω k) =
        symProj (copyPerm Ω k) * ((X k - Y k) * symProj (copyPerm Ω k)) := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, h1, Matrix.mul_assoc]
    rw [e]
    exact (l2_opNorm_mul _ _).trans ((mul_le_of_le_one_left (norm_nonneg _)
      l2_opNorm_symProj_le).trans hk)

/-- **Continuous functions of Hermitian sequences** (`05-replicas.tex`, lines 832–837): if
`X_k` is Hermitian with eigenvalues in `[a, b]`, has coherent symbol `f` with real values in
`[a, b]` on unit vectors, and `φ` is continuous on `[a, b]`, then `φ(X_k)` has coherent
symbol `φ ∘ f`. -/
theorem cfc (hX : HasCoherentSymbol X f) (hH : ∀ k, (X k).IsHermitian) {a b : ℝ}
    (hspec : ∀ k i, (hH k).eigenvalues i ∈ Set.Icc a b)
    (hf : ∀ θ ∈ unitSphere, f θ = ((f θ).re : ℂ) ∧ (f θ).re ∈ Set.Icc a b) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ (Set.Icc a b)) :
    HasCoherentSymbol (fun k => _root_.cfc φ (X k)) (fun θ => (φ (f θ).re : ℂ)) := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hφ
  refine of_approx (fun k => ((hX.commute k).symm.cfc_real φ).symm) ⟨max B 0, fun k => ?_⟩
    fun ε hε => ?_
  · refine (l2_opNorm_mul _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
      l2_opNorm_symProj_le).trans ?_)
    exact (hH k).l2_opNorm_cfc_le φ (le_max_right _ _) fun i =>
      (Real.norm_eq_abs _ ▸ hB _ (hspec k i)).trans (le_max_left _ _)
  · obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b φ hφ ε hε
    refine ⟨fun k => Polynomial.aeval (X k) p, fun θ => Polynomial.aeval (f θ) p, hX.aeval p,
      fun θ hθ => ?_, Eventually.of_forall fun k => ?_⟩
    · obtain ⟨h1, h2⟩ := hf θ hθ
      have hev : Polynomial.aeval (f θ) p = ((p.eval (f θ).re : ℝ) : ℂ) := by
        conv_lhs => rw [h1]
        exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (f θ).re p
      change ‖((φ (f θ).re : ℝ) : ℂ) - Polynomial.aeval (f θ) p‖ ≤ ε
      rw [hev, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact (hp _ h2).le
    · refine (l2_opNorm_mul _ _).trans ((mul_le_of_le_one_right (norm_nonneg _)
        l2_opNorm_symProj_le).trans ?_)
      exact (hH k).l2_opNorm_cfc_sub_aeval_le φ p hε.le fun i => by
        rw [abs_sub_comm]; exact (hp _ (hspec k i)).le

/-- **The absolute value** (`05-replicas.tex`, lines 832–837): if `X_k` has coherent symbol
`f`, then the absolute value `|X_k Π_k| = √(Π_k X_k^† X_k)` has coherent symbol `|f|`. -/
theorem abs (hX : HasCoherentSymbol X f) :
    HasCoherentSymbol (fun k => _root_.cfc Real.sqrt (symProj (copyPerm Ω k) * ((X k)ᴴ * X k)))
      (fun θ => (‖f θ‖ : ℂ)) := by
  set A := fun k => symProj (copyPerm Ω k) * ((X k)ᴴ * X k)
  have hA : HasCoherentSymbol A (fun θ => star (f θ) * f θ) :=
    (hX.conjTranspose.mul hX).symProj_mul
  have hcX : ∀ k, Commute (symProj (copyPerm Ω k)) (X k)ᴴ := fun k => by
    have h : (symProj (copyPerm Ω k) * X k)ᴴ = (X k * symProj (copyPerm Ω k))ᴴ := by
      rw [(hX.commute k).eq]
    rw [conjTranspose_mul, conjTranspose_mul, isHermitian_symProj.eq] at h
    exact h.symm
  have hAeq : ∀ k, A k = (X k * symProj (copyPerm Ω k))ᴴ * (X k * symProj (copyPerm Ω k)) := by
    intro k
    have hc2 : Commute (symProj (copyPerm Ω k)) ((X k)ᴴ * X k) :=
      (hcX k).mul_right (hX.commute k)
    simp only [A]
    rw [conjTranspose_mul, isHermitian_symProj.eq]
    calc symProj (copyPerm Ω k) * ((X k)ᴴ * X k)
        = symProj (copyPerm Ω k) * (symProj (copyPerm Ω k) * ((X k)ᴴ * X k)) := by
          rw [← Matrix.mul_assoc (symProj (copyPerm Ω k)) (symProj (copyPerm Ω k)),
            symProj_mul_symProj]
      _ = symProj (copyPerm Ω k) * (((X k)ᴴ * X k) * symProj (copyPerm Ω k)) := by
          rw [hc2.eq]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hH : ∀ k, (A k).IsHermitian := fun k => by
    rw [hAeq]; exact isHermitian_conjTranspose_mul_self _
  obtain ⟨M, hM⟩ := hX.bounded
  obtain ⟨B, hB0, hB⟩ := hX.exists_bound
  set b := max (M ^ 2) (B ^ 2)
  have hspec : ∀ k i, (hH k).eigenvalues i ∈ Set.Icc 0 b := fun k i => by
    have hpsd : (A k).PosSemidef := by rw [hAeq]; exact posSemidef_conjTranspose_mul_self _
    refine ⟨hpsd.eigenvalues_nonneg i, ?_⟩
    refine (le_abs_self _).trans (((hH k).abs_eigenvalues_le i).trans ?_)
    rw [hAeq, l2_opNorm_conjTranspose_mul_self]
    refine le_trans ?_ (le_max_left _ _)
    have := hM k
    nlinarith [norm_nonneg (X k * symProj (copyPerm Ω k))]
  have hsym : ∀ θ, star (f θ) * f θ = ((‖f θ‖ ^ 2 : ℝ) : ℂ) := fun θ => by
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  have hf : ∀ θ ∈ unitSphere, star (f θ) * f θ = ((star (f θ) * f θ).re : ℂ) ∧
      (star (f θ) * f θ).re ∈ Set.Icc 0 b := fun θ hθ => by
    rw [hsym, Complex.ofReal_re]
    refine ⟨rfl, by positivity, le_trans ?_ (le_max_right _ _)⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hB θ hθ) 2
  have h := hA.cfc hH hspec hf Real.continuous_sqrt.continuousOn
  convert h using 2 with θ
  rw [hsym, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)]

/-- **The skew operator** (`05-replicas.tex`, lines 627–631 and 837–838):
`𝒟_k = |X_k| + |X_k^†| - X_k - X_k^†` on the symmetric subspace has coherent symbol
`2(|f| - Re f)`. -/
theorem skew (hX : HasCoherentSymbol X f) :
    HasCoherentSymbol (fun k => skewOperator k (X k))
      (fun θ => ((2 * (‖f θ‖ - (f θ).re) : ℝ) : ℂ)) := by
  unfold skewOperator
  have h2 := hX.conjTranspose.abs
  simp only [conjTranspose_conjTranspose] at h2
  have h := (hX.abs.add h2).add ((hX.add hX.conjTranspose).smul (-1))
  convert h using 2 with k θ
  · simp only [neg_smul, one_smul, smul_add]
    abel
  · rw [norm_star]
    apply Complex.ext <;> simp
    ring

end HasCoherentSymbol

end TensorPower
