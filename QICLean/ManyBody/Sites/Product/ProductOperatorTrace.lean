/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Placement.Basic

/-!
# Linear maps and traces against product operators

On a system of sites `V` with basis `X v` at the site `v`, the product operators `⊗_v m_v`
span all operators. Two linear maps on the operators therefore agree once they agree on the
product operators. For a product operator `σ = ⊗_v σ_v` and operators `A`, `B` supported on
disjoint regions, the traces factorize as `tr(σ A B) tr σ = tr(σ A) tr(σ B)`; no normalization
of the factors `σ_v` is assumed (with `tr σ_v = 1` this is `ManyBody.trace_piKronecker_mul_mul`).

Moved from TNLean, `TNLean/Circuit/SupportedOperators.lean`, restated on a system of sites
with any basis `X v` at the site `v` in place of one local dimension `Fin d`. The choice of
Hermitian factors is moved from TNLean,
`TNLean/MPS/Symmetry/StringOrder/PhysicalStringBlockEndpoints.lean` at commit `600676ccac`.

## Main results

* `ManyBody.linearMap_ext_piKronecker` — linear maps agreeing on the product operators are
  equal.
* `ManyBody.trace_piKronecker_mul_mul_mul_trace` — product operators factorize traces of
  products of operators supported on disjoint regions.
* `ManyBody.exists_isHermitian_piKronecker_ne_zero` — a nonzero linear functional on the
  operators of `n` sites is nonzero at a product of Hermitian one-site matrices.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), Supplemental Material, proof of Theorem 1.
-/

open Matrix
open scoped BigOperators

namespace ManyBody

variable {V : Type*} [Fintype V] {X : V → Type*}

/-- Two linear maps on the operators of a system of sites agree once they agree on the product
operators `⊗_v m_v`. -/
theorem linearMap_ext_piKronecker [∀ v, Finite (X v)] {M : Type*} [AddCommMonoid M]
    [Module ℂ M] (Φ Ψ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] M)
    (h : ∀ m : (v : V) → Matrix (X v) (X v) ℂ, Φ (piKronecker m) = Ψ (piKronecker m)) :
    Φ = Ψ := by
  classical
  have : ∀ v, Fintype (X v) := fun v ↦ Fintype.ofFinite (X v)
  apply LinearMap.ext
  intro A
  have hA : A ∈ supportedOperators X Finset.univ := by simp
  induction hA using supportedOperators_induction with
  | prod m _ => exact h m
  | add A B _ _ hA hB => rw [map_add, map_add, hA, hB]
  | smul c A _ hA => rw [map_smul, map_smul, hA]

variable [DecidableEq V] [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- Product operators factorize traces of products of operators supported on disjoint regions:
`tr(σ A B) tr σ = tr(σ A) tr(σ B)` for `σ = ⊗_v σ_v`. -/
theorem trace_piKronecker_mul_mul_mul_trace {S S' : Finset V} (hSS' : Disjoint S S')
    (σ : (v : V) → Matrix (X v) (X v) ℂ) {A B : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X S) (hB : B ∈ supportedOperators X S') :
    trace (piKronecker σ * (A * B)) * trace (piKronecker σ) =
      trace (piKronecker σ * A) * trace (piKronecker σ * B) := by
  let φ := traceLinearMap (Config X) ℂ ℂ ∘ₗ LinearMap.mulLeft ℂ (piKronecker σ)
  rw [mul_comm]
  refine eq_of_mem_supportedOperators₂
    (trace (piKronecker σ) • (LinearMap.mul ℂ _).compr₂ φ)
    ((LinearMap.mul ℂ ℂ).compl₁₂ φ φ) (fun m m' hm hm' ↦ ?_) hA hB
  change trace (piKronecker σ) * trace (piKronecker σ * (piKronecker m * piKronecker m')) =
    trace (piKronecker σ * piKronecker m) * trace (piKronecker σ * piKronecker m')
  simp only [piKronecker_mul, trace_piKronecker, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases hi : i ∈ S
  · simp [hm' i (Finset.disjoint_left.mp hSS' hi), mul_comm]
  · simp [hm i hi]

/-- A linear functional on the operators of `n` sites of dimension `d` that does not vanish
identically does not vanish at some product `⊗ᵢ pᵢ` of Hermitian one-site matrices. -/
theorem exists_isHermitian_piKronecker_ne_zero
    {n d : ℕ} (f : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ →ₗ[ℂ] ℂ)
    {X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} (hX : f X ≠ 0) :
    ∃ p : Fin n → Matrix (Fin d) (Fin d) ℂ,
      (∀ i, (p i).IsHermitian) ∧ f (Matrix.piKronecker p) ≠ 0 := by
  classical
  have hunit : ∃ σ τ : Fin n → Fin d, f (Matrix.single σ τ 1) ≠ 0 := by
    by_contra! h
    have hf : f = 0 := by
      apply Matrix.ext_linearMap
      intro σ τ
      apply LinearMap.ext
      intro c
      change f (Matrix.single σ τ c) = 0
      have hs : Matrix.single σ τ c = c • Matrix.single σ τ (1 : ℂ) := by simp
      rw [hs, map_smul, h σ τ, smul_zero]
    exact hX (by rw [hf]; rfl)
  obtain ⟨σ, τ, hστ⟩ := hunit
  let p₀ : Fin n → Matrix (Fin d) (Fin d) ℂ := fun i => Matrix.single (σ i) (τ i) 1
  have hp₀ : Matrix.piKronecker p₀ = Matrix.single σ τ 1 := by
    ext a b
    simp only [Matrix.piKronecker_apply, p₀, Matrix.single_apply]
    rw [Finset.prod_boole]
    congr 1
    apply propext
    simp only [Finset.mem_univ, true_implies]
    constructor
    · intro h
      exact ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩
    · rintro ⟨rfl, rfl⟩
      simp
  let k : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin d) (Fin d) ℂ)
      (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
    MultilinearMap.pi fun a => MultilinearMap.pi fun b =>
      (MultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compLinearMap
        (fun i => (LinearMap.proj (b i) : (Fin d → ℂ) →ₗ[ℂ] ℂ).comp
          (LinearMap.proj (a i) : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Fin d → ℂ)))
  let F := f.compMultilinearMap k
  have hF (p : Fin n → Matrix (Fin d) (Fin d) ℂ) :
      F p = f (Matrix.piKronecker p) := rfl
  have hpartial : ∀ S : Finset (Fin n),
      ∃ p : Fin n → Matrix (Fin d) (Fin d) ℂ,
        (∀ i ∈ S, (p i).IsHermitian) ∧ F p ≠ 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨p₀, by simp, by simpa [hF, hp₀] using hστ⟩
    | @insert i S hi ih =>
        obtain ⟨p, hp, hpne⟩ := ih
        obtain ⟨H, K, hH, hK, hpi⟩ := Matrix.exists_isHermitian_eq_add_smul_I (p i)
        have heq : F p = F (Function.update p i H) +
            Complex.I * F (Function.update p i K) := by
          conv_lhs => rw [← Function.update_eq_self i p]
          rw [hpi, F.map_update_add, F.map_update_smul, smul_eq_mul]
        have hchoose : ∃ M : Matrix (Fin d) (Fin d) ℂ,
            M.IsHermitian ∧ F (Function.update p i M) ≠ 0 := by
          by_cases hz : F (Function.update p i H) = 0
          · refine ⟨K, hK, ?_⟩
            intro hzero
            exact hpne (by rw [heq, hz, hzero, mul_zero, add_zero])
          · exact ⟨H, hH, hz⟩
        obtain ⟨M, hM, hMne⟩ := hchoose
        refine ⟨Function.update p i M, ?_, hMne⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa using hM
        · have hji : j ≠ i := by intro h; exact hi (h ▸ hj)
          simpa [Function.update_of_ne hji] using hp j hj
  obtain ⟨p, hp, hpne⟩ := hpartial Finset.univ
  exact ⟨p, fun i => hp i (Finset.mem_univ i), hpne⟩

end ManyBody
