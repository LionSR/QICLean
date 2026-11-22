/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Placement

/-!
# Product vectors

On a system of sites `V` with basis `X v` at the site `v`, the product vector
$\bigotimes_{v}\lvert\phi^v\rangle$ of vectors `φ v : X v → ℂ` has the coefficient
$\prod_v\phi^v_{\sigma(v)}$ on the configuration $\sigma$. A product operator `⊗_v m_v` maps it
to the product vector of the images `m_v φ^v`, and its expectation in a product vector is the
product of the on-site expectations. A computational-basis vector is a product vector, so the
diagonal entries of a product of operators supported on disjoint regions factorize.

Moved from TNLean, `TNLean/Circuit/ProductVector.lean`, `TNLean/Circuit/SupportedOperators.lean`
and `TNLean/Circuit/SupportedMatrixElements.lean` at commit `49b78ed821` (Apache-2.0).
Changes: any finite set of sites with any basis `X v` at the site `v`, in place of one local
dimension `d`; the product operators are `Matrix.piKronecker` (TNLean's `Matrix.rectKronecker`),
and the expectations are written `star ψ ⬝ᵥ (A *ᵥ ψ)` (TNLean's `QuantumCircuit.expect`).

## Main definitions

* `QuantumCircuit.productVector` : the product vector $\bigotimes_v\lvert\phi^v\rangle$.

## Main results

* `QuantumCircuit.smul_productVector`, `QuantumCircuit.productVector_pi_smul` : scalars and
  product vectors.
* `QuantumCircuit.piKronecker_mulVec_productVector` : `(⊗_v m_v) (⊗_v |φ_v⟩) = ⊗_v m_v|φ_v⟩`.
* `QuantumCircuit.star_productVector_dotProduct_piKronecker_mulVec` : the expectation of a product
  operator in a product vector is `∏_v ⟨φ_v|m_v|φ_v⟩`.
* `QuantumCircuit.productVector_single` : computational-basis vectors are product vectors.
* `QuantumCircuit.mul_apply_eq_mul_of_mem_supportedOperators` : diagonal entries of products of
  operators supported on disjoint regions factorize.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127), Appendix A, "Product states",
  `Papers/2011.12127/TN-Review-main.tex` lines 2330–2333.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {V : Type*} [Fintype V] {X : V → Type*}

/-- Source: arXiv:2011.12127, lines 2330–2333. The product vector
$\bigotimes_{v}\lvert\phi^v\rangle$ of vectors `φ v : X v → ℂ`, in the computational basis: its
coefficient on the configuration $\sigma$ is $\prod_v\phi^v_{\sigma(v)}$. For the sites
`Fin N` this is $\lvert\phi^1\rangle\otimes\cdots\otimes\lvert\phi^N\rangle$. -/
def productVector (φ : (v : V) → X v → ℂ) : Config X → ℂ :=
  fun σ ↦ ∏ v, φ v (σ v)

/-- A scalar multiple of a product vector is a product vector: the scalar is absorbed into
the vector of one site. -/
theorem smul_productVector [DecidableEq V] (c : ℂ) (φ : (v : V) → X v → ℂ) (v : V) :
    c • productVector φ = productVector (Function.update φ v (c • φ v)) := by
  funext σ
  simp only [productVector, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ v), Function.update_self, Pi.smul_apply,
    smul_eq_mul, mul_assoc]
  congr 2
  exact Finset.prod_congr rfl fun u hu ↦ by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]

/-- Rescaling every factor of a product vector rescales it by the product of the factors. -/
theorem productVector_pi_smul (c : V → ℂ) (φ : (v : V) → X v → ℂ) :
    productVector (fun v ↦ c v • φ v) = (∏ v, c v) • productVector φ := by
  funext σ
  simp [productVector, Finset.prod_mul_distrib]

/-- A product operator maps a product vector to the product of the images:
`(⊗_v m_v) (⊗_v |φ_v⟩) = ⊗_v m_v|φ_v⟩`. The on-site matrices may be rectangular. -/
theorem piKronecker_mulVec_productVector [DecidableEq V] {Y : V → Type*} [∀ v, Fintype (Y v)]
    (m : (v : V) → Matrix (X v) (Y v) ℂ) (φ : (v : V) → Y v → ℂ) :
    piKronecker m *ᵥ productVector φ = productVector fun v ↦ m v *ᵥ φ v := by
  funext σ
  simp only [mulVec, dotProduct, productVector]
  rw [Finset.prod_univ_sum]
  exact Fintype.sum_congr _ _ fun τ ↦ (Finset.prod_mul_distrib).symm

/-- The expectation of a product operator `⊗_v m_v` in a product vector `⊗_v |φ_v⟩` is
`∏_v ⟨φ_v|m_v|φ_v⟩`. -/
theorem star_productVector_dotProduct_piKronecker_mulVec [DecidableEq V] [∀ v, Fintype (X v)]
    (φ : (v : V) → X v → ℂ) (m : (v : V) → Matrix (X v) (X v) ℂ) :
    star (productVector φ) ⬝ᵥ (piKronecker m *ᵥ productVector φ) =
      ∏ v, star (φ v) ⬝ᵥ (m v *ᵥ φ v) := by
  rw [piKronecker_mulVec_productVector]
  simp only [dotProduct, productVector, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum (t := fun _ ↦ Finset.univ)
    (f := fun v (a : X v) ↦ star (φ v a) * (m v *ᵥ φ v) a)).symm

/-- The tensor product of computational-basis vectors is the corresponding basis vector. -/
@[simp]
theorem productVector_single [∀ v, DecidableEq (X v)] [DecidableEq (Config X)]
    (σ : Config X) :
    productVector (fun v ↦ Pi.single (σ v) (1 : ℂ)) = Pi.single σ 1 := by
  funext τ
  simp only [productVector]
  by_cases hτσ : τ = σ
  · subst τ
    simp
  · obtain ⟨v, hv⟩ := Function.ne_iff.mp hτσ
    rw [Pi.single_eq_of_ne hτσ]
    exact Finset.prod_eq_zero (Finset.mem_univ v) (Pi.single_eq_of_ne hv _)

/-- **Diagonal entries of products of disjointly supported operators factor.** -/
theorem mul_apply_eq_mul_of_mem_supportedOperators [DecidableEq V] [∀ v, Fintype (X v)]
    [∀ v, DecidableEq (X v)] {S S' : Finset V} (hSS' : Disjoint S S')
    {A B : Matrix (Config X) (Config X) ℂ} (hA : A ∈ supportedOperators X S)
    (hB : B ∈ supportedOperators X S') (σ : Config X) :
    (A * B) σ σ = A σ σ * B σ σ := by
  simpa only [ite_self] using mul_apply_of_mem_supportedOperators_of_disjoint hA hB hSS' σ σ

end QuantumCircuit
