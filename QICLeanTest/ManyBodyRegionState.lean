import QICLean.ManyBody.Sites
import QICLean.ManyBody.Entropy.RegionCovariance
import QICLean.ManyBody.Entropy.RegionEntropy

/-! Signature regressions for arbitrary bases, empty bases, and legacy rewrite behavior. -/

open Matrix
open scoped InnerProductSpace Kronecker ComplexOrder

section ArbitraryBases

variable {V : Type*} [Fintype V] [DecidableEq V]
  {X : V → Type*} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

-- No nonempty basis or reference configuration is needed for the trace argument.
example {D : Finset V} {K : Matrix (ManyBody.RegionConfig X D)
    (ManyBody.RegionConfig X D) ℂ} (hK : IsUnit K.det)
    {ψ : EuclideanSpace ℂ (ManyBody.Config X)}
    (hcomm : K * ManyBody.regionState ψ D = ManyBody.regionState ψ D * K)
    {A : Matrix (ManyBody.Config X) (ManyBody.Config X) ℂ}
    (hA : A ∈ ManyBody.supportedOperators X D) :
    ⟪ψ, toEuclideanLin (ManyBody.place D K * A * ManyBody.place D K⁻¹) ψ⟫_ℂ =
      ⟪ψ, toEuclideanLin A ψ⟫_ℂ :=
  ManyBody.inner_conj_eq_of_mem_supportedOperators hK hcomm hA

end ArbitraryBases

-- A site can carry two independent wires without re-encoding their product as Fin.
example (D : Finset (Fin 2))
    (ψ : EuclideanSpace ℂ (ManyBody.Config (fun _ : Fin 2 ↦ Fin 2 × Fin 3))) :
    (ManyBody.regionState ψ D).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) :=
  ManyBody.trace_regionState D ψ

-- Empty local bases are permitted, even outside the selected region.
example (ψ : EuclideanSpace ℂ (ManyBody.Config (fun _ : Unit ↦ Fin 0))) :
    (ManyBody.regionState ψ (∅ : Finset Unit)).PosSemidef :=
  ManyBody.regionState_posSemidef _ ψ

section Compatibility

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

-- Existing consumers unfold these names before using partial trace lemmas.
example (D : Finset V) (ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    (ManyBody.regionState ψ D).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [ManyBody.regionState_eq_partialTraceRight_cutVector, trace_partialTraceRight, trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
    Entropy.norm_cutVector]
  simp

example (D : Finset V) (ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ManyBody.regionEntropy ψ D =
      vonNeumannEntropy (ManyBody.regionState ψ D) (ManyBody.regionState_isHermitian D ψ) := by
  rw [ManyBody.regionEntropy]

-- Entrywise consumers unfold the Sites definition before running their simp set.
example (D : Finset V) (c : ℂ) (ψ : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    ManyBody.regionState (c • ψ) D = ((‖c‖ ^ 2 : ℝ) : ℂ) • ManyBody.regionState ψ D := by
  ext a b
  simp only [ManyBody.regionState, ManyBody.regionMatrix_apply, vecMulVec_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [PiLp.smul_apply, smul_eq_mul, Pi.star_apply, star_mul',
    Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
  ring

-- The conditional-movement frame computes the old union equivalence's inverse.
omit [Fintype V] in
example {A B : Finset V} (hAB : Disjoint A B)
    (a : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) A))
        (b : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) B)) {v : V} (hv : v ∈ A) :
    (Entropy.regionUnionEquiv hAB).symm (a, b) ⟨v, Finset.mem_union_left B hv⟩ = a ⟨v, hv⟩ := by
  simp only [Entropy.regionUnionEquiv, ManyBody.regionUnionEquiv, Equiv.coe_fn_symm_mk]
  rw [dite_eq_left hv]

end Compatibility

-- TNLean PhysicalIntervalTransport unfolds this legacy name in simp only.
example {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (q : ℕ) (e : V ≃ V') (σ : V' → Fin q) :
    (Entropy.siteConfigurationEquiv (n := fun _ ↦ q) (n' := fun _ ↦ q)
      e (fun _ ↦ Equiv.refl (Fin q))).symm σ = fun v ↦ σ (e v) := by
  simp only [Entropy.siteConfigurationEquiv, Equiv.coe_piCongr_symm,
    Equiv.refl_symm, Equiv.refl_apply]
