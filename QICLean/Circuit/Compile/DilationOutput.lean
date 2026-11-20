/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PureMarginalApproximation
import QICLean.Circuit.Compile.Dilation

/-!
# Pure outputs of a unitary dilation

A unitary circuit on enlarged sites, with its environments prepared in a basis vector `e₀` and
traced out at the end, is a unitary dilation of the map it computes. If that map sends a pure
state `ψ` to within trace distance `ε` of a pure state `φ`, then the unitary of the circuit
sends `ψ ⊗ e₀` to within `√(2ε)` of a product `φ ⊗ η` with a unit vector `η` of the output
environments. The unitary sends the prepared vector to a unit vector `Ω` whose marginal on the
system is the output of the dilated map, so this is the projection estimate
`Matrix.exists_unit_product_approx_of_pure_marginal` read along the regrouping of the local
products `Z s × F s` into `Config Z × Config F`.

## Main results

* `QuantumCircuit.Circuit.exists_unit_product_approx` — a dilated map sending `ψ` close to the
  pure state `φ` in trace norm has a unitary sending `ψ ⊗ e₀` close to some `φ ⊗ η`.
-/

open Matrix ManyBody

namespace QuantumCircuit

/-- Reindexing a vector along an equivalence preserves its Euclidean norm. -/
private theorem norm_toLp_comp_equiv {α β : Type} [Fintype α] [Fintype β] (σ : α ≃ β)
    (g : β → ℂ) :
    ‖(WithLp.toLp 2 (g ∘ σ) : EuclideanSpace ℂ α)‖ = ‖(WithLp.toLp 2 g : EuclideanSpace ℂ β)‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp σ (fun b ↦ ‖g b‖ ^ 2)

/-- An isometry `Kᴴ K = 1` preserves the Euclidean norm. -/
private theorem norm_toLp_mulVec_of_isometry {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {K : Matrix κ ι ℂ} (hK : Kᴴ * K = 1) (v : ι → ℂ) :
    ‖(WithLp.toLp 2 (K *ᵥ v) : EuclideanSpace ℂ κ)‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℂ ι)‖ := by
  have key : ∀ {n : Type} [Fintype n] (w : n → ℂ),
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ n)‖ ^ 2 = (star w ⬝ᵥ w).re := by
    intro n _ w
    rw [@norm_sq_eq_re_inner ℂ, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    rfl
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [key, key, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hK, one_mulVec]

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {X Z E F : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] [∀ s, Fintype (E s)] [∀ s, DecidableEq (E s)]
  [∀ s, Fintype (F s)] [∀ s, DecidableEq (F s)]

omit [∀ s, DecidableEq (X s)] in
/-- The vector `ψ ⊗ e₀` of the enlarged sites has the norm of `ψ`. -/
private theorem norm_prepared (e₀ : ∀ s, E s) (ψ : EuclideanSpace ℂ (Config X)) :
    ‖(WithLp.toLp 2 (fun w : Config (fun s ↦ X s × E s) ↦
        if (fun s ↦ (w s).2) = e₀ then ψ (fun s ↦ (w s).1) else 0) :
          EuclideanSpace ℂ (Config fun s ↦ X s × E s))‖ = ‖ψ‖ := by
  set v : Config (fun s ↦ X s × E s) → ℂ := fun w ↦
    if (fun s ↦ (w s).2) = e₀ then ψ (fun s ↦ (w s).1) else 0
  rw [← norm_toLp_comp_equiv (Equiv.arrowProdEquivProdArrow S X E).symm v,
    EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  change ∑ f : Config E, ‖if f = e₀ then ψ x else 0‖ ^ 2 = _
  simp [apply_ite, Finset.sum_ite_eq']

/-- **Pure outputs of a unitary dilation.** Let a unitary circuit `c` on the enlarged sites
`X s × E s → Z s × F s`, with the environments prepared in the basis vector `e₀` and the output
environments traced out, send the pure state `ψ` to within trace distance `ε` of the pure state
`φ`: the full trace norm of the difference of the output and `|φ⟩⟨φ|` is at most `ε`. Then the
unitary of the circuit sends `ψ ⊗ e₀` to within `√(2ε)` of `φ ⊗ η` for some unit vector `η` of
the output environments. At `ε = 0` this is the exact pure case: the unitary sends `ψ ⊗ e₀` to
a product `φ ⊗ η`.

Source: arXiv:2103.13367, main text, paragraph "Phases of matter" (the trace-norm criterion);
the projection estimate is `Matrix.exists_unit_product_approx_of_pure_marginal`. -/
theorem Circuit.exists_unit_product_approx (e₀ : ∀ s, E s)
    (c : Circuit Γ KrausGate (fun s ↦ X s × E s) (fun s ↦ Z s × F s))
    (hc : c.Forall KrausGate.ev KrausFamily.IsUnitary)
    (ψ : EuclideanSpace ℂ (Config X)) (φ : EuclideanSpace ℂ (Config Z))
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) {ε : ℝ}
    (herror : rectangularTraceNorm
      (((traceCircuit Γ Z F).map KrausGate.ev ∘ₗ c.map KrausGate.ev ∘ₗ
          (prepareCircuit Γ e₀).map KrausGate.ev)
        (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) -
        vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) ≤ ε)
    (p : c.Index) :
    ∃ η : EuclideanSpace ℂ (Config F), ‖η‖ = 1 ∧
      ‖(WithLp.toLp 2 (c.kraus KrausGate.ev p *ᵥ fun w ↦
          if (fun s ↦ (w s).2) = e₀ then ψ (fun s ↦ (w s).1) else 0) -
        WithLp.toLp 2 (fun w ↦ φ (fun s ↦ (w s).1) * η (fun s ↦ (w s).2)) :
          EuclideanSpace ℂ (Config fun s ↦ Z s × F s))‖ ≤ Real.sqrt (2 * ε) := by
  obtain ⟨u⟩ := Circuit.nonempty_unique_index KrausGate.ev (hc.mono fun _ hK ↦ hK.1)
  let _ : Unique (c.krausFamily KrausGate.ev).Index := u
  have hp : p = default := u.uniq p
  subst hp
  set U := c.kraus KrausGate.ev default
  set v : Config (fun s ↦ X s × E s) → ℂ := fun w ↦
    if (fun s ↦ (w s).2) = e₀ then ψ (fun s ↦ (w s).1) else 0 with hv
  have hUU : Uᴴ * U = 1 := by
    have hTP := Circuit.isTP_krausFamily KrausGate.ev c (hc.mono fun _ hK ↦ hK.isTP)
    rwa [KrausFamily.IsTP, KrausFamily.effect, Fintype.sum_unique] at hTP
  have hprep : (prepareCircuit Γ e₀).map KrausGate.ev
      (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) = vecMulVec v (star v) := by
    ext w w'
    rw [map_prepareCircuit_apply]
    by_cases hw : (fun s ↦ (w s).2) = e₀ <;> by_cases hw' : (fun s ↦ (w' s).2) = e₀ <;>
      simp [hv, hw, hw', vecMulVec_apply]
  have hcirc : c.map KrausGate.ev (vecMulVec v (star v)) =
      vecMulVec (U *ᵥ v) (star (U *ᵥ v)) := by
    rw [Circuit.map, KrausFamily.map_apply, Fintype.sum_unique, mul_vecMulVec, vecMulVec_mul,
      star_mulVec]
    rfl
  let e := Equiv.arrowProdEquivProdArrow S Z F
  let Ω : EuclideanSpace ℂ (Config Z × Config F) := WithLp.toLp 2 ((U *ᵥ v) ∘ e.symm)
  have htrace : ((traceCircuit Γ Z F).map KrausGate.ev ∘ₗ c.map KrausGate.ev ∘ₗ
      (prepareCircuit Γ e₀).map KrausGate.ev)
        (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) =
      partialTraceRight (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hprep, hcirc]
    ext y y'
    rw [map_traceCircuit_apply]
    rfl
  have hΩ : ‖Ω‖ = 1 := by
    rw [norm_toLp_comp_equiv, norm_toLp_mulVec_of_isometry hUU, hv, norm_prepared, hψ]
  obtain ⟨η, hη, hb⟩ :=
    exists_unit_product_approx_of_pure_marginal Ω φ hΩ hφ (htrace ▸ herror)
  refine ⟨η, hη, le_of_eq_of_le ?_ hb⟩
  rw [← WithLp.toLp_sub, ← norm_toLp_comp_equiv e.symm]
  rfl

end QuantumCircuit
