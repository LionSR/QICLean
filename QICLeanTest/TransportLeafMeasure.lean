/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.LeafMeasure

/-! Literal old/new leaf measures, unconditioned finiteness, and zero-copy mass. -/

open Matrix MeasureTheory Set TensorPower TensorPower.ReplicaTransport Entropy
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TransportLeafMeasureTest

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : ℕ} {H : Type*} [DecidableEq H] {C : H → Type*}
  [∀ h, DecidableEq (C h)]
variable (D : TransportData V K H C) (n : V → ℕ) [∀ v, NeZero (n v)]
variable (t : ℝ) (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ)
  (p : ℝ) (h : H) (c : C h)

-- Finiteness at an arbitrary real parameter does not take transport admissibility,
-- positivity, symmetry, nonzero-vector, or interior-parameter hypotheses.
example : IsFiniteMeasure (D.transportLeafMeasure n t k pre p ⟨h, none⟩) := inferInstance

example : IsFiniteMeasure (D.transportLeafMeasure n t k pre (-7) ⟨h, some c⟩) := inferInstance

example : Measurable (D.transportLeafDensity n t k pre p ⟨h, some c⟩) :=
  D.measurable_transportLeafDensity n t k pre p ⟨h, some c⟩

example : Integrable (D.transportLeafDensity n t k pre p ⟨h, none⟩)
    (volume.prod (unitaryHaar (SiteConfig n))) :=
  D.integrable_transportLeafDensity n t k pre p ⟨h, none⟩

example : D.transportLeafMeasure n t k pre 0 ⟨h, some c⟩ = 0 := by simp

example : D.transportLeafMeasure n t k pre 1 ⟨h, none⟩ = 0 := by simp

example : D.transportLeafMeasure n t k 0 p ⟨h, none⟩ = 0 ∧
    D.transportLeafMeasure n t k 0 p ⟨h, some c⟩ = 0 := by simp

-- Both leaf kinds use the actual accepted state and exactly the same Fourier factor.
example (hD : D.IsAdmissible) (ht : 0 ≤ t) (hc : D.CrossBandCommute n t k)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂D.transportLeafMeasure n t k pre p ⟨h, none⟩) =
      ∫ u, Matrix.Transport.fourierWeight u *
        realCoherentIntegral k (TransportData.base n) (D.state n t k pre p ⟨h, none⟩ u) f :=
  D.integral_transportLeafMeasure n t k pre p ⟨h, none⟩ hD ht hc hf

example (hD : D.IsAdmissible) (ht : 0 ≤ t) (hc : D.CrossBandCommute n t k)
    {f : (SiteConfig n → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂D.transportLeafMeasure n t k pre p ⟨h, some c⟩) =
      ∫ u, Matrix.Transport.fourierWeight u *
        realCoherentIntegral k (TransportData.base n) (D.state n t k pre p ⟨h, some c⟩ u) f :=
  D.integral_transportLeafMeasure n t k pre p ⟨h, some c⟩ hD ht hc hf

example (hD : D.IsAdmissible) (ht : 0 ≤ t) (hc : D.CrossBandCommute n t k)
    (hs : pre ∈ symmetricSubspace k (fun v => Fin (n v))) (hn : pre ≠ 0)
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    (D.transportLeafMeasure n t k pre p ⟨h, none⟩).real univ = 1 / 2 ∧
      (D.transportLeafMeasure n t k pre p ⟨h, some c⟩).real univ = 1 / 2 :=
  ⟨D.transportLeafMeasure_real_univ n t k pre p ⟨h, none⟩ hD ht hc hs hn hp,
    D.transportLeafMeasure_real_univ n t k pre p ⟨h, some c⟩ hD ht hc hs hn hp⟩

-- A concrete round with one history and one choice, zero bands, one two-level site.
-- Its prevector is explicitly supplied, even at zero copies.
private def datum : TransportData Unit 0 Unit (fun _ => Unit) where
  histTree := .leaf ()
  choiceTree := fun _ => .leaf ()
  old := fun _ => Fin.elim0
  move := fun _ _ => Fin.elim0

private theorem datum_admissible : datum.IsAdmissible where
  histWeight_pos := by intro h; cases h; simp [datum, MeanTree.weight]
  choiceWeight_pos := by intro h c; cases h; cases c; simp [datum, MeanTree.weight]
  old_isPartition := by intro h g; exact Fin.elim0 g
  move_isValid := by intro h c g; exact Fin.elim0 g

private theorem datum_commute (k : ℕ) : datum.CrossBandCommute (fun _ => 2) 0 k := by
  intro j j' g
  exact Fin.elim0 g

private def scalarPre : Config 0 (fun _ : Unit => Fin 2) → ℂ :=
  tensorVec 0 (Pi.single (TransportData.base (fun _ : Unit => 2)) 1)

private theorem scalarPre_ne_zero : scalarPre ≠ 0 := by
  intro hz
  have hval := congrFun hz (Fin.elim0 : Config 0 (fun _ : Unit => Fin 2))
  simpa [scalarPre, tensorVec] using hval

private theorem scalarPre_symmetric :
    scalarPre ∈ symmetricSubspace 0 (fun _ : Unit => Fin 2) :=
  tensorVec_mem_symmetricSubspace _

example (j : Σ _ : Unit, Option Unit) :
    (datum.transportLeafMeasure (fun _ => 2) 0 0 scalarPre (1 / 2) j).real univ = 1 / 2 :=
  datum.transportLeafMeasure_real_univ (fun _ => 2) 0 0 scalarPre (1 / 2) j
    datum_admissible le_rfl (datum_commute 0) scalarPre_symmetric scalarPre_ne_zero (by norm_num)

-- Active endpoints remain mass one half; only the opposite leaves are zero.
example : (datum.transportLeafMeasure (fun _ => 2) 0 0 scalarPre 0 ⟨(), none⟩).real univ =
    1 / 2 := by
  apply datum.transportLeafMeasure_real_univ_of_weight_ne_zero (fun _ => 2) 0 0 scalarPre
    0 ⟨(), none⟩ datum_admissible le_rfl (datum_commute 0) scalarPre_symmetric scalarPre_ne_zero
  simp [TransportData.tree, MeanTree.weight_interpTree_old, datum,
    projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by simp), MeanTree.weight]

example : (datum.transportLeafMeasure (fun _ => 2) 0 0 scalarPre 1 ⟨(), some ()⟩).real univ =
    1 / 2 := by
  apply datum.transportLeafMeasure_real_univ_of_weight_ne_zero (fun _ => 2) 0 0 scalarPre
    1 ⟨(), some ()⟩ datum_admissible le_rfl (datum_commute 0) scalarPre_symmetric scalarPre_ne_zero
  simp [TransportData.tree, MeanTree.weight_interpTree_new, datum,
    projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by simp), MeanTree.weight]

end TransportLeafMeasureTest
