/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Model.CleanWorkspace
import QICLean.Circuit.Protocol.ZeroRegister.Conjunction

/-!
# Reflection of the zero data configuration with clean scratch

For a nonempty register of `a` data sites followed by `a` scratch sites, compute the
reversible conjunction of zero tests, apply the phase `-1` when the last scratch site is `1`,
and undo the conjunction. The result is the diagonal unitary whose phase is `-1` exactly on
the configurations whose last scratch site is `1` after the conjunction. On every data
configuration with clean scratch it applies the phase `-1` exactly when the data are all `0`
and returns the scratch to `0`, so it intertwines the reflection `1 - 2 |0⟩⟨0|` of the data
with the inclusion of the clean-scratch configurations. This is the initialized-register
reflection; the empty register, whose reflection is the global phase `-1`, is a separate case.

The declarations restate the algebra of `TNLean/Circuit/ZeroRegisterReflection.lean`
(Apache-2.0). The changes: the scratch phase is the diagonal matrix reading the last scratch
site, with its support on that site stated, instead of a one-site matrix placed there; the
reflection is unitary without a bound on `d`, by its diagonal form instead of a circuit. The gate
counts and the placement of the circuit in a larger chain are not restated here.

## Main definitions

* `QuantumCircuit.zeroScratchPhase` — the phase `-1` when the last scratch site is `1`.
* `QuantumCircuit.zeroRegisterReflection` — compute, phase, uncompute.

## Main results

* `Matrix.diagonal_ite_neg_one_mem_unitaryGroup` — a diagonal matrix of signs is unitary.
* `QuantumCircuit.zeroScratchPhase_mem_supportedOperators` — the phase acts on one site.
* `QuantumCircuit.zeroRegisterReflection_eq_diagonal`,
  `QuantumCircuit.zeroRegisterReflection_mem_unitaryGroup` — the diagonal form.
* `QuantumCircuit.zeroRegisterReflection_apply_clean` — the action on clean scratch.
* `QuantumCircuit.isCleanImplementation_zeroRegisterReflection` — the clean implementation
  `R J = J (1 - 2 |0⟩⟨0|)`.
-/

open Matrix ManyBody

namespace Matrix

/-- A diagonal matrix with entries `-1` and `1` is unitary. -/
theorem diagonal_ite_neg_one_mem_unitaryGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p] :
    diagonal (fun i ↦ if p i then (-1 : ℂ) else 1) ∈ unitaryGroup ι ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  by_cases hi : p i <;> simp [hi]

end Matrix

namespace QuantumCircuit

variable {d a : ℕ} [NeZero d]

/-- The phase `-1` on the configurations whose last scratch site is `1`. -/
def zeroScratchPhase (ha : 0 < a) : Matrix (Fin (a + a) → Fin d) (Fin (a + a) → Fin d) ℂ :=
  diagonal fun z ↦ if z (Fin.natAdd a ⟨a - 1, by omega⟩) = 1 then -1 else 1

/-- The scratch phase acts on the last scratch site. -/
theorem zeroScratchPhase_mem_supportedOperators (ha : 0 < a) :
    zeroScratchPhase (d := d) ha ∈
      supportedOperators (Qudits (Fin (a + a)) d) {Fin.natAdd a ⟨a - 1, by omega⟩} :=
  diagonal_mem_supportedOperators fun σ τ h ↦ by rw [h _ (Finset.mem_singleton_self _)]

/-- Compute the conjunction, apply the scratch phase, and uncompute. A permutation matrix
sends the basis vector of `z` to that of `σ⁻¹ z`, so the computation is the adjoint factor on
the right. -/
noncomputable def zeroRegisterReflection (ha : 0 < a) :
    Matrix (Fin (a + a) → Fin d) (Fin (a + a) → Fin d) ℂ :=
  (zeroConjunctionPerm a).permMatrix ℂ * zeroScratchPhase ha *
    ((zeroConjunctionPerm a).permMatrix ℂ)ᴴ

/-- The reflection is the diagonal phase `-1` on the configurations whose last scratch site
is `1` after the conjunction. -/
theorem zeroRegisterReflection_eq_diagonal (ha : 0 < a) :
    zeroRegisterReflection (d := d) ha = diagonal fun z ↦
      if zeroConjunctionPerm a z (Fin.natAdd a ⟨a - 1, by omega⟩) = 1 then -1 else 1 := by
  rw [zeroRegisterReflection, zeroScratchPhase, conjTranspose_permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext x y
  simp [submatrix_apply, diagonal_apply, Equiv.Perm.inv_def]

/-- The reflection is unitary on all configurations, including those with nonzero scratch. -/
theorem zeroRegisterReflection_mem_unitaryGroup (ha : 0 < a) :
    zeroRegisterReflection (d := d) ha ∈ unitaryGroup (Fin (a + a) → Fin d) ℂ := by
  rw [zeroRegisterReflection_eq_diagonal]
  exact diagonal_ite_neg_one_mem_unitaryGroup _

/-- On every data configuration `x` with clean scratch, the reflection applies the phase `-1`
exactly when `x = 0` and returns the scratch to `0`. -/
theorem zeroRegisterReflection_apply_clean (hd : 2 ≤ d) (ha : 0 < a) (x : Fin a → Fin d)
    (z : Fin (a + a) → Fin d) :
    zeroRegisterReflection ha z (Fin.append x 0) =
      (if ∀ i, x i = 0 then (-1 : ℂ) else 1) * (if z = Fin.append x 0 then 1 else 0) := by
  rw [zeroRegisterReflection_eq_diagonal, diagonal_apply]
  by_cases hz : z = Fin.append x 0
  · subst hz
    simp only [zeroConjunctionPerm_apply_clean_last_eq_one_iff hd ha, ite_true, mul_one]
  · simp [hz]

/-- With clean scratch the reflection implements the reflection `1 - 2 |0⟩⟨0|` of the data:
`R J = J (1 - 2 |0⟩⟨0|)` for the basis inclusion `J` of `x ↦ (x, 0)`. This is an identity of
linear maps, so it holds on superpositions and with a reference system. -/
theorem isCleanImplementation_zeroRegisterReflection (hd : 2 ≤ d) (ha : 0 < a) :
    IsCleanImplementation (basisInclusion (workspaceEmbedding (n := a) (0 : Fin a → Fin d)))
      (zeroRegisterReflection ha)
      (1 - (2 : ℂ) • diagonal fun x : Fin a → Fin d ↦ if x = 0 then (1 : ℂ) else 0) := by
  have hM : (1 - (2 : ℂ) • diagonal fun x : Fin a → Fin d ↦ if x = 0 then (1 : ℂ) else 0) =
      diagonal fun x ↦ if ∀ i, x i = 0 then -1 else 1 := by
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : x = 0
      · subst hx
        norm_num
      · have hx' : ¬∀ i, x i = 0 := fun h ↦ hx (funext h)
        simp [hx, hx']
    · simp [hxy]
  rw [IsCleanImplementation, hM]
  ext z x
  rw [mul_basisInclusion_apply, mul_diagonal, workspaceEmbedding_apply,
    zeroRegisterReflection_apply_clean hd, basisInclusion, submatrix_apply, id, one_apply,
    workspaceEmbedding_apply, mul_comm]

end QuantumCircuit
