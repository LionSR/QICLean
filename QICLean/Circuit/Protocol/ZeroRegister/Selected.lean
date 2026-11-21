/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Protocol.ZeroRegister.Reflection

/-!
# Reflection of selected zero flags with a shared clean scratch pool

A family `s` of `a` sites of a register of `n` sites selects flags, and the selected-flags
reflection is the diagonal unitary with phase `-1` on the configurations whose selected flags
are all `0`, that is `1 - 2 P` for the diagonal projection `P` onto these configurations. It
acts only on the selected flags, whatever the other sites hold; for an empty selection it is
the global phase `-1`.

For an injective selection and a scratch pool of `A ≥ a` sites appended to the register, the
zero-register reflection of the selected flags and the first `a` pool sites is a diagonal
unitary on the `n + A` sites, supported on those `a + a` sites, whose entries are those of the
zero-register reflection on the selected sites and the identity elsewhere. On every logical
configuration with the whole pool at `0` it applies the selected-flags reflection and returns
the pool, including its unused sites, to `0`.

The declarations restate the algebra of `TNLean/Circuit/SelectedZeroRegisterReflection.lean`,
`TNLean/Circuit/SelectedZeroRegisterReflectionPool.lean` and
`TNLean/Circuit/SelectedZeroRegisterSupport.lean` (Apache-2.0). The changes: the pool of size
`a` and the larger pool of size `A ≥ a` are one construction; the selected-flags reflection is
defined for any family of sites; the reflection on the larger register is the diagonal matrix
read through the selected sites, with an identity giving its entries as those of the
zero-register reflection placed there, instead of a placement along an injection of sites. The
gate counts are not restated here.

## Main definitions

* `QuantumCircuit.selectedZeroRegisterLogical` — the selected-flags reflection.
* `QuantumCircuit.selectedZeroRegisterSites` — the selected flags followed by the first `a`
  pool sites.
* `QuantumCircuit.selectedZeroRegisterReflection` — the zero-register reflection on these sites.

## Main results

* `QuantumCircuit.selectedZeroRegisterLogical_mem_unitaryGroup`,
  `QuantumCircuit.selectedZeroRegisterLogical_eq_one_sub`,
  `QuantumCircuit.selectedZeroRegisterLogical_empty`,
  `QuantumCircuit.selectedZeroRegisterLogical_mem_supportedOperators`.
* `QuantumCircuit.selectedZeroRegisterReflection_apply` — the entries are those of the
  zero-register reflection on the selected sites and of the identity elsewhere.
* `QuantumCircuit.selectedZeroRegisterReflection_mem_unitaryGroup`,
  `QuantumCircuit.selectedZeroRegisterReflection_mem_supportedOperators`.
* `QuantumCircuit.selectedZeroRegisterReflection_apply_clean`,
  `QuantumCircuit.isCleanImplementation_selectedZeroRegisterReflection` — the action on a clean
  pool.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {d n a A : ℕ}

section Logical

variable [NeZero d]

/-- The selected-flags reflection: the phase `-1` on the configurations whose selected flags
are all `0`, and `1` on the others. -/
def selectedZeroRegisterLogical (s : Fin a → Fin n) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  diagonal fun x ↦ if ∀ j, x (s j) = 0 then -1 else 1

/-- The selected-flags reflection is unitary. -/
theorem selectedZeroRegisterLogical_mem_unitaryGroup (s : Fin a → Fin n) :
    selectedZeroRegisterLogical (d := d) s ∈ unitaryGroup (Fin n → Fin d) ℂ :=
  diagonal_ite_neg_one_mem_unitaryGroup _

/-- The selected-flags reflection is `1 - 2 P` for the diagonal projection `P` onto the
configurations whose selected flags are all `0`. -/
theorem selectedZeroRegisterLogical_eq_one_sub (s : Fin a → Fin n) :
    selectedZeroRegisterLogical (d := d) s =
      1 - (2 : ℂ) • diagonal fun x : Fin n → Fin d ↦
        if ∀ j, x (s j) = 0 then (1 : ℂ) else 0 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hx : ∀ j, x (s j) = 0 <;>
      norm_num [selectedZeroRegisterLogical, diagonal_apply, one_apply, hx]
  · simp [selectedZeroRegisterLogical, hxy]

/-- With no selected flags the reflection is the global phase `-1`. -/
theorem selectedZeroRegisterLogical_empty (s : Fin 0 → Fin n) :
    selectedZeroRegisterLogical (d := d) s = -1 := by
  ext x y
  by_cases hxy : x = y <;> simp [selectedZeroRegisterLogical, hxy]

/-- The selected-flags reflection acts only on the selected flags. -/
theorem selectedZeroRegisterLogical_mem_supportedOperators (s : Fin a → Fin n) :
    selectedZeroRegisterLogical (d := d) s ∈
      supportedOperators (Qudits (Fin n) d) (Finset.univ.image s) :=
  diagonal_mem_supportedOperators fun σ τ h ↦ by
    simp only [h _ (Finset.mem_image_of_mem s (Finset.mem_univ _))]

end Logical

/-- The selected flags followed by the first `a` sites of a pool of `A ≥ a` sites appended to
the register of `n` sites. -/
def selectedZeroRegisterSites (s : Fin a ↪ Fin n) (hpool : a ≤ A) : Fin (a + a) ↪ Fin (n + A) where
  toFun := Fin.append (fun j ↦ Fin.castAdd A (s j)) fun j ↦ Fin.natAdd n (Fin.castLE hpool j)
  inj' := by
    refine Fin.append_injective_iff.mpr ⟨(Fin.castAdd_injective n A).comp s.injective,
      (Fin.natAdd_injective A n).comp (Fin.castLE_injective hpool), fun i j hij ↦ ?_⟩
    have hval := congrArg Fin.val hij
    simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_castLE] at hval
    have := (s i).isLt
    omega

/-- The first half of the sites are the selected flags. -/
@[simp] theorem selectedZeroRegisterSites_castAdd (s : Fin a ↪ Fin n) (hpool : a ≤ A)
    (j : Fin a) : selectedZeroRegisterSites s hpool (Fin.castAdd a j) = Fin.castAdd A (s j) :=
  Fin.append_left (fun j ↦ Fin.castAdd A (s j)) (fun j ↦ Fin.natAdd n (Fin.castLE hpool j)) j

/-- The second half of the sites are the first `a` pool sites. -/
@[simp] theorem selectedZeroRegisterSites_natAdd (s : Fin a ↪ Fin n) (hpool : a ≤ A)
    (j : Fin a) :
    selectedZeroRegisterSites s hpool (Fin.natAdd a j) = Fin.natAdd n (Fin.castLE hpool j) :=
  Fin.append_right (fun j ↦ Fin.castAdd A (s j)) (fun j ↦ Fin.natAdd n (Fin.castLE hpool j)) j

variable [NeZero d]

/-- The zero-register reflection of the selected flags and the first `a` pool sites: the
diagonal phase of the zero-register reflection, read through these sites. -/
noncomputable def selectedZeroRegisterReflection (s : Fin a ↪ Fin n) (hpool : a ≤ A)
    (ha : 0 < a) : Matrix (Fin (n + A) → Fin d) (Fin (n + A) → Fin d) ℂ :=
  diagonal fun z ↦
    if zeroConjunctionPerm a (z ∘ selectedZeroRegisterSites s hpool)
      (Fin.natAdd a ⟨a - 1, by omega⟩) = 1 then -1 else 1

/-- The entries of the reflection are those of the zero-register reflection on the selected
sites, between configurations that agree on the other sites, and `0` otherwise. -/
theorem selectedZeroRegisterReflection_apply (s : Fin a ↪ Fin n) (hpool : a ≤ A) (ha : 0 < a)
    (z z' : Fin (n + A) → Fin d) :
    selectedZeroRegisterReflection s hpool ha z z' =
      if ∀ v ∉ Set.range (selectedZeroRegisterSites s hpool), z v = z' v then
        zeroRegisterReflection ha (z ∘ selectedZeroRegisterSites s hpool)
          (z' ∘ selectedZeroRegisterSites s hpool)
      else 0 := by
  rw [selectedZeroRegisterReflection, zeroRegisterReflection_eq_diagonal, diagonal_apply]
  by_cases hz : z = z'
  · subst hz
    simp
  · rw [ite_eq_right hz]
    split_ifs with hoff
    · refine (diagonal_apply_ne _ fun h ↦ hz (funext fun v ↦ ?_)).symm
      by_cases hv : v ∈ Set.range (selectedZeroRegisterSites s hpool)
      · obtain ⟨p, rfl⟩ := hv
        exact congrFun h p
      · exact hoff v hv
    · rfl

/-- The reflection is unitary. -/
theorem selectedZeroRegisterReflection_mem_unitaryGroup (s : Fin a ↪ Fin n) (hpool : a ≤ A)
    (ha : 0 < a) :
    selectedZeroRegisterReflection (d := d) s hpool ha ∈ unitaryGroup (Fin (n + A) → Fin d) ℂ :=
  diagonal_ite_neg_one_mem_unitaryGroup _

/-- The reflection acts only on the selected flags and the first `a` pool sites. -/
theorem selectedZeroRegisterReflection_mem_supportedOperators (s : Fin a ↪ Fin n)
    (hpool : a ≤ A) (ha : 0 < a) :
    selectedZeroRegisterReflection (d := d) s hpool ha ∈
      supportedOperators (Qudits (Fin (n + A)) d)
        (Finset.univ.image (selectedZeroRegisterSites s hpool)) := by
  refine diagonal_mem_supportedOperators fun σ τ h ↦ ?_
  have hcomp : σ ∘ selectedZeroRegisterSites s hpool = τ ∘ selectedZeroRegisterSites s hpool :=
    funext fun p ↦ h _ (Finset.mem_image_of_mem _ (Finset.mem_univ p))
  simp only [hcomp]

/-- Through the selected sites, a logical configuration with a clean pool is the selected flags
followed by clean scratch. -/
private theorem append_zero_comp_selectedZeroRegisterSites (s : Fin a ↪ Fin n) (hpool : a ≤ A)
    (x : Fin n → Fin d) :
    Fin.append x (0 : Fin A → Fin d) ∘ selectedZeroRegisterSites s hpool =
      Fin.append (fun j ↦ x (s j)) 0 := by
  funext p
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) p
  · simp only [Function.comp_apply, selectedZeroRegisterSites_castAdd, Fin.append_left]
  · simp only [Function.comp_apply, selectedZeroRegisterSites_natAdd, Fin.append_right,
      Pi.zero_apply]

/-- On every logical configuration `x` with a clean pool, the reflection applies the phase
`-1` exactly when the selected flags of `x` are all `0` and returns the whole pool to `0`. -/
theorem selectedZeroRegisterReflection_apply_clean (hd : 2 ≤ d) (s : Fin a ↪ Fin n)
    (hpool : a ≤ A) (ha : 0 < a) (x : Fin n → Fin d) (z : Fin (n + A) → Fin d) :
    selectedZeroRegisterReflection s hpool ha z (Fin.append x 0) =
      (if ∀ j, x (s j) = 0 then (-1 : ℂ) else 1) * (if z = Fin.append x 0 then 1 else 0) := by
  rw [selectedZeroRegisterReflection, diagonal_apply]
  by_cases hz : z = Fin.append x 0
  · subst hz
    simp only [append_zero_comp_selectedZeroRegisterSites,
      zeroConjunctionPerm_apply_clean_last_eq_one_iff hd ha, ite_true, mul_one]
  · simp [hz]

/-- With a clean pool the reflection implements the selected-flags reflection: `R J = J Z` for
the basis inclusion `J` of `x ↦ (x, 0)`. The whole pool, including its unused sites, is the
workspace. -/
theorem isCleanImplementation_selectedZeroRegisterReflection (hd : 2 ≤ d) (s : Fin a ↪ Fin n)
    (hpool : a ≤ A) (ha : 0 < a) :
    IsCleanImplementation (basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d)))
      (selectedZeroRegisterReflection s hpool ha) (selectedZeroRegisterLogical s) := by
  rw [IsCleanImplementation]
  ext z x
  rw [mul_basisInclusion_apply, selectedZeroRegisterLogical, mul_diagonal,
    workspaceEmbedding_apply, selectedZeroRegisterReflection_apply_clean hd,
    basisInclusion, submatrix_apply, id, one_apply, workspaceEmbedding_apply, mul_comm]

end QuantumCircuit
