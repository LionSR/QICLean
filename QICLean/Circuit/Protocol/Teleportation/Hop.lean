/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Real.ComplexSqrt
import QICLean.Circuit.Core.Qudit
import QICLean.Circuit.Core.LocalGate
import QICLean.Circuit.Core.SiteControlled
import QICLean.Circuit.Model.Measurement
import QICLean.ManyBody.Sites.Relabel

/-!
# One teleportation hop for qudits

The paragraph "Tree-RG circuit with measurements" of arXiv:2307.01696 moves registers next to
each other by teleportation: "creating nearest-neighbor entangled pairs, then performing
simultaneous measurements, and correcting (without postselection) based on the measurement
outcomes". This file proves one step of such a teleportation, a hop across two sites, for
qudits of any dimension `d` on any finite set of sites and any geometry. Chains of hops,
performed in one round of depth at most `2`, are in `QICLean.Circuit.Protocol.Teleportation.Round`.

A *hop* consists of three distinct sites `c`, `e`, `f` and two cells of the geometry whose
regions are `{e, f}` and `{c, e}`. With labels in `ℤ_d`, `ζ = e^{2πi/d}` and the Fourier
matrix `F = d^{-1/2} (ζ^{ab})_{a,b}`:

* the gate of the first layer on `{e, f}` applies `F` at `e`, then
  `|a⟩_e |b⟩_f ↦ |a⟩_e |b + a⟩_f`; from `|0⟩_e |0⟩_f` it prepares the maximally entangled
  pair `d^{-1/2} ∑ⱼ |j⟩_e |j⟩_f`;
* the gate of the second layer on `{c, e}` applies `|a⟩_c |b⟩_e ↦ |a⟩_c |b - a⟩_e`, then
  `F` at `c`;
* the sites `c` and `e` are measured in the computational basis.

For the outcomes `z_c`, `z_e`, the content of `c` is found at `f`, acted on by `X^{z_e} Z^{z_c}`
(`|q⟩ ↦ ζ^{z_c q} |q + z_e⟩`), the measured sites carry `|z_c⟩` and `|z_e⟩`, and the amplitude is
`1/d` (`QuantumCircuit.TeleportHop.pre_mulVec`). The inverse of these one-site unitaries is a
correction.

## Main definitions

* `QuantumCircuit.IsZeroOn`, `QuantumCircuit.zeroOnSubmodule` — the vectors with `|0⟩` at the
  sites of a set.
* `QuantumCircuit.TeleportHop` — a hop on a geometry.
* `QuantumCircuit.TeleportHop.pairGate₁`, `QuantumCircuit.TeleportHop.pairGate₂` — the two
  two-qudit gates, and `QuantumCircuit.TeleportHop.gate₁`, `QuantumCircuit.TeleportHop.gate₂`
  their placements.
* `QuantumCircuit.TeleportHop.pre`, `QuantumCircuit.TeleportHop.frame`.

## Main results

* `QuantumCircuit.place_single_self_mulVec_apply` — a placed matrix unit `|m⟩⟨m|` is the
  projection onto the configurations restricting to `m`.
* `QuantumCircuit.piKronecker_update_one_mulVec_apply` — a one-site operator on a vector.
* `QuantumCircuit.IsZeroOn.mulVec_of_mem_supportedOperators`,
  `QuantumCircuit.IsZeroOn.sitePermOp_mulVec_image`,
  `QuantumCircuit.IsZeroOn.sitePermOp_mulVec_of_mapsTo`.
* `QuantumCircuit.TeleportHop.pre_mulVec` — one hop.

The declarations restate `TNLean/Circuit/Teleportation/Hop.lean` and
`TNLean/Circuit/Teleportation/ZeroSubspace.lean` at commit `414a18fb88` (Apache-2.0). The
changes: any finite type of sites and any geometry in place of the ring, the two cells of a hop
given with their regions; the gates are placements of two-qudit matrices along
`ManyBody.pairEquiv`; the projections onto outcomes are placed matrix units; the
permutations of sites are `ManyBody.sitePermOp`; the generalized Pauli matrix is written out in
the frame.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Tree-RG circuit with measurements".
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), Example 2 ("Fixed points in 1D": an ancilla is
  teleported through entangled pairs between neighbouring sites, "which can be done via LOCC").
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S]

/-! ### Projections onto outcomes and one-site operators -/

section Projection

variable {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- **Projections onto outcomes.** The matrix unit `|m⟩⟨m|` placed on `D` keeps the
configurations whose restriction to `D` is `m` and annihilates the others. -/
theorem place_single_self_mulVec_apply {D : Finset S} (m : RegionConfig X D) (v : Config X → ℂ)
    (σ : Config X) :
    (place D (single m m (1 : ℂ)) *ᵥ v) σ =
      if ∀ i (hi : i ∈ D), σ i = m ⟨i, hi⟩ then v σ else 0 := by
  rw [place_mulVec_apply, Finset.sum_eq_single m
    (fun a _ ha ↦ by rw [single_apply, ite_eq_right fun h ↦ ha h.2.symm, zero_mul])
    (fun h ↦ absurd (Finset.mem_univ m) h)]
  by_cases h : ∀ i (hi : i ∈ D), σ i = m ⟨i, hi⟩
  · have hm : (fun v : {v // v ∈ D} ↦ σ v) = m := funext fun v ↦ h v.1 v.2
    rw [ite_eq_left h, single_apply, ite_eq_left ⟨hm.symm, rfl⟩, one_mul, ← hm]
    exact congrArg v ((cutEquiv X D).symm_apply_apply σ)
  · rw [ite_eq_right h, single_apply,
      ite_eq_right fun h' ↦ h fun i hi ↦ (congrFun h'.1 ⟨i, hi⟩).symm,
      zero_mul]

/-- The projections onto the restrictions of one configuration to two regions multiply to the
projection onto its restriction to their union. -/
theorem place_single_union (D D' : Finset S) (z : Config X) :
    place (D ∪ D') (single (fun i ↦ z i) (fun i ↦ z i) (1 : ℂ)) =
      place D (single (fun i ↦ z i) (fun i ↦ z i) 1) *
        place D' (single (fun i ↦ z i) (fun i ↦ z i) 1) := by
  refine ext_iff_mulVec.mpr fun v ↦ funext fun σ ↦ ?_
  rw [← mulVec_mulVec]
  simp only [place_single_self_mulVec_apply, Finset.mem_union, or_imp, forall_and, ite_and]

/-- The projections onto the restrictions of one configuration commute. -/
theorem commute_place_single (D D' : Finset S) (z : Config X) :
    Commute (place D (single (fun i ↦ z i) (fun i ↦ z i) (1 : ℂ)))
      (place D' (single (fun i ↦ z i) (fun i ↦ z i) 1)) := by
  rw [Commute, SemiconjBy, ← place_single_union, ← place_single_union, Finset.union_comm]

/-- **A one-site operator on a vector.** The operator `u` at the site `t` and the identity
elsewhere maps `v` to `y ↦ ∑ⱼ u_{y_t, j} v(y[t ↦ j])`. -/
theorem piKronecker_update_one_mulVec_apply (t : S) (u : Matrix (X t) (X t) ℂ) (v : Config X → ℂ)
    (y : Config X) :
    (piKronecker (Function.update (fun s ↦ (1 : Matrix (X s) (X s) ℂ)) t u) *ᵥ v) y =
      ∑ j, u (y t) j * v (Function.update y t j) := by
  rw [← placeAt_eq_piKronecker t u, placeAt_mulVec_apply]

end Projection

/-! ### Vectors with `|0⟩` at given sites -/

section ZeroOn

variable {d : ℕ} [NeZero d]

/-- The vector `v` has `|0⟩` at the sites of `D`: it vanishes at every configuration with a
nonzero label at a site of `D`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" (the entangled pairs are
created on sites prepared in `|0⟩`). -/
def IsZeroOn (D : Finset S) (v : Config (Qudits S d) → ℂ) : Prop :=
  ∀ x, v x ≠ 0 → ∀ i ∈ D, x i = 0

omit [Fintype S] [DecidableEq S] in
theorem IsZeroOn.mono {D D' : Finset S} {v : Config (Qudits S d) → ℂ} (h : IsZeroOn D' v)
    (hD : D ⊆ D') : IsZeroOn D v :=
  fun x hx i hi ↦ h x hx i (hD hi)

omit [Fintype S] [DecidableEq S] in
theorem IsZeroOn.smul {D : Finset S} {v : Config (Qudits S d) → ℂ} (h : IsZeroOn D v) (c : ℂ) :
    IsZeroOn D (c • v) :=
  fun x hx ↦ h x fun h0 ↦ hx (by simp [h0])

/-- The subspace of the vectors with `|0⟩` at every site of `D`.

Source: arXiv:2307.01696, paragraphs "Tree-RG circuit with measurements" and "Long-range MPS
using measurements". -/
def zeroOnSubmodule (D : Finset S) : Submodule ℂ (Config (Qudits S d) → ℂ) where
  carrier := {v | IsZeroOn D v}
  zero_mem' := fun _ hx ↦ (hx rfl).elim
  add_mem' := by
    intro u v hu hv x hx i hi
    by_cases hux : u x = 0
    · exact hv x (fun hvx ↦ hx (by simp [hux, hvx])) i hi
    · exact hu x hux i hi
  smul_mem' := fun c _ hv ↦ hv.smul c

omit [Fintype S] [DecidableEq S] in
@[simp] theorem mem_zeroOnSubmodule {D : Finset S} {v : Config (Qudits S d) → ℂ} :
    v ∈ zeroOnSubmodule D ↔ IsZeroOn D v :=
  Iff.rfl

/-- A vector has `|0⟩` on `D` exactly when the projection onto `|0⟩` at the sites of `D` fixes
it. -/
theorem isZeroOn_iff_place_single_mulVec {D : Finset S} {v : Config (Qudits S d) → ℂ} :
    IsZeroOn D v ↔ place D (single (0 : RegionConfig (Qudits S d) D) 0 (1 : ℂ)) *ᵥ v = v := by
  constructor
  · intro hv
    funext x
    rw [place_single_self_mulVec_apply]
    split_ifs with h
    · rfl
    · by_contra h0
      exact h fun i hi ↦ hv x (Ne.symm h0) i hi
  · intro hv x hx i hi
    rw [← hv, place_single_self_mulVec_apply] at hx
    by_contra hne
    exact hx (by rw [ite_eq_right fun h ↦ hne (h i hi)])

/-- An operator acting on sites outside `D` keeps `|0⟩` at the sites of `D`. -/
theorem IsZeroOn.mulVec_of_mem_supportedOperators {D T : Finset S}
    {v : Config (Qudits S d) → ℂ} (h : IsZeroOn D v) (hDT : Disjoint D T)
    {A : Matrix (Config (Qudits S d)) (Config (Qudits S d)) ℂ}
    (hA : A ∈ supportedOperators (Qudits S d) T) : IsZeroOn D (A *ᵥ v) := by
  rw [isZeroOn_iff_place_single_mulVec] at h ⊢
  rw [mulVec_mulVec, (commute_of_mem_supportedOperators_of_disjoint
    (place_mem_supportedOperators _) hA hDT).eq, ← mulVec_mulVec, h]

/-- A one-site operator at a site outside `D` keeps `|0⟩` at the sites of `D`. -/
theorem IsZeroOn.piKronecker_update_one_mulVec {D : Finset S} {v : Config (Qudits S d) → ℂ}
    (h : IsZeroOn D v) {t : S} (ht : t ∉ D) (u : Matrix (Fin d) (Fin d) ℂ) :
    IsZeroOn D
      (piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) t u) *ᵥ v) := by
  intro y hy i hi
  rw [piKronecker_update_one_mulVec_apply] at hy
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  have := h _ (right_ne_zero_of_mul hj) i hi
  rwa [Function.update_of_ne (by rintro rfl; exact ht hi)] at this

/-- Permuting the sites moves the sites carrying `|0⟩`. -/
theorem IsZeroOn.sitePermOp_mulVec_image {D : Finset S} {v : Config (Qudits S d) → ℂ}
    (h : IsZeroOn D v) (π : Equiv.Perm S) : IsZeroOn (D.image π) (sitePermOp π *ᵥ v) := by
  intro y hy j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  rw [sitePermOp_mulVec] at hy
  exact h _ hy i hi

/-- If the permutation `π` maps no site outside `D` into `D'`, it moves the sites carrying `|0⟩`
from `D` onto `D'`. -/
theorem IsZeroOn.sitePermOp_mulVec_of_mapsTo {D D' : Finset S} {v : Config (Qudits S d) → ℂ}
    (h : IsZeroOn D v) {π : Equiv.Perm S} (hπ : ∀ x, x ∉ D → π x ∉ D') :
    IsZeroOn D' (sitePermOp π *ᵥ v) := by
  refine (h.sitePermOp_mulVec_image π).mono fun y hy ↦ Finset.mem_image.mpr ⟨π.symm y, ?_,
    π.apply_symm_apply y⟩
  by_contra hx
  exact hπ _ hx (by simpa using hy)

end ZeroOn

/-! ### One hop -/

/-- A hop of a teleportation chain on the geometry `Γ`: three distinct sites `c`, `e`, `f`, and
two cells `b₁`, `b₂` whose regions are `{e, f}` and `{c, e}`. The content of `c` is teleported
to `f` through the maximally entangled pair prepared on `{e, f}`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("creating
nearest-neighbor entangled pairs"). -/
structure TeleportHop (Γ : Geometry S) where
  /-- The site whose content is teleported. -/
  c : S
  /-- The site of the pair next to `c`, measured with `c`. -/
  e : S
  /-- The site receiving the content. -/
  f : S
  /-- The cell of the pair `{e, f}`. -/
  b₁ : Γ.Cell
  /-- The cell of the pair `{c, e}`. -/
  b₂ : Γ.Cell
  cell_b₁ : Γ.cell b₁ = {e, f}
  cell_b₂ : Γ.cell b₂ = {c, e}
  c_ne_e : c ≠ e
  c_ne_f : c ≠ f
  e_ne_f : e ≠ f

namespace TeleportHop

variable {Γ : Geometry S} (h : TeleportHop Γ) (d : ℕ)

/-- The first two-qudit gate of a hop: `F` at the first qudit, then
`|a⟩ |b⟩ ↦ |a⟩ |b + a⟩`. Its entries are `F_{p₁ q₁} [p₂ - p₁ = q₂]`. -/
noncomputable def pairGate₁ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  of fun p q ↦ Qudit.fourier d p.1 q.1 * if p.2 - p.1 = q.2 then 1 else 0

/-- The second two-qudit gate of a hop: `|a⟩ |b⟩ ↦ |a⟩ |b - a⟩`, then `F` at the first qudit.
Its entries are `F_{p₁ q₁} [p₂ = q₂ - q₁]`. -/
noncomputable def pairGate₂ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  of fun p q ↦ Qudit.fourier d p.1 q.1 * if p.2 = q.2 - q.1 then 1 else 0

variable {d} [NeZero d]

theorem pairGate₁_mem_unitaryGroup : pairGate₁ d ∈ unitaryGroup (Fin d × Fin d) ℂ := by
  have e : pairGate₁ d = Equiv.Perm.permMatrix ℂ (Equiv.prodShear (Equiv.refl (Fin d))
      fun a ↦ Equiv.subRight a : Equiv.Perm (Fin d × Fin d)) *
        (Qudit.fourier d ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    ext p q
    simp only [pairGate₁, of_apply, mul_apply, kroneckerMap_apply, one_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_eq_single (p.1, p.2 - p.1) fun x hx ↦ by simp [Ne.symm hx]]
    simp
  rw [e]
  exact Submonoid.mul_mem _ (Equiv.Perm.permMatrix_mem_unitaryGroup _)
    (kronecker_mem_unitary (Qudit.fourier_mem_unitaryGroup d) (one_mem _))

theorem pairGate₂_mem_unitaryGroup : pairGate₂ d ∈ unitaryGroup (Fin d × Fin d) ℂ := by
  have e : pairGate₂ d = (Qudit.fourier d ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *
      Equiv.Perm.permMatrix ℂ (Equiv.prodShear (Equiv.refl (Fin d))
        fun a ↦ Equiv.addRight a : Equiv.Perm (Fin d × Fin d)) := by
    ext p q
    simp only [pairGate₂, of_apply, mul_apply, kroneckerMap_apply, one_apply,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, mul_ite, mul_one, mul_zero]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single q.1, Finset.sum_eq_single (q.2 - q.1)]
    · simp
    · intro b _ hb
      rw [ite_eq_right fun h ↦ hb (eq_sub_of_add_eq (congrArg Prod.snd h))]
    · simp
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ ↦ ite_eq_right fun h ↦ ha (congrArg Prod.fst h)
    · simp
  rw [e]
  exact Submonoid.mul_mem _
    (kronecker_mem_unitary (Qudit.fourier_mem_unitaryGroup d) (one_mem _))
    (Equiv.Perm.permMatrix_mem_unitaryGroup _)

/-- The gate of the first layer: `pairGate₁` placed on `{e, f}`, the first qudit at `e`. -/
noncomputable def gate₁ : Matrix (Config (Qudits S d)) (Config (Qudits S d)) ℂ :=
  place ({h.e} ∪ {h.f})
    ((pairGate₁ d).submatrix (pairEquiv _ h.e_ne_f) (pairEquiv _ h.e_ne_f))

/-- The gate of the second layer: `pairGate₂` placed on `{c, e}`, the first qudit at `c`. -/
noncomputable def gate₂ : Matrix (Config (Qudits S d)) (Config (Qudits S d)) ℂ :=
  place ({h.c} ∪ {h.e})
    ((pairGate₂ d).submatrix (pairEquiv _ h.c_ne_e) (pairEquiv _ h.c_ne_e))

theorem gate₁_mem_unitaryGroup : h.gate₁ (d := d) ∈ unitaryGroup (Config (Qudits S d)) ℂ :=
  place_mem_unitaryGroup (submatrix_equiv_mem_unitary.mpr pairGate₁_mem_unitaryGroup)

theorem gate₂_mem_unitaryGroup : h.gate₂ (d := d) ∈ unitaryGroup (Config (Qudits S d)) ℂ :=
  place_mem_unitaryGroup (submatrix_equiv_mem_unitary.mpr pairGate₂_mem_unitaryGroup)

omit [NeZero d] in
theorem gate₁_mem_supportedOperators :
    h.gate₁ (d := d) ∈ supportedOperators (Qudits S d) (Γ.cell h.b₁) := by
  rw [h.cell_b₁, Finset.insert_eq]
  exact place_mem_supportedOperators _

omit [NeZero d] in
theorem gate₂_mem_supportedOperators :
    h.gate₂ (d := d) ∈ supportedOperators (Qudits S d) (Γ.cell h.b₂) := by
  rw [h.cell_b₂, Finset.insert_eq]
  exact place_mem_supportedOperators _

/-- The operator of one hop before the correction, for the outcome `z`: the two gates followed by
the projection onto `|z_c⟩` at `c` and `|z_e⟩` at `e`. -/
noncomputable def pre (z : Config (Qudits S d)) :
    Matrix (Config (Qudits S d)) (Config (Qudits S d)) ℂ :=
  place {h.c, h.e} (single (fun i ↦ z i) (fun i ↦ z i) 1) * h.gate₂ * h.gate₁

/-- The one-site unitaries left by one hop: `|0⟩ ↦ |z_c⟩` at `c`, `|0⟩ ↦ |z_e⟩` at `e`, and
`X^{z_e} Z^{z_c}`, mapping `|q⟩` to `ζ^{z_c q} |q + z_e⟩`, at `f`. -/
noncomputable def frame (z : Config (Qudits S d)) : S → Matrix (Fin d) (Fin d) ℂ :=
  Function.update (Function.update
    (Function.update 1 h.c (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.c))))
    h.e (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.e)))) h.f
    (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.e)) *
      diagonal fun q : Fin d ↦ Complex.exp (2 * Real.pi * Complex.I / d) ^ ((z h.c : ℕ) * q))

omit [NeZero d] in
/-- The diagonal factor `Z^z` of the frame is unitary: its entries are powers of a root of
unity. -/
private theorem diagonal_pow_mem_unitaryGroup (k : ℕ) :
    (diagonal fun q : Fin d ↦ Complex.exp (2 * Real.pi * Complex.I / d) ^ (k * q)) ∈
      unitaryGroup (Fin d) ℂ := by
  refine diagonal_mem_unitary.mpr (Unitary.mem_iff.mpr ⟨?_, ?_⟩) <;>
  · funext q
    have h1 : ‖Complex.exp (2 * Real.pi * Complex.I / d)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    simp only [Pi.mul_apply, Pi.star_apply, Pi.one_apply, RCLike.star_def]
    first
      | rw [Complex.conj_mul', norm_pow, h1, one_pow]; simp
      | rw [Complex.mul_conj', norm_pow, h1, one_pow]; simp

omit [Fintype S] in
theorem frame_mem_unitaryGroup (z : Config (Qudits S d)) (i : S) :
    h.frame z i ∈ unitaryGroup (Fin d) ℂ := by
  simp only [frame, Function.update_apply]
  split_ifs
  · exact Submonoid.mul_mem _ (Equiv.Perm.permMatrix_mem_unitaryGroup _)
      (diagonal_pow_mem_unitaryGroup _)
  · exact Equiv.Perm.permMatrix_mem_unitaryGroup _
  · exact Equiv.Perm.permMatrix_mem_unitaryGroup _
  · exact one_mem _

omit [Fintype S] in
theorem frame_of_ne (z : Config (Qudits S d)) {i : S} (hc : i ≠ h.c) (he : i ≠ h.e)
    (hf : i ≠ h.f) : h.frame z i = 1 := by
  simp [frame, Function.update_of_ne, hc, he, hf]

omit [NeZero d] in
/-- The entries of the Fourier matrix as powers of `ζ = e^{2πi/d}`. -/
private theorem fourier_apply_pow (a b : Fin d) :
    Qudit.fourier d a b = Complex.invSqrt d *
      Complex.exp (2 * Real.pi * Complex.I / d) ^ ((a : ℕ) * b) := by
  rw [Qudit.fourier_apply, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- **One hop.** On a vector with `|0⟩` at `e` and `f`, the hop for the outcome `z` is `1/d`
times the exchange of `c` and `f` followed by the one-site unitaries `|0⟩ ↦ |z_c⟩` at `c`,
`|0⟩ ↦ |z_e⟩` at `e`, and `X^{z_e} Z^{z_c}` at `f`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" (teleportation through a
nearest-neighbour entangled pair). -/
theorem pre_mulVec (z : Config (Qudits S d)) {v : Config (Qudits S d) → ℂ}
    (hv : IsZeroOn {h.e, h.f} v) :
    h.pre z *ᵥ v = (d : ℂ)⁻¹ •
      (piKronecker (h.frame z) *ᵥ (sitePermOp (Equiv.swap h.c h.f) *ᵥ v)) := by
  have hce := h.c_ne_e
  have hcf := h.c_ne_f
  have hef := h.e_ne_f
  set s : ℂ := Complex.invSqrt d with hs
  have hF0 : ∀ a, Qudit.fourier d a 0 = s := fun a ↦ by simp [fourier_apply_pow, s]
  have hss : s * s = (d : ℂ)⁻¹ := by
    rw [hs, Complex.invSqrt_mul_self (Nat.cast_nonneg _)]
    push_cast
    rfl
  have hve : ∀ x : Config (Qudits S d), x h.e ≠ 0 → v x = 0 := fun x hx ↦ by
    by_contra hne; exact hx (hv x hne h.e (by simp))
  have hvf : ∀ x : Config (Qudits S d), x h.f ≠ 0 → v x = 0 := fun x hx ↦ by
    by_contra hne; exact hx (hv x hne h.f (by simp))
  -- The first layer.
  have hG1 : ∀ w, (h.gate₁ *ᵥ v) w =
      s * v (Function.update (Function.update w h.e 0) h.f (w h.f - w h.e)) := by
    intro w
    rw [gate₁, place_pairEquiv_mulVec, Fintype.sum_prod_type, Finset.sum_eq_single 0]
    · simp [pairGate₁, hF0]
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ ↦ ?_
      rw [hve, mul_zero]
      rwa [Function.update_of_ne hef, Function.update_self]
    · simp
  -- The second layer.
  have hG2 : ∀ y, (h.gate₂ *ᵥ (h.gate₁ *ᵥ v)) y =
      Qudit.fourier d (y h.c) (y h.f - y h.e) * s *
        v (Function.update (Function.update (Function.update y h.c (y h.f - y h.e)) h.e 0)
          h.f 0) := by
    intro y
    have hinner : ∀ a : Fin d, ∑ b : Fin d, pairGate₂ d (y h.c, y h.e) (a, b) *
        (h.gate₁ *ᵥ v) (Function.update (Function.update y h.c a) h.e b) =
          Qudit.fourier d (y h.c) a * (s * v (Function.update (Function.update
            (Function.update y h.c a) h.e 0) h.f (y h.f - (y h.e + a)))) := by
      intro a
      rw [Finset.sum_eq_single (y h.e + a)]
      · simp only [pairGate₂, of_apply, add_sub_cancel_right, ite_true, mul_one, hG1,
          Function.update_idem, Function.update_self]
        rw [Function.update_of_ne hef.symm, Function.update_of_ne hcf.symm]
      · intro b _ hb
        simp only [pairGate₂, of_apply]
        rw [ite_eq_right fun h' ↦ hb (by rw [h', sub_add_cancel]), mul_zero, zero_mul]
      · simp
    rw [gate₂, place_pairEquiv_mulVec, Fintype.sum_prod_type]
    simp only [hinner]
    rw [Finset.sum_eq_single (y h.f - y h.e)]
    · rw [add_sub_cancel, sub_self, ← mul_assoc]
    · intro a _ ha
      rw [hvf, mul_zero, mul_zero]
      rw [Function.update_self, sub_ne_zero]
      intro h'
      exact ha (by rw [h', add_sub_cancel_left])
    · simp
  -- The frame is a product of three one-site operators.
  have hframe : piKronecker (h.frame z) =
      piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) h.c
          (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.c)))) *
        (piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) h.e
            (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.e)))) *
          piKronecker (Function.update (fun _ ↦ (1 : Matrix (Fin d) (Fin d) ℂ)) h.f
            (Equiv.Perm.permMatrix ℂ (Equiv.subRight (z h.e)) * diagonal fun q : Fin d ↦
              Complex.exp (2 * Real.pi * Complex.I / d) ^ ((z h.c : ℕ) * q)))) := by
    rw [piKronecker_mul, piKronecker_mul]
    congr 1
    funext i
    simp only [frame, Function.update_apply, Pi.one_apply]
    clear hG1 hG2 hve hvf hss hF0
    split_ifs <;> simp_all
  funext y
  have hL : (h.pre z *ᵥ v) y = if y h.c = z h.c ∧ y h.e = z h.e then
      (h.gate₂ *ᵥ (h.gate₁ *ᵥ v)) y else 0 := by
    rw [pre, ← mulVec_mulVec, ← mulVec_mulVec, place_single_self_mulVec_apply]
    simp
  rw [hL, hG2, Pi.smul_apply, smul_eq_mul, hframe, ← mulVec_mulVec, ← mulVec_mulVec]
  simp only [piKronecker_update_one_mulVec_apply, sitePermOp_mulVec, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, mul_apply,
    diagonal_apply, mul_ite, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, Equiv.subRight_apply, Function.update_apply,
    hce.symm, hcf.symm, hef.symm, ↓reduceIte]
  by_cases he : y h.e = z h.e
  · by_cases hc : y h.c = z h.c
    · rw [ite_eq_left ⟨hc, he⟩, fourier_apply_pow, ← hs, hc, he]
      have hcfg : Function.update (Function.update (Function.update y h.c (y h.f - z h.e)) h.e 0)
          h.f 0 = Function.update (Function.update (Function.update y h.c (z h.c - z h.c)) h.e
            (z h.e - z h.e)) h.f (y h.f - z h.e) ∘ ⇑(Equiv.swap h.c h.f) := by
        funext i
        by_cases hic : i = h.c
        · subst hic
          simp [hce, hcf]
        by_cases hif : i = h.f
        · subst hif
          simp [Function.update_apply, hcf]
        rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hic hif]
        simp only [Function.update_apply]
        split_ifs <;> simp
      rw [hcfg, ← hss]
      ring
    · rw [ite_eq_right fun h' ↦ hc h'.1, hvf, mul_zero, mul_zero]
      simp only [Function.comp_apply, Equiv.swap_apply_right, Function.update_apply, hcf, hce,
        ↓reduceIte]
      exact sub_ne_zero.mpr hc
  · rw [ite_eq_right fun h' ↦ he h'.2, hve, mul_zero, mul_zero]
    simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hce.symm hef,
      Function.update_apply, hef, ↓reduceIte]
    exact sub_ne_zero.mpr he

end TeleportHop

end QuantumCircuit
