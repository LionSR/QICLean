/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Block
import QICLean.ManyBody.Sites.Subregion
import QICLean.Analysis.Norm.MatrixKroneckerContraction
import QICLean.Algebra.Combinatorics.TupleEquiv

/-!
# Systems changed on a region, and placement between two systems

An operation on a region `D` may change the basis types of the sites of `D`: it prepares or
discards registers there, and leaves the other sites alone. Its input and output systems `X` and
`Y` then agree outside `D`. The system `updateOn X D Z` is `X` with the basis types `Z` on `D`;
it is one such `Y`.

For two systems `X` and `Y` that agree outside `D`, the placement `placeBetween D hXY K` of a
matrix `K` from the configurations of `D` in `X` to those in `Y` is the operator `K ⊗ 1` from
`⊗_v ℂ^{X v}` to `⊗_v ℂ^{Y v}`: it acts as `K` on the sites of `D` and as the identity on the
other sites. When `Y = X` it is the placement `place D K`. Placements on the same region compose
as their matrices do, and the adjoint of a placement is the placement of the adjoint.

The agreement outside `D` is a hypothesis `hXY : ∀ v ∉ D, Y v = X v`, not a definition of `Y`,
so that a placement from `X` to `Y` followed by one from `Y` to `W` is a placement from `X` to
`W`. The identification of the configurations outside `D` of the two systems along `hXY` is the
equivalence `complCast hXY`.

## Main definitions

* `ManyBody.updateOn` — the system `X` with the basis types `Z` on a region.
* `ManyBody.updateOnConfigEquiv` — its configurations, as pairs.
* `ManyBody.pairConfigEquiv` — the configurations of a region of two sites, as pairs.
* `ManyBody.factorConfigEquiv` — the configurations of a system with a factor split off at one
  site, as pairs.
* `ManyBody.complCast` — configurations outside a region of two systems that agree there.
* `ManyBody.placeBetween` — the placement `K ⊗ 1` of a matrix between two systems.

## Main results

* `ManyBody.placeBetween_apply`, `ManyBody.placeBetween_apply_cutEquiv_symm` — its entries.
* `ManyBody.placeBetween_eq_place` — on one system it is the placement.
* `ManyBody.placeBetween_sum` — the placement of a finite sum.
* `ManyBody.placeBetween_mul` — placements on a region compose.
* `ManyBody.placeBetween_conjTranspose` — the adjoint of a placement.
* `ManyBody.placeBetween_reindex_one_kronecker` — a placement beside spectator factors.
* `ManyBody.norm_placeBetween_le`, `ManyBody.norm_submatrix_singleton_le` — norm bounds.
* `ManyBody.placeBetween_piKronecker` — a placed product operator.
* `ManyBody.subregionPlaceBetween`, `ManyBody.placeBetween_subregionPlaceBetween` — a matrix on
  a region extended to a larger region; placing the extension is placing the matrix.
* `ManyBody.reindex_blockConfigEquiv_placeBetween_singleton` — a matrix of one block.
* `ManyBody.reindex_blockConfigEquiv_placeBetween` — a placement on a region of blocks is, on the
  sites, the placement on the preimage of the region.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

universe u

namespace ManyBody

variable {V : Type*}

/-! ### Systems changed on a region -/

section Update

variable [DecidableEq V]

/-- The system `X` with the basis type `Z v` at every site `v` of the region `D`. -/
def updateOn (X : V → Type u) (D : Finset V) (Z : {v // v ∈ D} → Type u) : V → Type u :=
  fun v ↦ if h : v ∈ D then Z ⟨v, h⟩ else X v

variable {X : V → Type u} {D : Finset V} {Z : {v // v ∈ D} → Type u}

theorem updateOn_of_mem {v : V} (hv : v ∈ D) : updateOn X D Z v = Z ⟨v, hv⟩ := by
  simp [updateOn, hv]

theorem updateOn_of_notMem {v : V} (hv : v ∉ D) : updateOn X D Z v = X v := by
  simp [updateOn, hv]

/-- The updated system agrees with `X` outside the region, in the form `placeBetween` takes. -/
theorem updateOn_eq_of_notMem : ∀ v ∉ D, updateOn X D Z v = X v :=
  fun _ hv ↦ updateOn_of_notMem hv

instance [∀ v, Fintype (X v)] [∀ v, Fintype (Z v)] (v : V) : Fintype (updateOn X D Z v) := by
  unfold updateOn; split <;> infer_instance

instance [∀ v, DecidableEq (X v)] [∀ v, DecidableEq (Z v)] (v : V) :
    DecidableEq (updateOn X D Z v) := by
  unfold updateOn; split <;> infer_instance

variable (X D Z) in
/-- A configuration of the updated system is a configuration of `Z` on the sites of `D` and a
configuration of `X` outside `D`. -/
def updateOnConfigEquiv : Config (updateOn X D Z) ≃ Config Z × ComplConfig X D :=
  (cutEquiv (updateOn X D Z) D).trans <|
    Equiv.prodCongr (Equiv.piCongrRight fun v ↦ Equiv.cast (updateOn_of_mem v.2))
      (Equiv.piCongrRight fun v ↦ Equiv.cast (updateOn_of_notMem v.2))

@[simp] theorem updateOnConfigEquiv_apply_fst (σ : Config (updateOn X D Z))
    (v : {v // v ∈ D}) : (updateOnConfigEquiv X D Z σ).1 v = cast (updateOn_of_mem v.2) (σ v) :=
  rfl

@[simp] theorem updateOnConfigEquiv_apply_snd (σ : Config (updateOn X D Z))
    (v : {v // v ∉ D}) :
    (updateOnConfigEquiv X D Z σ).2 v = cast (updateOn_of_notMem v.2) (σ v) :=
  rfl

variable (X) in
/-- The configurations of a region `D` of two distinct sites `a` and `b` are pairs of basis
vectors, the first at `a`. -/
def pairConfigEquiv {a b : V} (hab : a ≠ b) (hD : D = {a, b}) : RegionConfig X D ≃ X a × X b where
  toFun σ := (σ ⟨a, by simp [hD]⟩, σ ⟨b, by simp [hD]⟩)
  invFun x v :=
    if hv : v.1 = a then cast (congrArg X hv.symm) x.1
    else cast (congrArg X (by simpa [hD, hv] using v.2 : v.1 = b).symm) x.2
  left_inv σ := by
    funext ⟨v, hv⟩
    have hv' := hv
    rw [hD, Finset.mem_insert, Finset.mem_singleton] at hv'
    rcases hv' with rfl | rfl
    · simp
    · simp [hab.symm]
  right_inv x := by
    simp [hab.symm]

/-- The two entries of a configuration of a region of two sites. -/
@[simp] theorem pairConfigEquiv_apply {a b : V} (hab : a ≠ b) (hD : D = {a, b})
    (σ : RegionConfig X D) :
    pairConfigEquiv X hab hD σ = (σ ⟨a, by simp [hD]⟩, σ ⟨b, by simp [hD]⟩) :=
  rfl

end Update

/-! ### Splitting off a factor at one site -/

section Factor

variable [DecidableEq V] {W Z : V → Type u} {α : Type u} (p : V) (h : ∀ s ≠ p, W s = Z s)
  (e : W p ≃ α × Z p)

/-- The configurations of a system `W` whose basis at `p` is read as `α × Z p` through `e`, and
which agrees with `Z` at the other sites: pairs of a configuration of the factor `α` and a
configuration of `Z`. -/
def factorConfigEquiv : Config W ≃ α × Config Z :=
  (Equiv.piSplitAt p W).trans <|
    (e.prodCongr (Equiv.piCongrRight fun s : {s // s ≠ p} ↦ Equiv.cast (h s s.2))).trans <|
      (Equiv.prodAssoc _ _ _).trans ((Equiv.refl α).prodCongr (Equiv.piSplitAt p Z).symm)

/-- The factor of a configuration is read at `p`. -/
@[simp] theorem factorConfigEquiv_apply_fst (w : Config W) :
    (factorConfigEquiv p h e w).1 = (e (w p)).1 :=
  rfl

/-- The remaining configuration is the rest of `w` at `p` and `w` elsewhere. -/
theorem factorConfigEquiv_apply_snd_eq_iff (w : Config W) (z : Config Z) :
    (factorConfigEquiv p h e w).2 = z ↔
      (e (w p)).2 = z p ∧ ∀ s (hs : s ≠ p), cast (h s hs) (w s) = z s := by
  change (Equiv.piSplitAt p Z).symm ((e (w p)).2, fun s ↦ cast (h s s.2) (w s)) = z ↔ _
  rw [Equiv.symm_apply_eq, Equiv.piSplitAt_apply, Prod.mk.injEq, funext_iff, Subtype.forall]

/-- A configuration is determined by its factor and its remaining configuration. -/
theorem factorConfigEquiv_eq_iff (w : Config W) (a : α) (z : Config Z) :
    factorConfigEquiv p h e w = (a, z) ↔
      e (w p) = (a, z p) ∧ ∀ s (hs : s ≠ p), cast (h s hs) (w s) = z s := by
  rw [Prod.ext_iff, factorConfigEquiv_apply_fst, factorConfigEquiv_apply_snd_eq_iff,
    Prod.ext_iff, and_assoc]

end Factor

/-! ### Placement between two systems -/

variable {X Y W : V → Type u} {D : Finset V}

/-- The configurations outside `D` of two systems that agree outside `D` are the same. -/
def complCast (hXY : ∀ v ∉ D, Y v = X v) : ComplConfig X D ≃ ComplConfig Y D :=
  Equiv.piCongrRight fun v ↦ Equiv.cast (hXY v v.2).symm

@[simp] theorem complCast_apply (hXY : ∀ v ∉ D, Y v = X v) (z : ComplConfig X D)
    (v : {v // v ∉ D}) : complCast hXY z v = cast (hXY v v.2).symm (z v) :=
  rfl

@[simp] theorem complCast_symm_apply (hXY : ∀ v ∉ D, Y v = X v) (z : ComplConfig Y D)
    (v : {v // v ∉ D}) : (complCast hXY).symm z v = cast (hXY v v.2) (z v) :=
  rfl

@[simp] theorem complCast_rfl : complCast (fun _ _ ↦ rfl : ∀ v ∉ D, X v = X v) = Equiv.refl _ :=
  rfl

theorem complCast_symm (hXY : ∀ v ∉ D, Y v = X v) :
    (complCast hXY).symm = complCast fun v hv ↦ (hXY v hv).symm :=
  rfl

theorem complCast_trans (hXY : ∀ v ∉ D, Y v = X v) (hYW : ∀ v ∉ D, W v = Y v) :
    (complCast hXY).trans (complCast hYW) = complCast fun v hv ↦ (hYW v hv).trans (hXY v hv) :=
  Equiv.ext fun z ↦ funext fun v ↦ by simp

variable [DecidableEq V] [Fintype V] [∀ v, DecidableEq (X v)]

variable (D) in
/-- The placement `K ⊗ 1` of a matrix `K` from the configurations of the region `D` in the
system `X` to those in a system `Y` that agrees with `X` outside `D`: the operator that acts as
`K` on the sites of `D` and as the identity on the other sites. -/
noncomputable def placeBetween (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) : Matrix (Config Y) (Config X) ℂ :=
  reindex (cutEquiv Y D).symm (cutEquiv X D).symm
    (K ⊗ₖ ((complCast hXY).symm.toPEquiv.toMatrix : Matrix (ComplConfig Y D) _ ℂ))

/-- Entries of a placement between two systems: the entry of `K` at the parts of `y` and `x` on
`D` when `y` and `x` agree outside `D`, and zero otherwise. -/
theorem placeBetween_apply (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) (y : Config Y) (x : Config X) :
    placeBetween D hXY K y x =
      if ∀ v (hv : v ∉ D), cast (hXY v hv) (y v) = x v then
        K (fun v ↦ y v) (fun v ↦ x v) else 0 := by
  simp only [placeBetween, reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, mul_ite,
    mul_one, mul_zero]
  exact if_congr ⟨fun h v hv ↦ congrFun h ⟨v, hv⟩, fun h ↦ funext fun v ↦ h v.1 v.2⟩ rfl rfl

/-- A matrix on a region is recovered from its placement between two systems, at any
configuration `z` of the other sites. -/
theorem placeBetween_apply_cutEquiv_symm (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) (a : RegionConfig Y D)
    (b : RegionConfig X D) (z : ComplConfig X D) :
    placeBetween D hXY K ((cutEquiv Y D).symm (a, complCast hXY z)) ((cutEquiv X D).symm (b, z)) =
      K a b := by
  simp [placeBetween, PEquiv.toMatrix_apply]

/-- On one system, the placement between two systems is the placement. -/
theorem placeBetween_eq_place (K : Matrix (RegionConfig X D) (RegionConfig X D) ℂ) :
    placeBetween D (fun _ _ ↦ rfl) K = place D K := by
  rw [placeBetween, place, complCast_rfl, Equiv.refl_symm, Equiv.toPEquiv_refl,
    PEquiv.toMatrix_refl]

@[simp] theorem placeBetween_zero (hXY : ∀ v ∉ D, Y v = X v) :
    placeBetween D hXY (0 : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) = 0 := by
  simp [placeBetween]

theorem placeBetween_add (hXY : ∀ v ∉ D, Y v = X v)
    (K K' : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    placeBetween D hXY (K + K') = placeBetween D hXY K + placeBetween D hXY K' := by
  simp [placeBetween, add_kronecker, submatrix_add]

theorem placeBetween_smul (hXY : ∀ v ∉ D, Y v = X v) (c : ℂ)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    placeBetween D hXY (c • K) = c • placeBetween D hXY K := by
  simp [placeBetween, smul_kronecker, submatrix_smul]

/-- The placement of a difference is the difference of the placements. -/
theorem placeBetween_sub (hXY : ∀ v ∉ D, Y v = X v)
    (K K' : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    placeBetween D hXY K - placeBetween D hXY K' = placeBetween D hXY (K - K') := by
  rw [sub_eq_add_neg, sub_eq_add_neg, placeBetween_add, ← neg_one_smul ℂ K', placeBetween_smul,
    neg_one_smul]

/-- The placement of a finite sum is the sum of the placements. -/
theorem placeBetween_sum (hXY : ∀ v ∉ D, Y v = X v) {ι : Type*} (s : Finset ι)
    (K : ι → Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    placeBetween D hXY (∑ i ∈ s, K i) = ∑ i ∈ s, placeBetween D hXY (K i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, placeBetween_add, ih]

/-- Placements on a region compose: `(K' ⊗ 1)(K ⊗ 1) = K' K ⊗ 1`. -/
theorem placeBetween_mul [∀ v, Fintype (Y v)] [∀ v, DecidableEq (Y v)]
    [Fintype (RegionConfig Y D)] (hXY : ∀ v ∉ D, Y v = X v) (hYW : ∀ v ∉ D, W v = Y v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ)
    (K' : Matrix (RegionConfig W D) (RegionConfig Y D) ℂ) :
    placeBetween D hYW K' * placeBetween D hXY K =
      placeBetween D (fun v hv ↦ (hYW v hv).trans (hXY v hv)) (K' * K) := by
  obtain rfl : ‹Fintype (RegionConfig Y D)› = Pi.instFintype := Subsingleton.elim _ _
  simp only [placeBetween, reindex_apply, Equiv.symm_symm, submatrix_mul_equiv,
    ← mul_kronecker_mul, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, ← Equiv.symm_trans,
    complCast_trans]

/-- The adjoint of a placement between two systems is the placement of the adjoint. -/
theorem placeBetween_conjTranspose [∀ v, DecidableEq (Y v)] (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    (placeBetween D hXY K)ᴴ = placeBetween D (fun v hv ↦ (hXY v hv).symm) Kᴴ := by
  have hC : ((complCast hXY).symm.toPEquiv.toMatrix : Matrix (ComplConfig Y D) _ ℂ)ᴴ =
      (complCast fun v hv ↦ (hXY v hv).symm).symm.toPEquiv.toMatrix := by
    ext a b
    simp only [conjTranspose_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
      Option.some.injEq, apply_ite star, star_one, star_zero]
    exact if_congr ((Equiv.symm_apply_eq _).trans eq_comm) rfl rfl
  simp only [placeBetween, reindex_apply, conjTranspose_submatrix, conjTranspose_kronecker, hC]

/-- A cast of a pair along an equality of second factors is the pair of the first component
and the cast of the second. -/
private theorem cast_prod_eq_iff {W A B : Type u} (h' : A = B) (h : (W × A) = (W × B))
    (z : W × A) (z' : W × B) : cast h z = z' ↔ z.1 = z'.1 ∧ cast h' z.2 = z'.2 := by
  subst h'
  simp [Prod.ext_iff]

/-- **A placement beside spectator factors.** Placing `1 ⊗ K`, with the spectator factor `W v`
in front of the basis of every site of `D`, is placing `K` and tensoring with the identity on
the spectators of all sites. -/
theorem placeBetween_reindex_one_kronecker {W : V → Type} [∀ v, DecidableEq (W v)]
    {X Y : V → Type} [∀ v, DecidableEq (X v)]
    (hXY : ∀ v ∉ D, Y v = X v) (hWXY : ∀ v ∉ D, (W v × Y v) = (W v × X v))
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    placeBetween D hWXY
        (reindex (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ Y v)).symm
          (Equiv.arrowProdEquivProdArrow {v // v ∈ D} (fun v ↦ W v) (fun v ↦ X v)).symm
          ((1 : Matrix (RegionConfig W D) (RegionConfig W D) ℂ) ⊗ₖ K)) =
      reindex (Equiv.arrowProdEquivProdArrow V W Y).symm (Equiv.arrowProdEquivProdArrow V W X).symm
        ((1 : Matrix (Config W) (Config W) ℂ) ⊗ₖ placeBetween D hXY K) := by
  ext y x
  have key : ∀ v (hv : v ∉ D), cast (hWXY v hv) (y v) = x v ↔
      (y v).1 = (x v).1 ∧ cast (hXY v hv) (y v).2 = (x v).2 :=
    fun v hv ↦ cast_prod_eq_iff (hXY v hv) _ _ _
  rw [placeBetween_apply]
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm,
    Equiv.arrowProdEquivProdArrow_apply, kroneckerMap_apply, one_apply, placeBetween_apply]
  by_cases hW : (fun v ↦ (y v).1) = fun v ↦ (x v).1
  · have hWD : (fun v : {v // v ∈ D} ↦ (y v.1).1) = fun v : {v // v ∈ D} ↦ (x v.1).1 :=
      funext fun v ↦ congrFun hW v.1
    rw [ite_eq_left hW, ite_eq_left hWD, one_mul, one_mul]
    exact if_congr ⟨fun h v hv ↦ ((key v hv).mp (h v hv)).2,
      fun h v hv ↦ (key v hv).mpr ⟨congrFun hW v, h v hv⟩⟩ rfl rfl
  · rw [ite_eq_right hW, zero_mul]
    split_ifs with h₁ h₂
    · exact absurd (funext fun v ↦ if hv : v ∈ D then congrFun h₂ ⟨v, hv⟩
        else ((key v hv).mp (h₁ v hv)).1) hW
    · rw [zero_mul]
    · rfl

/-- A placement between two systems does not increase the operator norm. -/
theorem norm_placeBetween_le [∀ v, Fintype (X v)] [∀ v, Fintype (Y v)]
    (hXY : ∀ v ∉ D, Y v = X v) (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    ‖placeBetween D hXY K‖ ≤ ‖K‖ := by
  classical
  refine (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_kronecker_le _ _).trans ?_)
  exact (mul_le_of_le_one_right (norm_nonneg K) (l2_opNorm_toMatrix_toPEquiv_le _))

omit [Fintype V] [∀ v, DecidableEq (X v)] in
/-- A matrix read through the evaluation at the one site of a one-site region does not change its
operator norm bound. -/
theorem norm_submatrix_singleton_le [∀ v, Fintype (X v)] [∀ v, Fintype (Y v)]
    [∀ v, DecidableEq (X v)] (v₀ : V) (A : Matrix (Y v₀) (X v₀) ℂ) :
    ‖A.submatrix (fun y : RegionConfig Y {v₀} ↦ y ⟨v₀, Finset.mem_singleton_self v₀⟩)
      (fun x : RegionConfig X {v₀} ↦ x ⟨v₀, Finset.mem_singleton_self v₀⟩)‖ ≤ ‖A‖ := by
  have hb : ∀ T : V → Type u, Function.Bijective
      (fun y : RegionConfig T {v₀} ↦ y ⟨v₀, Finset.mem_singleton_self v₀⟩) := fun T ↦
    ⟨fun y y' h ↦ funext fun v ↦ by
      obtain rfl : v = ⟨v₀, Finset.mem_singleton_self v₀⟩ :=
        Subtype.ext (Finset.mem_singleton.mp v.2)
      exact h,
    fun a ↦ ⟨fun v ↦ cast (congrArg T (Finset.mem_singleton.mp v.2).symm) a, rfl⟩⟩
  exact l2_opNorm_reindex_le (Equiv.ofBijective _ (hb Y)).symm (Equiv.ofBijective _ (hb X)).symm A

/-- **A placed product operator is a product operator**: placing `⊗_{w ∈ D} K w` between two
systems is the product of the `K w` on `D` and of the identifications of the equal bases outside
`D`. -/
theorem placeBetween_piKronecker (hXY : ∀ v ∉ D, Y v = X v)
    (K : ∀ w : {v // v ∈ D}, Matrix (Y w) (X w) ℂ) :
    placeBetween D hXY (piKronecker K) =
      piKronecker fun v ↦
        if h : v ∈ D then K ⟨v, h⟩ else (Equiv.cast (hXY v h)).toPEquiv.toMatrix := by
  ext y x
  rw [placeBetween_apply]
  simp only [piKronecker_apply]
  have key : ∀ k, (if h : k ∈ D then K ⟨k, h⟩ else (Equiv.cast (hXY k h)).toPEquiv.toMatrix)
      (y k) (x k) = if h : k ∈ D then K ⟨k, h⟩ (y k) (x k) else
        if cast (hXY k h) (y k) = x k then 1 else 0 := fun k ↦ by
    by_cases h : k ∈ D <;> simp [h, PEquiv.toMatrix_apply, eq_comm]
  rw [Finset.prod_congr rfl fun k _ ↦ key k, Fintype.prod_dite]
  simp only [Finset.prod_boole, Finset.mem_univ, true_imp_iff]
  split_ifs with ha hb hb
  · rw [mul_one]
    exact Finset.prod_congr (congrArg (@Finset.univ {v // v ∈ D}) (Subsingleton.elim _ _))
      fun _ _ ↦ rfl
  · exact absurd (fun (w : {a // a ∉ D}) ↦ ha w.1 w.2) hb
  · exact absurd (fun v hv ↦ hb ⟨v, hv⟩) ha
  · rw [mul_zero]

/-! ### Placement between two systems inside a larger region -/

section Subregion

variable {U : Finset V}

/-- The extension of a matrix `K` from the configurations of `D ⊆ U` in `X` to those in a system
`Y` agreeing with `X` outside `D`, to the configurations of `U`, by the identification of the
equal bases on the sites of `U` outside `D`: the placement of `K` in the system of the sites of
`U`. -/
noncomputable def subregionPlaceBetween (hDU : D ⊆ U) (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    Matrix (RegionConfig Y U) (RegionConfig X U) ℂ :=
  placeBetween (X := fun w : {v // v ∈ U} ↦ X w.1) (Y := fun w : {v // v ∈ U} ↦ Y w.1)
    (D.subtype (· ∈ U)) (fun w hw ↦ hXY w.1 (by simpa using hw))
    (reindex (subregionConfigEquiv hDU) (subregionConfigEquiv hDU) K)

omit [Fintype V] in
/-- Entries of the extension: the entry of `K` at the parts on `D` when the two configurations
agree on the sites of `U` outside `D`, and zero otherwise. -/
theorem subregionPlaceBetween_apply (hDU : D ⊆ U) (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) (y : RegionConfig Y U)
    (x : RegionConfig X U) :
    subregionPlaceBetween hDU hXY K y x =
      if ∀ (w : {v // v ∈ U}) (hw : w.1 ∉ D), cast (hXY w.1 hw) (y w) = x w then
        K (fun w ↦ y ⟨w.1, hDU w.2⟩) (fun w ↦ x ⟨w.1, hDU w.2⟩)
      else 0 := by
  rw [subregionPlaceBetween, placeBetween_apply]
  exact if_congr ⟨fun h w hw ↦ h w (by simpa using hw), fun h w hw ↦ h w (by simpa using hw)⟩
    rfl rfl

omit [Fintype V] in
/-- The extension of a sum is the sum of the extensions. -/
theorem subregionPlaceBetween_add (hDU : D ⊆ U) (hXY : ∀ v ∉ D, Y v = X v)
    (K K' : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    subregionPlaceBetween hDU hXY (K + K') =
      subregionPlaceBetween hDU hXY K + subregionPlaceBetween hDU hXY K' := by
  simp only [subregionPlaceBetween, ← placeBetween_add]
  congr 1

omit [Fintype V] in
/-- The extension of a multiple is the multiple of the extension. -/
theorem subregionPlaceBetween_smul (hDU : D ⊆ U) (hXY : ∀ v ∉ D, Y v = X v) (c : ℂ)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    subregionPlaceBetween hDU hXY (c • K) = c • subregionPlaceBetween hDU hXY K := by
  simp only [subregionPlaceBetween, ← placeBetween_smul]
  congr 1

omit [Fintype V] in
/-- The extension does not increase the operator norm. -/
theorem norm_subregionPlaceBetween_le [∀ v, Fintype (X v)] [∀ v, Fintype (Y v)]
    (hDU : D ⊆ U) (hXY : ∀ v ∉ D, Y v = X v)
    (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    ‖subregionPlaceBetween hDU hXY K‖ ≤ ‖K‖ := by
  classical
  exact (norm_placeBetween_le _ _).trans (l2_opNorm_reindex_le _ _ K)

/-- **Nested placement between two systems.** Placing the extension of `K` from `D` to `U`
gives the placement of `K`. -/
theorem placeBetween_subregionPlaceBetween (hDU : D ⊆ U) (hXY : ∀ v ∉ D, Y v = X v)
    (hU : ∀ v ∉ U, Y v = X v) (K : Matrix (RegionConfig Y D) (RegionConfig X D) ℂ) :
    placeBetween U hU (subregionPlaceBetween hDU hXY K) = placeBetween D hXY K := by
  ext σ τ
  rw [placeBetween_apply, placeBetween_apply, subregionPlaceBetween_apply]
  split_ifs with hUc hUD hD hD hD
  · rfl
  · push Not at hD
    obtain ⟨v, hvD, hne⟩ := hD
    by_cases hvU : v ∈ U
    · exact absurd (hUD ⟨v, hvU⟩ hvD) hne
    · exact absurd (hUc v hvU) hne
  · exact absurd (fun (w : {v // v ∈ U}) hw ↦ hD w.1 hw) hUD
  · rfl
  · exact absurd (fun v hvU ↦ hD v fun hvD ↦ hvU (hDU hvD)) hUc
  · rfl

end Subregion

/-! ### Placement between two systems read on blocks -/

section Block

variable {V' : Type} [Fintype V'] [DecidableEq V'] {V₀ : Type} [Fintype V₀] [DecidableEq V₀]
  (f : V₀ → V') {X Y : V₀ → Type}

omit [Fintype V'] [DecidableEq V₀] in
/-- A site of a block outside a region of blocks lies outside the preimage of the region. -/
private theorem notMem_blockPreimage {D' : Finset V'} {b : V'} (hb : b ∉ D')
    (w : {w // w ∈ blockPreimage f {b}}) : w.1 ∉ blockPreimage f D' := by
  have hw := w.2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hw
  simpa [hw] using hb

omit [Fintype V'] [DecidableEq V₀] in
/-- Two systems that agree outside the preimage of a region of blocks agree on the blocks outside
the region. -/
theorem blockSystem_eq_of_notMem {D' : Finset V'} (hY : ∀ v ∉ blockPreimage f D', Y v = X v) :
    ∀ b ∉ D', blockSystem f Y b = blockSystem f X b :=
  fun _ hb ↦ congrArg (fun T : {w // w ∈ blockPreimage f {_}} → Type ↦ (w : _) → T w)
    (funext fun w ↦ hY w.1 (notMem_blockPreimage f hb w))

/-- Blocking commutes with placement between two systems: a matrix placed on the region `D'` of
the blocked systems is, read on the sites, the same matrix placed on the preimage of `D'`. -/
theorem reindex_blockConfigEquiv_placeBetween [∀ v, DecidableEq (X v)] (D' : Finset V')
    (hY : ∀ v ∉ blockPreimage f D', Y v = X v)
    (K : Matrix (RegionConfig (blockSystem f Y) D') (RegionConfig (blockSystem f X) D') ℂ) :
    reindex (blockConfigEquiv f Y) (blockConfigEquiv f X)
        (placeBetween D' (blockSystem_eq_of_notMem f hY) K) =
      placeBetween (blockPreimage f D') hY
        (reindex (blockRegionConfigEquiv f Y D') (blockRegionConfigEquiv f X D') K) := by
  ext σ τ
  have hAB : ∀ {b} (hb : b ∉ D'), (fun w : {w // w ∈ blockPreimage f {b}} ↦ Y w) =
      fun w : {w // w ∈ blockPreimage f {b}} ↦ X w :=
    fun hb ↦ funext fun w ↦ hY w.1 (notMem_blockPreimage f hb w)
  have key : (∀ b (hb : b ∉ D'), cast (blockSystem_eq_of_notMem f hY b hb)
        ((blockConfigEquiv f Y).symm σ b) = (blockConfigEquiv f X).symm τ b) ↔
      ∀ v (hv : v ∉ blockPreimage f D'), cast (hY v hv) (σ v) = τ v := by
    refine ⟨fun h v hv ↦ ?_, fun h b hb ↦ funext fun w ↦
      (cast_pi_apply (hAB hb) _ _ w).trans (h w.1 (notMem_blockPreimage f hb w))⟩
    have hb : f v ∉ D' := by simpa using hv
    have hv' : v ∈ blockPreimage f {f v} := by simp
    exact (cast_pi_apply (hAB hb) _ _ ⟨v, hv'⟩).symm.trans (congrFun (h (f v) hb) ⟨v, hv'⟩)
  rw [reindex_apply, submatrix_apply, placeBetween_apply, placeBetween_apply]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (key.mp h₁) h₂
  · exact absurd (key.mpr h₂) h₁
  · rfl

/-- A matrix of one block, placed at that block of the blocked systems, is, read on the sites,
the same matrix placed on the block. -/
theorem reindex_blockConfigEquiv_placeBetween_singleton [∀ v, DecidableEq (X v)] (b : V')
    (hY : ∀ v ∉ blockPreimage f {b}, Y v = X v)
    (K : Matrix (blockSystem f Y b) (blockSystem f X b) ℂ) :
    reindex (blockConfigEquiv f Y) (blockConfigEquiv f X)
        (placeBetween {b} (blockSystem_eq_of_notMem f hY)
          (K.submatrix (fun y ↦ y ⟨b, Finset.mem_singleton_self b⟩)
            (fun x ↦ x ⟨b, Finset.mem_singleton_self b⟩))) =
      placeBetween (blockPreimage f {b}) hY K := by
  rw [reindex_blockConfigEquiv_placeBetween f {b} hY]
  congr 1

end Block

end ManyBody
