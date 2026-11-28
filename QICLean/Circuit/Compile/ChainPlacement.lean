/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.SwapRouting
import QICLean.Circuit.Model.CleanWorkspace
import QICLean.Circuit.Model.UnitaryPlacement
import QICLean.ManyBody.Sites.Placement.PlaceAlong

/-!
# Circuits on an open chain placed in a longer open chain

A product of gates on neighbouring sites of an open chain of `m` sites, placed along an
injection of its sites into an open chain of `N` sites, is a product of gates on neighbouring
sites of the long chain. Along an arbitrary injection every gate acts on an ordered pair of
distinct sites and is routed by SWAP gates, so the gate count grows by a factor of at most
`2 N`; along an injection carrying neighbouring sites to neighbouring sites, in order, the gate
count does not change.

A circuit on `m` logical sites and `b` scratch sites that acts cleanly with a zero workspace,
`QuantumCircuit.IsCleanImplementation` along the basis inclusion
`Matrix.basisInclusion (QuantumCircuit.workspaceEmbedding 0)`, stays clean when its logical
sites are placed among `n` logical sites and its scratch sites among `A` shared scratch sites:
the extra scratch sites stay zero, for every logical input.

Moved from TNLean, `TNLean/Circuit/CleanImplementationPlacement.lean` and the lemma
`isGateProduct_placeAlong_of_succ` of `TNLean/MPS/MPU/EncodedUniformMergingCircuit.lean`, at
commit `49b78ed821` (Apache-2.0). Changes: the consecutive placement is
`QuantumCircuit.IsGateProduct.placeAlong_pathGraph_of_succ`, for any finite local basis.
Source: the placement step in Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex` (placing a circuit at arbitrary distinct
sites increases its gate count by at most `2 N` per gate, and the common workspace).

## Main definitions

* `QuantumCircuit.cleanImplementationSites` — the logical and scratch sites of a small register
  placed in a larger one.

## Main results

* `QuantumCircuit.IsGateProduct.placeAlong_pathGraph` — a product of gates on neighbouring sites
  of an open chain, placed at arbitrary sites of a longer open chain.
* `QuantumCircuit.IsGateProduct.placeAlong_pathGraph_of_succ` — the same on consecutive sites,
  at no extra cost.
* `QuantumCircuit.IsCleanImplementation.placeAlong` — a clean implementation placed in a larger
  register with a common workspace.
* `QuantumCircuit.isGateProduct_isCleanImplementation_placeAlong` — both together.
-/

open Matrix

namespace QuantumCircuit

/-- **A circuit on an open chain placed at arbitrary sites.** Placing a product of `K` gates on
neighbouring sites of the open chain of `m` sites along any injection into the open chain of `N`
sites gives a product of at most `2 N K` gates on neighbouring sites: every gate of the short
chain is a gate on an ordered pair of distinct sites of the long chain, routed by SWAP gates. -/
theorem IsGateProduct.placeAlong_pathGraph {α : Type} [Fintype α] [DecidableEq α] {m N K : ℕ}
    (w : Fin m ↪ Fin N) {U : Matrix (Fin m → α) (Fin m → α) ℂ}
    (hU : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph m)) K U) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph N)) (2 * N * K)
      (ManyBody.placeAlong (X := fun _ ↦ α) w U) := by
  have h := (hU.isUnitaryCircuitOn_graph (Γ := Geometry.sitesAndPairs (Fin N) 0 1)
    (X := fun _ : Fin N ↦ α) (ManyBody.windowEquiv w) fun u v huv ↦
      ⟨Sum.inr ⟨(w u, w v), w.injective.ne huv.ne⟩, (Finset.insert_eq _ _).symm, rfl⟩).2
  convert IsGateProduct.of_sitesAndPairs le_rfl h using 1
  ext z z'
  have hcfg : ∀ y : Fin N → α,
      (ManyBody.siteConfigurationEquiv (ManyBody.windowEquiv w) fun _ ↦ Equiv.refl α).symm
        (fun v : {v // v ∈ Finset.univ.map w} ↦ y v) = fun u ↦ y (w u) := fun y ↦
    funext fun u ↦ by
      rw [ManyBody.siteConfigurationEquiv_symm_apply]
      rfl
  have hoff : (∀ v ∉ Finset.univ.map w, z v = z' v) ↔ ∀ v, (∀ u, w u ≠ v) → z v = z' v := by
    simp
  rw [ManyBody.placeAlong_apply, ManyBody.place_apply, reindex_apply, submatrix_apply]
  split_ifs with h₁ h₂ h₂
  · exact congrArg₂ U (hcfg z).symm (hcfg z').symm
  · exact absurd (hoff.mpr h₁) h₂
  · exact absurd (hoff.mp h₂) h₁
  · rfl

/-- **A circuit on an open chain placed on consecutive sites.** Placing a product of gates of
cost `K` on neighbouring sites of the open chain of `m` sites along an injection into the open
chain of `n` sites that carries neighbouring sites to neighbouring sites, in order, gives a
product of gates of cost `K` on neighbouring sites of the long chain. -/
theorem IsGateProduct.placeAlong_pathGraph_of_succ {α : Type} [Fintype α] [DecidableEq α]
    {m n K : ℕ} (w : Fin m ↪ Fin n)
    (hw : ∀ p p' : Fin m, p'.val = p.val + 1 → (w p').val = (w p).val + 1)
    {V : Matrix (Fin m → α) (Fin m → α) ℂ}
    (hV : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph m)) K V) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) K
      (ManyBody.placeAlong (X := fun _ ↦ α) w V) :=
  hV.place_pathGraph (X := fun _ : Fin n ↦ α) (ManyBody.windowEquiv w)
    (fun p p' h ↦ by simpa only [ManyBody.coe_windowEquiv] using hw p p' h)

variable {d m n b A K : ℕ}

/-- The sites of a register of `m` logical and `b` scratch sites placed in a register of `n`
logical and `A` scratch sites: the logical sites along `e`, the scratch sites along `t`. -/
def cleanImplementationSites (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A) :
    Fin (m + b) ↪ Fin (n + A) where
  toFun := Fin.append (fun j ↦ Fin.castAdd A (e j)) (fun j ↦ Fin.natAdd n (t j))
  inj' := by
    apply Fin.append_injective_iff.mpr
    refine ⟨(Fin.castAdd_injective n A).comp e.injective, ?_, ?_⟩
    · intro i j hij
      apply t.injective
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simp only [Fin.val_natAdd] at hval
      omega
    · intro i j hij
      have hval := congrArg Fin.val hij
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      have := (e i).isLt
      omega

/-- The logical part of a clean placement. -/
@[simp] theorem cleanImplementationSites_castAdd (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    (j : Fin m) :
    cleanImplementationSites e t (Fin.castAdd b j) = Fin.castAdd A (e j) := by
  change Fin.append (fun i ↦ Fin.castAdd A (e i)) (fun i ↦ Fin.natAdd n (t i))
    (Fin.castAdd b j) = _
  exact Fin.append_left _ _ j

/-- The scratch part of a clean placement. -/
@[simp] theorem cleanImplementationSites_natAdd (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    (j : Fin b) :
    cleanImplementationSites e t (Fin.natAdd m j) = Fin.natAdd n (t j) := by
  change Fin.append (fun i ↦ Fin.castAdd A (e i)) (fun i ↦ Fin.natAdd n (t i))
    (Fin.natAdd m j) = _
  exact Fin.append_right _ _ j

variable [NeZero d]

private theorem cleanImplementationSites_agreeOff_iff
    (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    (z : (Fin (n + A) → Fin d)) (x : (Fin n → Fin d)) :
    ((∀ v, (∀ u, cleanImplementationSites e t u ≠ v) →
        z v = Fin.append x (0 : Fin A → Fin d) v) ∧
        ∀ j, z (Fin.natAdd n (t j)) = 0) ↔
      ((∀ j, z (Fin.natAdd n j) = 0) ∧
        ∀ v, (∀ u, e u ≠ v) → z (Fin.castAdd A v) = x v) := by
  constructor
  · rintro ⟨hag, hzero⟩
    constructor
    · intro j
      by_cases hj : ∃ i, t i = j
      · obtain ⟨i, rfl⟩ := hj
        exact hzero i
      · have h := hag (Fin.natAdd n j) (by
          intro p
          refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) p
          · rw [cleanImplementationSites_castAdd]
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
            have := (e i).isLt
            omega
          · rw [cleanImplementationSites_natAdd]
            intro h
            exact hj ⟨i, (Fin.natAdd_injective A n) h⟩)
        simpa only [Fin.append_right, Pi.zero_apply] using h
    · intro j hj
      have h := hag (Fin.castAdd A j) (by
        intro p
        refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) p
        · rw [cleanImplementationSites_castAdd]
          intro h
          exact hj i ((Fin.castAdd_injective n A) h)
        · rw [cleanImplementationSites_natAdd]
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
          have := j.isLt
          omega)
      simpa only [Fin.append_left] using h
  · rintro ⟨hzero, hag⟩
    constructor
    · intro p hp
      refine Fin.addCases (fun j hj ↦ ?_) (fun j _ ↦ ?_) p hp
      · have h := hag j (by
          intro i hi
          apply hj (Fin.castAdd b i)
          simp only [cleanImplementationSites_castAdd, hi])
        simpa only [Fin.append_left] using h
      · simpa only [Fin.append_right, Pi.zero_apply] using hzero j
    · intro j
      exact hzero (t j)

/-- A local clean implementation remains clean after placing its logical
sites and scratch sites in a larger register. The entire larger workspace
starts and ends in zero, for every logical input. -/
theorem IsCleanImplementation.placeAlong
    (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    {U : Matrix ((Fin (m + b) → Fin d)) ((Fin (m + b) → Fin d)) ℂ}
    {Z : Matrix ((Fin m → Fin d)) ((Fin m → Fin d)) ℂ}
    (hlocal : IsCleanImplementation
      (basisInclusion (workspaceEmbedding (n := m) (0 : Fin b → Fin d))) U Z) :
    IsCleanImplementation
      (basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d)))
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) (cleanImplementationSites e t) U)
      (ManyBody.placeAlong (X := fun _ ↦ Fin d) e Z) := by
  classical
  unfold IsCleanImplementation at hlocal ⊢
  ext z x
  have hrestrict :
      (fun u ↦ Fin.append x (0 : Fin A → Fin d) (cleanImplementationSites e t u)) =
        Fin.append (fun u ↦ x (e u)) (0 : Fin b → Fin d) := by
    funext j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) j
    · simp only [cleanImplementationSites_castAdd, Fin.append_left]
    · simp only [cleanImplementationSites_natAdd, Fin.append_right, Pi.zero_apply]
  have hentry := congrArg (fun M ↦ M (fun u ↦ z (cleanImplementationSites e t u))
    (fun u ↦ x (e u))) hlocal
  rw [mul_basisInclusion_apply, basisInclusion_workspaceEmbedding_mul_apply,
    workspaceEmbedding_apply] at hentry
  simp only [cleanImplementationSites_natAdd, cleanImplementationSites_castAdd,
    Pi.zero_apply] at hentry
  rw [mul_basisInclusion_apply, basisInclusion_workspaceEmbedding_mul_apply,
    workspaceEmbedding_apply, ManyBody.placeAlong_apply, hrestrict, hentry,
    ManyBody.placeAlong_apply, ← ite_and, ← ite_and]
  congr 1
  exact propext (cleanImplementationSites_agreeOff_iff e t z x)

/-- **A clean circuit on an open chain placed in a larger register.** A product of `K` gates on
neighbouring sites of the open chain of `m + b` sites that cleanly implements `Z` with a zero
workspace of `b` sites, placed along `cleanImplementationSites e t`, is a product of at most
`2 (n + A) K` gates on neighbouring sites of the open chain of `n + A` sites, and cleanly
implements the placement of `Z` along `e` with the zero workspace of `A` sites. -/
theorem isGateProduct_isCleanImplementation_placeAlong
    (e : Fin m ↪ Fin n) (t : Fin b ↪ Fin A)
    {U : Matrix ((Fin (m + b) → Fin d)) ((Fin (m + b) → Fin d)) ℂ}
    {Z : Matrix ((Fin m → Fin d)) ((Fin m → Fin d)) ℂ}
    (hU : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (m + b))) K U)
    (hlocal : IsCleanImplementation
      (basisInclusion (workspaceEmbedding (n := m) (0 : Fin b → Fin d))) U Z) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph (n + A))) (K * (2 * (n + A)))
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (cleanImplementationSites e t) U) ∧
      IsCleanImplementation
        (basisInclusion (workspaceEmbedding (n := n) (0 : Fin A → Fin d)))
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) (cleanImplementationSites e t) U)
        (ManyBody.placeAlong (X := fun _ ↦ Fin d) e Z) :=
  ⟨(hU.placeAlong_pathGraph (cleanImplementationSites e t)).mono (Nat.mul_comm _ _).le,
    hlocal.placeAlong e t⟩

end QuantumCircuit
