/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap.KrausFamily
import QICLean.ManyBody.Sites.Placement

/-!
# Products of Kraus families over the sites

A Kraus family `K v` from `X v` to `Y v` at every site `v` gives the Kraus family `⊗_v K v` from
the configurations of `X` to those of `Y`: its Kraus operators are indexed by a choice `j` of an
index at every site, and each is the product operator `⊗_v (K v)_{j v}`. When every factor is
trace-preserving, so is the product.

## Main definitions

* `ManyBody.prodFamily` — the product of a Kraus family at every site.

## Main results

* `ManyBody.map_prodFamily_piKronecker` — the product family maps `⊗_v σ_v` to `⊗_v (K v)(σ_v)`.
* `KrausFamily.IsTP.prodFamily` — a product of trace-preserving families is trace-preserving.
-/

open Matrix

namespace ManyBody

variable {V : Type} [Fintype V] [DecidableEq V] {X Y : V → Type}

/-- The product `⊗_v K v` of a Kraus family at every site: the operators `⊗_v (K v)_{j v}`, one
for every choice `j` of an index at every site. -/
def prodFamily (K : (v : V) → KrausFamily (X v) (Y v)) : KrausFamily (Config X) (Config Y) :=
  ⟨(v : V) → (K v).Index, fun j ↦ piKronecker fun v ↦ (K v).op (j v)⟩

@[simp] theorem prodFamily_op (K : (v : V) → KrausFamily (X v) (Y v))
    (j : (v : V) → (K v).Index) : (prodFamily K).op j = piKronecker fun v ↦ (K v).op (j v) :=
  rfl

/-- The effect of a product of Kraus families is the product of their effects. -/
theorem effect_prodFamily [∀ v, Fintype (Y v)]
    (K : (v : V) → KrausFamily (X v) (Y v)) :
    (prodFamily K).effect = piKronecker fun v ↦ (K v).effect := by
  ext σ τ
  simp only [KrausFamily.effect, Matrix.sum_apply, piKronecker_apply]
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun j ↦ ?_
  change ((piKronecker fun v ↦ (K v).op (j v))ᴴ * piKronecker fun v ↦ (K v).op (j v)) σ τ = _
  rw [conjTranspose_piKronecker, piKronecker_mul, piKronecker_apply]

/-- The product of Kraus families maps the product operator `⊗_v σ_v` to `⊗_v (K v)(σ_v)`.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (local operations
`U = ⊗ᵢ uᵢ` acting on each site), here for channels. -/
theorem map_prodFamily_piKronecker [∀ v, Fintype (X v)] (K : (v : V) → KrausFamily (X v) (Y v))
    (σ : (v : V) → Matrix (X v) (X v) ℂ) :
    (prodFamily K).map (piKronecker σ) = piKronecker fun v ↦ (K v).map (σ v) := by
  rw [KrausFamily.map_apply]
  refine Eq.trans (Fintype.sum_congr _ _ fun j ↦ ?_)
    (sum_piKronecker fun v i ↦ (K v).op i * σ v * ((K v).op i)ᴴ)
  change (piKronecker fun v ↦ (K v).op (j v)) * piKronecker σ *
    (piKronecker fun v ↦ (K v).op (j v))ᴴ = _
  rw [conjTranspose_piKronecker, piKronecker_mul, piKronecker_mul]

end ManyBody

namespace KrausFamily

open ManyBody

variable {V : Type} [Fintype V] [DecidableEq V] {X Y : V → Type} [∀ v, Fintype (Y v)]
  [∀ v, DecidableEq (X v)]

/-- A product of trace-preserving Kraus families is trace-preserving. -/
theorem IsTP.prodFamily {K : (v : V) → KrausFamily (X v) (Y v)} (hK : ∀ v, (K v).IsTP) :
    (ManyBody.prodFamily K).IsTP := by
  rw [isTP_iff_effect_eq_one, effect_prodFamily,
    show (fun v ↦ (K v).effect) = fun v ↦ 1 from funext hK, piKronecker_one]

end KrausFamily
