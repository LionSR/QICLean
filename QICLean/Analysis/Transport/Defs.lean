/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OperatorMean.LeafStates
import QICLean.Analysis.OperatorMean.BlockDiagonal
import QICLean.Analysis.SinhRatioShift
import QICLean.Analysis.HermitianUnitaryPath

/-!
# Interpolated mean trees and their transport states

This file holds the shared definitions of the finite-dimensional transport estimate
(area-law paper, Proposition 7.4, `prop:transport`, `06-transport.tex` lines 240--434).

Given a history tree `T` with leaves `h : H`, a conditional choice tree `S h` at every
history, old inputs `A h` and new inputs `A' h c`, the interpolated tree at parameter `p`
replaces each leaf `h` of `T` by the vertex `A_h #_p B_h`, where `B_h` is the root of
`S h`. Its terminal leaves are `(h, old)` and `(h, c, new)`, labelled here by
`⟨h, none⟩` and `⟨h, some c⟩` (`06-transport.tex`, display
`transport:terminal-weights`, lines 275--286).

For a nonzero vector `pre`, the filtered vector is `v(p) = M(p)^{-1/4} pre / N(p)`, with
`N(p) = ‖M(p)^{-1/4} pre‖`, and the transport states are
`σ_{j,u} = Φ_j^*(|M^{-iu} v⟩⟨M^{-iu} v|)` (`06-transport.tex`, displays
`transport:filtered-vector` and `transport:states`, lines 388--401).

The proofs in this directory are written from the paper; no Lean source was adapted.

## Main definitions

* `Matrix.MeanTree.bind`, `Matrix.MeanTree.map` — substitution of trees at leaves.
* `Matrix.MeanTree.interpTree` — the interpolated tree of one round.
* `Matrix.Transport.interpRoot` — the root `M(p)`.
* `Matrix.Transport.choiceRoot`, `Matrix.Transport.relRatio` — `B_h`, `C_h`.
* `Matrix.Transport.filteredNormSq`, `Matrix.Transport.filteredVector` — `N(p)²`, `v(p)`.
* `Matrix.Transport.imagPow` — the unitary `M^{-iu}`.
* `Matrix.Transport.transportState` — `σ_{j,u}`.
* `Matrix.Transport.skewSquare` — `|O^*| + |O| - O - O^*` for `O = A^{-1/2} h A^{1/2}`.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval

namespace Matrix

namespace MeanTree

variable {ι κ : Type*}

/-- Substitute the tree `f j` at every leaf `j`. -/
def bind : MeanTree ι → (ι → MeanTree κ) → MeanTree κ
  | leaf j, f => f j
  | node p l r, f => node p (l.bind f) (r.bind f)

/-- Relabel the leaves of a tree. -/
def map (f : ι → κ) (T : MeanTree ι) : MeanTree κ := T.bind fun j => leaf (f j)

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem eval_bind (A : κ → Matrix n n ℂ) (T : MeanTree ι) (f : ι → MeanTree κ) :
    (T.bind f).eval A = T.eval fun j => (f j).eval A := by
  induction T with
  | leaf j => rfl
  | node p l r ihl ihr => simp only [bind, eval, ihl, ihr]

theorem eval_map (A : κ → Matrix n n ℂ) (T : MeanTree ι) (f : ι → κ) :
    (T.map f).eval A = T.eval (A ∘ f) :=
  eval_bind A T _

variable {H : Type*} {C : H → Type*}

/-- The interpolated tree of one round: each leaf `h` of the history tree `T` becomes the
vertex `(h, old) #_p (S h)`, whose second child is the conditional choice tree with leaves
relabelled `(h, c, new)`.

Area-law paper, `06-transport.tex` lines 270--286 and Figure `transport:tree-figure`. -/
def interpTree (T : MeanTree H) (S : ∀ h, MeanTree (C h)) (p : I) :
    MeanTree (Σ h, Option (C h)) :=
  T.bind fun h => node p (leaf ⟨h, none⟩) ((S h).map fun c => ⟨h, some c⟩)

end MeanTree

namespace Transport

open MeanTree

variable {n : Type*} [Fintype n] [DecidableEq n] {H : Type*} {C : H → Type*}

/-- The terminal inputs: `A_h` at `(h, old)` and `A_{h,c}` at `(h, c, new)`. -/
def interpInput (A : H → Matrix n n ℂ) (A' : ∀ h, C h → Matrix n n ℂ) :
    (Σ h, Option (C h)) → Matrix n n ℂ
  | ⟨h, none⟩ => A h
  | ⟨h, some c⟩ => A' h c

/-- The root `M(p)` of the interpolated tree (`06-transport.tex` lines 272--275). -/
noncomputable def interpRoot (T : MeanTree H) (S : ∀ h, MeanTree (C h))
    (A : H → Matrix n n ℂ) (A' : ∀ h, C h → Matrix n n ℂ) (p : I) : Matrix n n ℂ :=
  (interpTree T S p).eval (interpInput A A')

/-- The conditional choice root `B_h` (`06-transport.tex` line 272). -/
noncomputable def choiceRoot (S : ∀ h, MeanTree (C h)) (A' : ∀ h, C h → Matrix n n ℂ)
    (h : H) : Matrix n n ℂ :=
  (S h).eval (A' h)

/-- The relative ratio `C_h = A_h^{-1/2} B_h A_h^{-1/2}` (`06-transport.tex` line 403). -/
noncomputable def relRatio (S : ∀ h, MeanTree (C h)) (A : H → Matrix n n ℂ)
    (A' : ∀ h, C h → Matrix n n ℂ) (h : H) : Matrix n n ℂ :=
  A h ^ (-(1 / 2) : ℝ) * choiceRoot S A' h * A h ^ (-(1 / 2) : ℝ)

/-- The filtered vector before normalization, `M^{-s} pre` with `s = 1/4`. -/
noncomputable def filteredRaw (M : Matrix n n ℂ) (pre : n → ℂ) : n → ℂ :=
  M ^ (-(1 / 4) : ℝ) *ᵥ pre

/-- The squared norm `N² = ‖M^{-1/4} pre‖²` (`06-transport.tex`, display
`transport:filtered-vector`, lines 388--392). -/
noncomputable def filteredNormSq (M : Matrix n n ℂ) (pre : n → ℂ) : ℝ :=
  (star (filteredRaw M pre) ⬝ᵥ filteredRaw M pre).re

/-- The normalized filtered vector `v = M^{-1/4} pre / N` (`06-transport.tex`, display
`transport:filtered-vector`). -/
noncomputable def filteredVector (M : Matrix n n ℂ) (pre : n → ℂ) : n → ℂ :=
  ((Real.sqrt (filteredNormSq M pre))⁻¹ : ℂ) • filteredRaw M pre

/-- The unitary `M^{-iu} = exp(-iu log M)`. -/
noncomputable def imagPow (M : Matrix n n ℂ) (u : ℝ) : Matrix n n ℂ :=
  hermitianUnitaryPath (CFC.log M) (-u)

/-- The transport state `σ_{j,u} = Φ_j^*(|M^{-iu} v⟩⟨M^{-iu} v|)` of a leaf `j` of a tree
`T'` with inputs `A`, for a vector `v` at the root (`06-transport.tex`, display
`transport:states`, lines 395--401). -/
noncomputable def transportState {J : Type*} [DecidableEq J] (T' : MeanTree J)
    (A : J → Matrix n n ℂ) (v : n → ℂ) (j : J) (u : ℝ) : Matrix n n ℂ :=
  let w := imagPow (T'.eval A) u *ᵥ v
  traceAdjointMap (T'.leafMap A j).toLinearMap (vecMulVec w (star w))

/-- The skew square `𝖣 = |O^*| + |O| - O - O^*` of the similarity transform
`O = A^{-1/2} h A^{1/2}` (`06-transport.tex`, display `transport:skew-square`,
lines 646--650). -/
noncomputable def skewSquare (A h : Matrix n n ℂ) : Matrix n n ℂ :=
  let O := A ^ (-(1 / 2) : ℝ) * h * A ^ (1 / 2 : ℝ)
  CFC.sqrt (O * Oᴴ) + CFC.sqrt (Oᴴ * O) - O - Oᴴ

/-- The Fourier density `m_{1/4}` of the derivative formula. -/
noncomputable abbrev fourierWeight (u : ℝ) : ℝ := Real.sinhRatioDensity (1 / 4) u

end Transport

end Matrix
