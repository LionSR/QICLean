/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Entropy
import QICLean.Analysis.TraceCFC

/-!
# Finite-order Rényi entropy

Order zero is the logarithm of the rank; order one is the von Neumann entropy.
At positive orders different from one, the definition uses the spectral trace
of the real power and natural logarithms.

Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2,
`paper_v2.tex`, lines 212–219. The definition is copied without changing its
name, signature, or body from `TNLean/Algebra/FlatDensityRenyiEntropy.lean`,
TNLean commit `9587f793f61deb5c0a9e52633b0745c1bb069e6e` (Apache-2.0).
Only its imports and documentation have changed.
-/

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Finite-order Rényi entropy, with the rank convention at zero and the
von Neumann convention at one. The positive-order formula uses the Hermitian
spectral functional calculus. Source: Schuch–Wolf–Verstraete–Cirac,
arXiv:0705.0292v2, `paper_v2.tex`, lines 212–219. -/
noncomputable def renyiEntropy (ρ : Matrix ι ι ℂ) (hρ : ρ.IsHermitian) (α : ℝ) : ℝ :=
  if α = 0 then Real.log (ρ.rank : ℝ)
  else if α = 1 then vonNeumannEntropy ρ hρ
  else (1 - α)⁻¹ * Real.log ((hρ.cfc (fun x => x ^ α)).trace.re)
