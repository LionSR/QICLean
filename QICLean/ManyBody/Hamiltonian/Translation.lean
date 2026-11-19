/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import QICLean.ManyBody.Hamiltonian.LowEnergyBasis
import QICLean.ManyBody.Sites.SiteAction
import QICLean.ManyBody.Dynamics.GraphBall

/-!
@@DOC
-/

noncomputable section

namespace ManyBody

open GaussianFilter Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [Group G] [MulAction G V]

/-- **Covariance of the filtered terms.** If `H` is invariant under the site action, the
filtered operator of the translate `P_g W P_g†` is the translate of the filtered operator of
`W`. With covariant terms `H_{g•i} = P_g H_i P_g†` this gives the relation
`M_{g•i} = P_g M_i P_g†` that Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1613–1618, uses for translationally invariant systems. -/
theorem gaussianFilteredTerm_sitePermOp_conj {q : ℕ} (r ΔE : ℝ)
    {H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ} (hInv : IsSiteInvariant G H) (hH : H.IsHermitian)
    (g : G) (W : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ) :
    gaussianFilteredTerm r ΔE H
        (sitePermOp (α := Fin q) (MulAction.toPerm g) * W * (sitePermOp (α := Fin q) (MulAction.toPerm g))ᴴ) =
      sitePermOp (α := Fin q) (MulAction.toPerm g) * gaussianFilteredTerm r ΔE H W *
        (sitePermOp (α := Fin q) (MulAction.toPerm g))ᴴ := by
  have hu := sitePermOp_mem_unitary (V := V) (α := Fin q) (MulAction.toPerm g)
  have hconj : sitePermOp (α := Fin q) (MulAction.toPerm g) * H * (sitePermOp (α := Fin q) (MulAction.toPerm g))ᴴ = H := by
    rw [(hInv g).eq, Matrix.mul_assoc]
    simpa [star_eq_conjTranspose] using
      congrArg (H * ·) ((mem_unitaryGroup_iff).mp hu)
  conv_lhs => rw [← hconj]
  exact gaussianFilteredTerm_conj r ΔE hu hH W

end ManyBody

open Matrix GaussianFilter
open scoped InnerProductSpace

section Projection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **Compression of a conjugate by an operator fixing the subspace.** If the adjoint `U†`
leaves every vector of `K` unchanged, then `P (U W U†) P = P W P`, where `P` is the orthogonal
projection onto `K`: indeed `U† P = P`, and so `P U = P` on taking adjoints. -/
theorem Submodule.starProjection_mul_conj_mul_starProjection {K : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] {U : E →L[𝕜] E} (hU : ∀ v ∈ K, U.adjoint v = v)
    (W : E →L[𝕜] E) :
    K.starProjection * (U * W * U.adjoint) * K.starProjection =
      K.starProjection * W * K.starProjection := by
  have hP : U.adjoint * K.starProjection = K.starProjection := by
    ext1 x
    exact hU _ (K.starProjection_apply_mem x)
  have hP' : K.starProjection * U = K.starProjection := by
    have hsa : K.starProjection.adjoint = K.starProjection :=
      (isSelfAdjoint_starProjection K).adjoint_eq
    have h := congrArg star hP
    simpa only [star_mul, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint,
      hsa] using h
  calc K.starProjection * (U * W * U.adjoint) * K.starProjection
      = K.starProjection * U * W * (U.adjoint * K.starProjection) := by simp only [mul_assoc]
    _ = K.starProjection * W * K.starProjection := by rw [hP', hP]

end Projection


namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [Group G] [MulAction G V]

variable {q : ℕ} {H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ} {E₀ : ℝ}

/-- **The low-energy compression is unchanged by a supercell translation.** Let `S` be a
subgroup whose site permutations leave every ground vector of `H` unchanged: the source's
supercell, "such that all of the `n` ground states are unchanged by translation by a
supercell" (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1626–1628). Then for
`g ∈ S` the compression of `P_g W P_g†` to the ground space equals that of `W`. -/
theorem groundCompression_sitePermOp_conj (S : Subgroup G)
    (hS : ∀ g ∈ S, ∀ v ∈ groundSpace H E₀,
      sitePermOp (α := Fin q) (MulAction.toPerm g) *ᵥ WithLp.ofLp v = WithLp.ofLp v)
    {g : G} (hg : g ∈ S) (W : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ) :
    groundCompression H E₀ (sitePermOp (α := Fin q) (MulAction.toPerm g) * W * (sitePermOp (α := Fin q) (MulAction.toPerm g))ᴴ) =
      groundCompression H E₀ W := by
  have hstar : toEuclideanCLM (n := V → Fin q) (𝕜 := ℂ) (sitePermOp (α := Fin q) (MulAction.toPerm g))ᴴ =
      (toEuclideanCLM (n := V → Fin q) (𝕜 := ℂ) (sitePermOp (α := Fin q) (MulAction.toPerm g))).adjoint := by
    rw [← star_eq_conjTranspose, map_star, ContinuousLinearMap.star_eq_adjoint]
  simp only [groundCompression]
  rw [map_mul, map_mul, hstar]
  refine Submodule.starProjection_mul_conj_mul_starProjection (fun v hv ↦ ?_) _
  rw [← hstar, ← sitePermOp_toPerm_inv]
  calc toEuclideanCLM (n := V → Fin q) (𝕜 := ℂ) (sitePermOp (α := Fin q) (MulAction.toPerm g⁻¹)) v
      = WithLp.toLp 2 (sitePermOp (α := Fin q) (MulAction.toPerm g⁻¹) *ᵥ WithLp.ofLp v) := toEuclideanCLM_toLp _ _
    _ = v := by rw [hS g⁻¹ (S.inv_mem hg) v hv]

variable {κ : Type*} [MulAction G κ] {h : κ → Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ}

/-- **Low-energy commutators across a supercell translation.** Let the terms be covariant,
`h_{g•k} = P_g h_k P_g†` (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, line 862, the
terms of a translationally invariant Hamiltonian are translates of one another), let `H` be
invariant and Hermitian, and let `M_k` be the filtered terms. For `g` in a subgroup `S` that
leaves every ground vector unchanged (lines 1626–1628),
`[P M_i P, P M_j P] = [P M_i P, P M_{g•j} P]`. This is the identity used at lines 1634–1637:
the commutator "equal[s] `[M_{x₁,y₁}, M_{x₂+x',y₂}]` where `x'` translates `x₂` by some number
of supercells". -/
theorem groundCompression_commutator_eq_of_mem_supercell (r ΔE : ℝ)
    (hInv : IsSiteInvariant G H) (hH : H.IsHermitian)
    (hcov : ∀ (g : G) k, h (g • k) = sitePermOp (α := Fin q) (MulAction.toPerm g) * h k * (sitePermOp (α := Fin q) (MulAction.toPerm g))ᴴ)
    (S : Subgroup G)
    (hS : ∀ g ∈ S, ∀ v ∈ groundSpace H E₀,
      sitePermOp (α := Fin q) (MulAction.toPerm g) *ᵥ WithLp.ofLp v = WithLp.ofLp v)
    {g : G} (hg : g ∈ S) (i j : κ) :
    groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h i)) *
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h (g • j))) -
      groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h (g • j))) *
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h i)) =
    groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h i)) *
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h j)) -
      groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h j)) *
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h i)) := by
  have hj : groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h (g • j))) =
      groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h j)) := by
    simp only [hcov, gaussianFilteredTerm_sitePermOp_conj r ΔE hInv hH]
    exact groundCompression_sitePermOp_conj S hS hg _
  rw [hj]

/-- **Transfer of a commutator bound across supercell translations.** If `B i j` bounds the
low-energy commutator of the filtered terms at `i` and `j` for all `i` and `j`, then so does
`B i (g • j)` for every `g` in a subgroup `S` that leaves every ground vector unchanged. With
`B` the bound that decays in the distance from `i` to `j`, choosing `g` that moves `j` far from
`i` makes the commutator small in that larger distance: Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1634–1641. -/
theorem norm_groundCompression_commutator_le_of_mem_supercell (r ΔE : ℝ)
    (hInv : IsSiteInvariant G H) (hH : H.IsHermitian)
    (hcov : ∀ (g : G) k, h (g • k) = sitePermOp (α := Fin q) (MulAction.toPerm g) * h k * (sitePermOp (α := Fin q) (MulAction.toPerm g))ᴴ)
    (S : Subgroup G)
    (hS : ∀ g ∈ S, ∀ v ∈ groundSpace H E₀,
      sitePermOp (α := Fin q) (MulAction.toPerm g) *ᵥ WithLp.ofLp v = WithLp.ofLp v)
    (B : κ → κ → ℝ)
    (hB : ∀ i j,
      ‖groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h i)) *
          groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h j)) -
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h j)) *
          groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h i))‖ ≤ B i j)
    {g : G} (hg : g ∈ S) (i j : κ) :
    ‖groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h i)) *
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h j)) -
      groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h j)) *
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H (h i))‖ ≤
      B i (g • j) := by
  have := hB i (g • j)
  rwa [groundCompression_commutator_eq_of_mem_supercell r ΔE hInv hH hcov S hS hg i j] at this

end ManyBody

open Matrix Module.End


namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [CommGroup G] [MulAction G V]
  {q : ℕ}

private theorem toEuclideanLin_apply_eq (A : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ)
    (v : EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)) :
    toEuclideanLin A v = WithLp.toLp 2 (A *ᵥ WithLp.ofLp v) := rfl

theorem toEuclideanLin_sitePermOp_toPerm_mul (g h : G) (v : EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)) :
    toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm (g * h))) v =
      toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm g)) (toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm h)) v) := by
  rw [sitePermOp_toPerm_mul]
  simp [toEuclideanLin_apply_eq, mulVec_mulVec]

theorem toEuclideanLin_sitePermOp_toPerm_one (v : EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)) :
    toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm (1 : G))) v = v := by
  rw [sitePermOp_toPerm_one, toEuclideanLin_apply_eq]
  simp only [one_mulVec, WithLp.toLp_ofLp]

/-- An invariant `H` has its ground space mapped into itself by every site permutation. -/
theorem mapsTo_groundSpace_sitePermOp {H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) (g : G) :
    Set.MapsTo (toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm g)))
      (groundSpace H E₀ : Set (EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)))
      (groundSpace H E₀ : Set (EuclideanSpace ℂ (Config fun _ : V ↦ Fin q))) := fun v hv ↦ by
  rw [SetLike.mem_coe, mem_groundSpace_iff_mulVec] at hv ⊢
  rw [toEuclideanLin_apply_eq, WithLp.ofLp_toLp, mulVec_mulVec, ← (hInv g).eq, ← mulVec_mulVec,
    hv, mulVec_smul]

variable (G q) in
/-- **The momentum sector** of the ground space of `H` at energy `E₀` for a character
`χ : G →* ℂ`: the ground vectors `v` with `P_g v = χ(g) v` for every `g`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1613–1618, ground states that are eigenvectors
of the translations with momentum `k_a`, for which `χ(x) = e^{i k_a · x}`. -/
noncomputable def momentumSector (H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ) (E₀ : ℝ)
    (χ : G →* ℂ) : Submodule ℂ (EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)) :=
  groundSpace H E₀ ⊓ ⨅ g, eigenspace (toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm g))) (χ g)

theorem momentumSector_le_groundSpace (H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ) (E₀ : ℝ)
    (χ : G →* ℂ) : momentumSector G q H E₀ χ ≤ groundSpace H E₀ :=
  inf_le_left

theorem toEuclideanLin_sitePermOp_of_mem_momentumSector
    {H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ} {E₀ : ℝ} {χ : G →* ℂ}
    {v : EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)} (hv : v ∈ momentumSector G q H E₀ χ) (g : G) :
    toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm g)) v = χ g • v :=
  mem_eigenspace_iff.mp (Submodule.mem_iInf _ |>.mp hv.2 g)

/-- A site permutation has finite order on the configurations. -/
theorem exists_pow_sitePermOp_eq_one (g : G) :
    ∃ N : ℕ, 0 < N ∧ sitePermOp (V := V) (α := Fin q) (MulAction.toPerm g) ^ N = 1 := by
  refine ⟨orderOf (MulAction.toPerm g : Equiv.Perm V), orderOf_pos _, ?_⟩
  rw [sitePermOp_pow, pow_orderOf_eq_one, sitePermOp_one]

/-- **The momentum sectors span the ground space.** For an abelian group acting on the sites and
an invariant `H`, every ground vector is a sum of ground vectors with definite momentum.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1613–1618: "we can pick the ground
states to be eigenvectors of the translation operators". -/
theorem iSup_momentumSector {H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) :
    ⨆ χ : G →* ℂ, momentumSector G q H E₀ χ = groundSpace H E₀ := by
  set K := groundSpace H E₀
  let R : G → Module.End ℂ K := fun g ↦
    (toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm g))).restrict
      (mapsTo_groundSpace_sitePermOp hInv E₀ g)
  have hR (g : G) (v : K) : (R g v : EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)) =
      toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm g)) v := rfl
  have hRmul (g h : G) (v : K) : R (g * h) v = R g (R h v) := by
    ext1; simp only [hR, toEuclideanLin_sitePermOp_toPerm_mul]
  have hcomm : Pairwise fun g h ↦ Commute (R g) (R h) := fun g h _ ↦
    LinearMap.ext fun v ↦ by
      change R g (R h v) = R h (R g v)
      rw [← hRmul, ← hRmul, mul_comm]
  have hss (g : G) : Module.End.IsFinitelySemisimple (R g) := by
    obtain ⟨N, hN, hpow⟩ := exists_pow_sitePermOp_eq_one (V := V) (q := q) g
    refine (isSemisimple_of_squarefree_aeval_eq_zero (p := Polynomial.X ^ N - 1) ?_ ?_)
      |>.isFinitelySemisimple
    · exact (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hN.ne') one_ne_zero).squarefree
    · have hRpow (n : ℕ) (v : K) : ((R g ^ n) v : EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)) =
          toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm g) ^ n) v := by
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ', Module.End.mul_apply, hR, ih, pow_succ', toEuclideanLin_apply_eq,
            toEuclideanLin_apply_eq, toEuclideanLin_apply_eq, WithLp.ofLp_toLp, mulVec_mulVec]
      have hRN : R g ^ N = 1 := LinearMap.ext fun v ↦ Subtype.ext <| by
        rw [hRpow, hpow, toEuclideanLin_apply_eq, one_mulVec, WithLp.toLp_ofLp]; rfl
      simp [hRN]
  have htop : ⨆ χ : G → ℂ, ⨅ g, eigenspace (R g) (χ g) = ⊤ := by
    have := iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute R hcomm
      fun g ↦ iSup_maxGenEigenspace_eq_top (R g)
    simpa only [IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace (hss _)] using this
  refine le_antisymm (iSup_le fun χ ↦ momentumSector_le_groundSpace H E₀ χ) ?_
  -- every joint eigenspace of the restrictions lies in a momentum sector
  have hjoint (χ : G → ℂ) :
      (⨅ g, eigenspace (R g) (χ g)).map K.subtype ≤ ⨆ χ : G →* ℂ, momentumSector G q H E₀ χ := by
    by_cases hbot : ⨅ g, eigenspace (R g) (χ g) = ⊥
    · simp [hbot]
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hwg (g : G) : R g w = χ g • w := mem_eigenspace_iff.mp (Submodule.mem_iInf _ |>.mp hw g)
    have hmul (g h : G) : χ (g * h) = χ g * χ h := by
      have := hRmul g h w
      rw [hwg, hwg, map_smul, hwg, smul_smul, mul_comm (χ h)] at this
      exact smul_left_injective ℂ hw0 this
    have hone : χ 1 = 1 := by
      have : R 1 w = w := by ext1; simp [hR, sitePermOp_toPerm_one]
      rw [hwg] at this
      exact smul_left_injective ℂ hw0 (this.trans (one_smul ℂ w).symm)
    let χ' : G →* ℂ := ⟨⟨χ, hone⟩, hmul⟩
    refine le_trans ?_ (le_iSup _ χ')
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.2, Submodule.mem_iInf _ |>.mpr fun g ↦ mem_eigenspace_iff.mpr ?_⟩
    have := mem_eigenspace_iff.mp (Submodule.mem_iInf _ |>.mp hu g)
    simpa [hR, χ'] using congrArg Subtype.val this
  calc K = (⊤ : Submodule ℂ K).map K.subtype := by simp
    _ = (⨆ χ : G → ℂ, ⨅ g, eigenspace (R g) (χ g)).map K.subtype := by rw [htop]
    _ ≤ _ := by rw [Submodule.map_iSup]; exact iSup_le hjoint

variable (G q) in
/-- **The supercell**: the elements of `G` on which every character with a nonzero momentum
sector of the ground space is trivial. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1626–1630, the translations by whole supercells, which leave every ground state unchanged
(`mem_supercell_iff`). -/
noncomputable def supercell (H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ) (E₀ : ℝ) : Subgroup G :=
  ⨅ (χ : G →* ℂ) (_ : momentumSector G q H E₀ χ ≠ ⊥), χ.ker

/-- **The supercell fixes the ground space.** For an abelian group acting on the sites and an
invariant `H`, `g` lies in the supercell exactly when `P_g v = v` for every ground vector `v`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1626–1630: "all of the `n` ground
states are unchanged by translation by a supercell". -/
theorem mem_supercell_iff {H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ}
    (hInv : IsSiteInvariant G H) {E₀ : ℝ} {g : G} :
    g ∈ supercell G q H E₀ ↔
      ∀ v ∈ groundSpace H E₀, toEuclideanLin (sitePermOp (α := Fin q) (MulAction.toPerm g)) v = v := by
  simp only [supercell, Subgroup.mem_iInf, MonoidHom.mem_ker]
  constructor
  · intro hg v hv
    rw [← iSup_momentumSector hInv E₀] at hv
    induction hv using Submodule.iSup_induction' with
    | mem χ v hv =>
      by_cases hbot : momentumSector G q H E₀ χ = ⊥
      · rw [hbot, Submodule.mem_bot] at hv; simp [hv]
      · rw [toEuclideanLin_sitePermOp_of_mem_momentumSector hv, hg χ hbot, one_smul]
    | zero => simp
    | add v w _ _ hv hw => rw [map_add, hv, hw]
  · intro hg χ hbot
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have := (toEuclideanLin_sitePermOp_of_mem_momentumSector hv g).symm.trans
      (hg v (momentumSector_le_groundSpace H E₀ χ hv))
    exact smul_left_injective ℂ hv0 (this.trans (one_smul ℂ v).symm)

/-- The supercell satisfies the hypothesis on the subgroup in
`groundCompression_sitePermOp_conj`, `groundCompression_commutator_eq_of_mem_supercell` and
`norm_groundCompression_commutator_le_of_mem_supercell`. -/
theorem sitePermOp_toPerm_mulVec_eq_of_mem_supercell {H : Matrix (Config fun _ : V ↦ Fin q) (Config fun _ : V ↦ Fin q) ℂ}
    (hInv : IsSiteInvariant G H) {E₀ : ℝ} {g : G} (hg : g ∈ supercell G q H E₀)
    (v : EuclideanSpace ℂ (Config fun _ : V ↦ Fin q)) (hv : v ∈ groundSpace H E₀) :
    sitePermOp (α := Fin q) (MulAction.toPerm g) *ᵥ WithLp.ofLp v = WithLp.ofLp v := by
  simpa [toEuclideanLin_apply_eq] using congrArg WithLp.ofLp ((mem_supercell_iff hInv).mp hg v hv)

end ManyBody

open Matrix
open scoped Matrix.Norms.L2Operator


namespace ManyBody

variable {V G : Type*} [Fintype V] [DecidableEq V] [CommGroup G] [MulAction G V]
  {d : ℕ}

/-- A site translation acts unitarily on the actual ground eigenspace.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
noncomputable def groundTranslation {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) (g : G) :
    groundSpace H E₀ ≃ₗᵢ[ℂ] groundSpace H E₀ := by
  let f : groundSpace H E₀ →ₗᵢ[ℂ] groundSpace H E₀ := {
    toFun := fun x ↦ ⟨toEuclideanLin (sitePermOp (α := Fin d) (MulAction.toPerm g)) x,
      mapsTo_groundSpace_sitePermOp hInv E₀ g x.property⟩
    map_add' := fun x y ↦ Subtype.ext
      (map_add (toEuclideanLin (sitePermOp (α := Fin d) (MulAction.toPerm g)))
        (x : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d)) (y : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d)))
    map_smul' := fun c x ↦ Subtype.ext
      (map_smul (toEuclideanLin (sitePermOp (α := Fin d) (MulAction.toPerm g))) c (x : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d)))
    norm_map' := by
      intro x
      change ‖toEuclideanCLM (n := V → Fin d) (𝕜 := ℂ) (sitePermOp (α := Fin d) (MulAction.toPerm g))
        (x : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d))‖ = ‖(x : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d))‖
      exact ContinuousLinearMap.norm_map_of_mem_unitary
        (Unitary.map_mem (toEuclideanCLM (n := V → Fin d) (𝕜 := ℂ))
          (sitePermOp_mem_unitary (MulAction.toPerm g))) x }
  exact LinearIsometryEquiv.ofSurjective f (LinearMap.surjective_of_injective f.injective)

/-- Conjugation on the ground-space operator algebra preserves the operator norm.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
noncomputable def groundTranslationConjugation {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) (g : G) :
    (groundSpace H E₀ →L[ℂ] groundSpace H E₀) ≃ₗᵢ[ℂ]
      (groundSpace H E₀ →L[ℂ] groundSpace H E₀) := by
  let u := groundTranslation hInv E₀ g
  refine { (u.toContinuousLinearEquiv.arrowCongr u.toContinuousLinearEquiv).toLinearEquiv with
    norm_map' := ?_ }
  intro B
  change ‖(u : groundSpace H E₀ →L[ℂ] groundSpace H E₀).comp
    (B.comp (u.symm : groundSpace H E₀ →L[ℂ] groundSpace H E₀))‖ = ‖B‖
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- The site translation commutes with the canonical orthogonal ground projection.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
theorem sitePerm_starProjection_commute {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) (g : G)
    (x : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d)) :
    toEuclideanLin (sitePermOp (α := Fin d) (MulAction.toPerm g)) ((groundSpace H E₀).starProjection x) =
      (groundSpace H E₀).starProjection (toEuclideanLin (sitePermOp (α := Fin d) (MulAction.toPerm g)) x) := by
  let u : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Config fun _ : V ↦ Fin d) :=
    Unitary.linearIsometryEquiv
      ⟨toEuclideanCLM (n := V → Fin d) (𝕜 := ℂ) (sitePermOp (α := Fin d) (MulAction.toPerm g)),
        Unitary.map_mem _ (sitePermOp_mem_unitary (MulAction.toPerm g))⟩
  have hle : (groundSpace H E₀).map u.toLinearEquiv.toLinearMap ≤
      groundSpace H E₀ := by
    rintro y ⟨z, hz, rfl⟩
    exact mapsTo_groundSpace_sitePermOp hInv E₀ g hz
  have heq : (groundSpace H E₀).map u.toLinearEquiv.toLinearMap =
      groundSpace H E₀ := Submodule.eq_of_le_of_finrank_eq hle
        (u.toLinearEquiv.finrank_map_eq (groundSpace H E₀))
  have h := u.toLinearIsometry.map_starProjection (groundSpace H E₀) x
  change u ((groundSpace H E₀).starProjection x) =
    ((groundSpace H E₀).map u.toLinearEquiv.toLinearMap).starProjection (u x) at h
  have hu (y : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d)) :
      u y = toEuclideanLin (sitePermOp (α := Fin d) (MulAction.toPerm g)) y := rfl
  simpa only [heq, hu] using h

/-- The ground-space unitary is the restriction of the physical site translation.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
@[simp] theorem groundTranslation_apply_coe {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) (g : G) (x : groundSpace H E₀) :
    (groundTranslation hInv E₀ g x : EuclideanSpace ℂ (Config fun _ : V ↦ Fin d)) =
      toEuclideanLin (sitePermOp (α := Fin d) (MulAction.toPerm g)) x := rfl

/-- Inverse ground translation agrees with the inverse physical site translation.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
theorem groundTranslation_symm_apply {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) (g : G) (x : groundSpace H E₀) :
    (groundTranslation hInv E₀ g).symm x = groundTranslation hInv E₀ g⁻¹ x := by
  apply (groundTranslation hInv E₀ g).injective
  apply Subtype.ext
  simp only [LinearIsometryEquiv.apply_symm_apply, groundTranslation_apply_coe]
  rw [← toEuclideanLin_sitePermOp_toPerm_mul, mul_inv_cancel,
    toEuclideanLin_sitePermOp_toPerm_one]

/-- Ground-space conjugation is compression of physical conjugation.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618 and 1644–1654. -/
theorem groundTranslationConjugation_groundSpaceCompression
    {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) (g : G)
    (W : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ) :
    groundTranslationConjugation hInv E₀ g (groundSpaceCompression H E₀ W) =
      groundSpaceCompression H E₀ (sitePermOp (α := Fin d) (MulAction.toPerm g) * W * (sitePermOp (α := Fin d) (MulAction.toPerm g))ᴴ) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change (groundTranslation hInv E₀ g
    (groundSpaceCompression H E₀ W ((groundTranslation hInv E₀ g).symm x)) :
      EuclideanSpace ℂ (Config fun _ : V ↦ Fin d)) = _
  rw [groundTranslation_symm_apply, groundTranslation_apply_coe,
    coe_groundSpaceCompression_apply, coe_groundSpaceCompression_apply]
  simp only [groundCompression, mul_apply_eq_comp]
  rw [sitePerm_starProjection_commute hInv E₀ g,
    ← sitePermOp_toPerm_inv g, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp]
  simp only [Submodule.starProjection_mem_subspace_eq_self, groundTranslation_apply_coe]
  rw [(groundSpace H E₀).starProjection_eq_self_iff.mpr
    (mapsTo_groundSpace_sitePermOp hInv E₀ g⁻¹ x.property)]
  rfl

/-- Iterating ground-space conjugation follows the orbit of any covariant local family.
Hastings, arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem groundTranslationConjugation_pow_compression_of_covariant
    {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ}
    (hInv : IsSiteInvariant G H) (E₀ : ℝ) {κ : Type*} [MulAction G κ]
    (M : κ → Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ)
    (hcov : ∀ (g : G) i, M (g • i) = sitePermOp (α := Fin d) (MulAction.toPerm g) * M i * (sitePermOp (α := Fin d) (MulAction.toPerm g))ᴴ)
    (g : G) (k : ℕ) (i : κ) :
    ((groundTranslationConjugation hInv E₀ g).toLinearMap ^ k)
        (groundSpaceCompression H E₀ (M i)) =
      groundSpaceCompression H E₀ (M (g ^ k • i)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change groundTranslationConjugation hInv E₀ g
      (groundSpaceCompression H E₀ (M (g ^ k • i))) = _
    rw [groundTranslationConjugation_groundSpaceCompression, ← hcov, pow_succ', mul_smul]


/-- Iterated conjugation of an arbitrary observable agrees before and after compression.
No covariance assumption on a local decomposition is needed. Hastings,
arXiv:cond-mat/0508554v3, lines 1644–1654. -/
theorem groundTranslationConjugation_pow_compression
    {V Γ : Type*} [Fintype V] [DecidableEq V] [CommGroup Γ] [MulAction Γ V]
    {d : ℕ} {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ}
    (hInv : IsSiteInvariant Γ H) (E₀ : ℝ) (g : Γ) (k : ℕ)
    (W : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ) :
    ((groundTranslationConjugation hInv E₀ g).toLinearMap ^ k)
        (groundSpaceCompression H E₀ W) =
      groundSpaceCompression H E₀
        (sitePermOp (α := Fin d) (MulAction.toPerm (g ^ k)) * W * (sitePermOp (α := Fin d) (MulAction.toPerm (g ^ k)))ᴴ) := by
  let M : Γ → Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ :=
    fun h ↦ sitePermOp (α := Fin d) (MulAction.toPerm h) * W * (sitePermOp (α := Fin d) (MulAction.toPerm h))ᴴ
  have hcov (a b : Γ) : M (a • b) = sitePermOp (α := Fin d) (MulAction.toPerm a) * M b * (sitePermOp (α := Fin d) (MulAction.toPerm a))ᴴ := by
    dsimp [M]
    rw [sitePermOp_toPerm_mul, Matrix.conjTranspose_mul]
    noncomm_ring
  have h := groundTranslationConjugation_pow_compression_of_covariant hInv E₀ M hcov g k 1
  simpa only [M, sitePermOp_toPerm_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    smul_eq_mul, mul_one] using h


end ManyBody

open Matrix

namespace SimpleGraph

variable {V : Type*} {Γ : SimpleGraph V} {n R : ℕ}

/-- One step of the triangle inequality: crossing an edge changes the circular displacement
from a fixed site by at most \(R\). -/
private theorem natAbs_valMinAbs_sub_le_add_of_adj (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R)
    (u w x : V) (h : Γ.Adj u w) :
    (π w - π x).valMinAbs.natAbs ≤ (π u - π x).valMinAbs.natAbs + R := by
  simpa only [add_comm (π u - π x) (π w - π u), sub_add_sub_cancel] using
    (ZMod.natAbs_valMinAbs_add_le (π u - π x) (π w - π u)).trans
      ((Int.natAbs_add_le _ _).trans (Nat.add_le_add_left (hπ u w h) _))

/-- Accumulating the one-edge step along a walk: the circular displacement grows by at most
\(R\) times the length of the walk. -/
private theorem natAbs_valMinAbs_sub_le_add_length_mul (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R)
    (x : V) {u y : V} (p : Γ.Walk u y) :
    (π y - π x).valMinAbs.natAbs ≤
      (π u - π x).valMinAbs.natAbs + R * p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    have hstep := natAbs_valMinAbs_sub_le_add_of_adj π hπ _ _ x h
    rw [SimpleGraph.Walk.length_cons, Nat.mul_succ]
    omega

/-- If each edge changes a cell coordinate by at most the positive integer \(R\), its
circular displacement is at most \(R\) times the graph distance. -/
theorem natAbs_valMinAbs_sub_le_edist (hR : 0 < R) (π : V → ZMod n)
    (hπ : ∀ u v, Γ.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R) (x y : V) :
    ((π y - π x).valMinAbs.natAbs : ℕ∞) ≤ (R : ℕ∞) * Γ.edist x y := by
  rcases eq_or_ne (Γ.edist x y) ⊤ with h | h
  · simp [h, hR.ne']
  · obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
    rw [← hp]
    have hw := natAbs_valMinAbs_sub_le_add_length_mul π hπ x p
    simp only [sub_self, ZMod.valMinAbs_zero, Int.natAbs_zero, zero_add] at hw
    exact_mod_cast hw

end SimpleGraph

namespace ManyBody

/-- Translation by the `k`-th power advances a cell coordinate by `k`.
Hastings, arXiv:cond-mat/0508554v3, lines 1603–1618. -/
theorem coordinate_pow_smul {V Γ : Type*} [Group Γ] [MulAction Γ V]
    {n : ℕ} (π : V → ZMod n) (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (k : ℕ) (v : V) : π (e ^ k • v) = π v + (k : ZMod n) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, he, ih, Nat.cast_succ]; abel

/-- **Multiples of `q` reach far.** For `q ≥ 1` and residues `a`, `b` modulo `n`, some
`b + qt` lies at circular distance more than `n / 2 - q` from `a`. -/
theorem exists_lt_natAbs_valMinAbs_add {n : ℕ} [NeZero n] {q : ℕ} (hq : 0 < q)
    (a b : ZMod n) :
    ∃ t : ℕ, n / 2 < (b + ((q * t : ℕ) : ZMod n) - a).valMinAbs.natAbs + q := by
  have hn := NeZero.pos n
  set c := (b - a).val with hc
  have hcL : c < n := ZMod.val_lt (b - a)
  set h := n / 2 with hh
  have hhn : h ≤ n - h := by omega
  have hval (t : ℕ) : (b + ((q * t : ℕ) : ZMod n) - a).val = (q * t + c) % n := by
    rw [← ZMod.val_natCast, Nat.cast_add, hc, ZMod.natCast_zmod_val]
    congr 1
    abel
  simp only [ZMod.valMinAbs_natAbs_eq_min]
  by_cases hsmall : h < q
  · exact ⟨0, by omega⟩
  replace hsmall := not_lt.mp hsmall
  by_cases hch : c ≤ h
  · refine ⟨(h - c) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (h - c) q
    have h2 := Nat.lt_div_mul_add (a := h - c) hq
    rw [mul_comm] at h1 h2
    rw [hval, Nat.mod_eq_of_lt (show q * ((h - c) / q) + c < n by omega)]
    omega
  · refine ⟨(n + h - c) / q, ?_⟩
    have h1 := Nat.div_mul_le_self (n + h - c) q
    have h2 := Nat.lt_div_mul_add (a := n + h - c) hq
    rw [mul_comm] at h1 h2
    set s := q * ((n + h - c) / q) + c
    have hs : s % n = s - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hval, hs]
    omega

/-- The coordinate of a site of the ring, as a residue: subtraction of sites is subtraction of
residues. -/
private theorem natCast_val_sub {n : ℕ} [NeZero n] (u v : Fin n) :
    (((v - u : Fin n) : ℕ) : ZMod n) = ((v : ℕ) : ZMod n) - ((u : ℕ) : ZMod n) := by
  rw [Fin.val_sub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub u.isLt.le, ZMod.natCast_self]
  ring

/-- Every edge of the ring joins residues at circular distance one. -/
private theorem natAbs_valMinAbs_sub_le_one_of_adj_cycleGraph {n : ℕ} [NeZero n] (u v : Fin n)
    (h : (SimpleGraph.cycleGraph n).Adj u v) :
    (((v : ℕ) : ZMod n) - ((u : ℕ) : ZMod n)).valMinAbs.natAbs ≤ 1 := by
  have hone : ((1 : ZMod n)).valMinAbs.natAbs ≤ 1 := by
    rw [ZMod.valMinAbs_natAbs_eq_min]
    exact (min_le_left _ _).trans (by rw [ZMod.val_one_eq_one_mod]; exact Nat.mod_le 1 n)
  rcases SimpleGraph.cycleGraph_adj'.mp h with h | h
  · rw [← neg_sub, ZMod.natAbs_valMinAbs_neg, ← natCast_val_sub, h, Nat.cast_one]; exact hone
  · rw [← natCast_val_sub, h, Nat.cast_one]; exact hone

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [CommGroup G] [MulAction G V]
  {d : ℕ}

/-- **Momenta of denominator `q`.** If every character with a nonzero momentum sector satisfies
`χ(g)^q = 1`, then every `q`-th power lies in the supercell. For the translations of a lattice
these are the momenta `2πp/q` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1620–1625, and `g^q` is a translation by whole supercells (lines 1626–1630). -/
theorem pow_mem_supercell {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ} {E₀ : ℝ} {q : ℕ}
    (hden : ∀ χ : G →* ℂ, momentumSector G d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1) (g : G) :
    g ^ q ∈ supercell G d H E₀ := by
  simp only [supercell, Subgroup.mem_iInf, MonoidHom.mem_ker, map_pow]
  exact fun χ hχ ↦ hden χ hχ g

/-- **A supercell translation carries a site far away.** Let an abelian group act on the
sites, and suppose \(\chi(g)^q=1\) for every group element and every character with a nonzero
momentum sector, where \(q\ge1\). Let \(\pi\) be a cell coordinate with \(n\) cells, let
\(R\ge1\) bound its circular displacement along every edge, and let \(e\) translate it by
one. Then some supercell translation satisfies
\(\lfloor n/2\rfloor<R\,d(x,g\cdot y)+q\).

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1620–1641, chooses a supercell
translation carrying a site to a distance of order the linear size of the system. -/
theorem exists_mem_supercell_lt_edist_add {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (G : SimpleGraph V) {n R : ℕ} [NeZero n] (hR : 0 < R) (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ R)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1) (x y : V) :
    ∃ g ∈ supercell Γ d H E₀, ((n / 2 : ℕ) : ℕ∞) < (R : ℕ∞) * G.edist x (g • y) + q := by
  obtain ⟨t, ht⟩ := exists_lt_natAbs_valMinAbs_add hq (π x) (π y)
  refine ⟨(e ^ t) ^ q, pow_mem_supercell hden _, ?_⟩
  rw [← pow_mul, Nat.mul_comm t q]
  have hdist := SimpleGraph.natAbs_valMinAbs_sub_le_edist hR π hπ x (e ^ (q * t) • y)
  rw [coordinate_pow_smul π e he] at hdist
  have h1 : ((n / 2 : ℕ) : ℕ∞) <
      ((π y + ((q * t : ℕ) : ZMod n) - π x).valMinAbs.natAbs : ℕ∞) + q := by
    exact_mod_cast ht
  exact h1.trans_le (add_le_add_left hdist _)

/-- If each edge changes the cell coordinate by at most one and
`l + q ≤ n / 2`, a supercell translation carries any site to graph distance
strictly greater than `l` from any other. This combines the geometric choice
with its distance consequence in Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1634–1641. -/
theorem exists_mem_supercell_lt_edist {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    {H : Matrix (Config fun _ : V ↦ Fin d) (Config fun _ : V ↦ Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (G : SimpleGraph V) {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (l : ℕ) (hl : l + q ≤ n / 2) (x y : V) :
    ∃ g ∈ supercell Γ d H E₀, (l : ℕ∞) < G.edist x (g • y) := by
  obtain ⟨g, hg, hdist⟩ : ∃ g ∈ supercell Γ d H E₀,
      ((n / 2 : ℕ) : ℕ∞) < G.edist x (g • y) + q := by
    simpa only [Nat.cast_one, one_mul] using
      exists_mem_supercell_lt_edist_add hq hden G (R := 1) Nat.zero_lt_one π hπ e he x y
  refine ⟨g, hg, ?_⟩
  by_contra hfar
  have hle := le_of_not_gt hfar
  have hlt : ((n / 2 : ℕ) : ℕ∞) < ((l + q : ℕ) : ℕ∞) := by
    calc
      ((n / 2 : ℕ) : ℕ∞) < G.edist x (g • y) + q := hdist
      _ ≤ (l : ℕ∞) + q := add_le_add hle le_rfl
      _ = ((l + q : ℕ) : ℕ∞) := by rw [Nat.cast_add]
  exact (not_lt_of_ge hl) (ENat.natCast_lt_natCast.mp hlt)

/-- **A supercell rotation of a ring carries a site far away.** The case of
`exists_mem_supercell_lt_edist_add` for the rotations of a ring of `n` sites, with the
coordinate of a site as a residue modulo `n`. -/
theorem exists_mem_supercell_lt_edist_add_ring {n : ℕ} [NeZero n]
    {H : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ} {E₀ : ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ χ : Multiplicative (Fin n) →* ℂ,
      momentumSector (Multiplicative (Fin n)) d H E₀ χ ≠ ⊥ → ∀ g, χ g ^ q = 1)
    (x y : Fin n) :
    ∃ g ∈ supercell (Multiplicative (Fin n)) d H E₀,
      ((n / 2 : ℕ) : ℕ∞) < (SimpleGraph.cycleGraph n).edist x (g • y) + q := by
  simpa only [Nat.cast_one, one_mul] using
    exists_mem_supercell_lt_edist_add hq hden (SimpleGraph.cycleGraph n) (R := 1)
      Nat.zero_lt_one
      (fun x : Fin n ↦ ((x : ℕ) : ZMod n)) natAbs_valMinAbs_sub_le_one_of_adj_cycleGraph
      (Multiplicative.ofAdd 1) (fun v ↦ by
        change (((1 + v : Fin n) : ℕ) : ZMod n) = _
        rw [Fin.val_add, ZMod.natCast_mod, Nat.cast_add, Fin.val_one', ZMod.natCast_mod,
          Nat.cast_one, add_comm]) x y

end ManyBody

open Matrix GaussianFilter 
open scoped Matrix.Norms.L2Operator


namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ} {κ : Type*} [Fintype κ]
  (G : SimpleGraph V) {T : κ → Finset V}
  (Φ : Interaction (fun _ : V ↦ Fin d) T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)

include hHerm hDiam hCard hBudget

/-- **The low-energy commutator is small when a supercell translate is far away.** Let the
terms be covariant under the action of `Γ`, `h_{g•k} = P_g h_k P_g†` (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, line 862), let every eigenvalue of `H = ∑_k h_k`
equal `E₀` or be at least `E₀ + ΔE`, and let `S ≤ Γ` leave every ground vector unchanged
(lines 1626–1628). If `g ∈ S` and the support of `h_{g•j}` is disjoint from the sites within
graph distance `l` of the support of `h_i`, then the low-energy commutator of the filtered terms
`M_k` at `i` and `j` obeys the bound of eq. `blecm` at separation `l`, for all `q ≥ 0` and
`τ ≥ 0`. This is the step of lines 1634–1641. -/
theorem norm_groundCompression_commutator_le_of_supercell_separation
    {Γ : Type*} [Group Γ] [MulAction Γ V] [MulAction Γ κ]
    (hcov : ∀ (g : Γ) k, Φ.term (g • k) = sitePermOp (α := Fin d) (MulAction.toPerm g) * Φ.term k * (sitePermOp (α := Fin d) (MulAction.toPerm g))ᴴ)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {r q ΔE : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hΔE : 0 < ΔE)
    {E₀ : ℝ} (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    (S : Subgroup Γ)
    (hS : ∀ g ∈ S, ∀ v ∈ groundSpace Φ.hamiltonian E₀,
      sitePermOp (α := Fin d) (MulAction.toPerm g) *ᵥ WithLp.ofLp v = WithLp.ofLp v)
    {g : Γ} (hg : g ∈ S) (i j : κ) (l : ℕ)
    (hsep : Disjoint ((T i).biUnion fun x => graphBall G x l) (T (g • j)))
    {τ : ℝ} (hT : 0 ≤ τ) :
    ‖groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term j)) -
        groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term j)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i))‖ ≤
      2 * ‖Φ.term (g • j)‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * ((T i).card : ℝ) ^ 2 * ‖Φ.term i‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
            2 * ‖Φ.term i‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q))) +
        2 * ‖Φ.term i‖ * ‖Φ.term (g • j)‖ * Real.exp (-q / 2) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hj : groundCompression Φ.hamiltonian E₀ (Φ.term (g • j)) =
      groundCompression Φ.hamiltonian E₀ (Φ.term j) := by
    rw [hcov]
    exact groundCompression_sitePermOp_conj S hS hg _
  rw [groundCompression_gaussianFilteredTerm hr hH, groundCompression_gaussianFilteredTerm hr hH,
    ← hj]
  exact norm_groundCompression_commutator_le_graphNeighborhood G Φ hHerm R hDiam
    vR hCard b₀ hBudget Kg kg hGrowth hq hΔE hgap (T i) (Φ.mem i) l _ hsep
    (Φ.mem (g • j)) hT

end ManyBody
