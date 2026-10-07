# Uniform physical-buffer Gaussian approximation: independent review

Reviewed source: `PhysicalBufferUniform.lean` at
`2edb1bc5190252f43201267e5a16f6088b692ebb`, together with the original-system
constructor in `PhysicalBuffer.lean` and its coordinate, gap, and overlap
dependencies. The mathematical source is the September 24, 2026
Polynomial-PEPS manuscript, `02-information.tex`, lines 395–452, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

This is a source review. Compiler and axiom output are separate evidence;
the presence of a driver alone does not establish that it passed.

## Findings

No mathematical or quantifier-order defect was found in the reviewed scope.

- `exists_uniform_physicalBuffer_filter` first quantifies the positive gap
  and nonnegative real exponent, then chooses `a,T₀`, and only then
  quantifies the finite register types, Hamiltonian, ground state, ground
  energy, and entropy bound. Thus the constants do not depend on dimension
  or original-system data. The proof selects them using the scalar theorem
  before introducing any such data.
- For each original system, `W,z` precede the universal quantifier over `L`.
  They are obtained from the original-buffer constructor before the
  positive variance and cutoff are specified. Applying the same result at
  different `L` therefore reuses the same physical-buffer contraction and
  overlap, rather than selecting unrelated witnesses for each scale.
- The regrouping direction is consistent. `Equiv.doubledRegroup` maps
  `((P × Q) × (P × Q))` to `((P × P) × (Q × Q))`; reindexing the matrix by
  this equivalence uses its inverse on both coordinates. The ground vector
  is the doubled vector composed with that same inverse, so the transported
  matrix-vector equation has the correct direction.
- `physicalLeftSwap` exchanges only the two `R` coordinates. Both `C`
  coordinates and the ordered pair of original `Q` coordinates are fixed.
  Its matrix is `partialSwap R C ⊗ₖ 1`. The filter input is `1 ⊗ₖ W` with
  `W` indexed by exactly `Q × Q`; enlarged purifying factors do not occur
  in this conclusion.
- The doubled energy is `2 * E₀`, and the lower gap remains `Δ`. Writing
  `P = |Ω⟩⟨Ω|`, `Q = I-P`, and `D = H-E₀I-ΔQ`, the doubled defect is
  `D ⊗ I + I ⊗ D + Δ(Q ⊗ Q)`. Normalization makes `Q` positive
  semidefinite, so the three terms are positive semidefinite for `Δ ≥ 0`.
  The eigenvector equation separately supplies the doubled energy. Unitary
  regrouping and partial swap preserve both assertions.
- The original gap residual already forces `H` to be Hermitian: it is
  Hermitian, as are the added real multiples of the identity and rank-one
  projection. The constructor derives the two generators' Hermiticity;
  it does not assume extra paired-system hypotheses.
- The real coefficient is justified by the physical-buffer overlap
  theorem: it is a reduced-state purity and is at least `exp (-2*b)`.
  The constructor identifies the dot product with the complex inner
  product in the correct conjugate-linear slot. The reverse Gaussian
  estimate has the conjugate overlap, which becomes the same coefficient
  because `z` is real. No claim that the truncated filter is Hermitian
  appears in the statement or proof.
- The filter is the actual unrenormalized restricted Gaussian integral.
  The tensor embedding of `W` is contractive; the positive Gaussian
  measure of the time interval is at most one. No normalization by that
  interval mass is introduced. The two scalar errors contribute factors
  `1` and `2`, yielding exactly `3 * exp (-10*b) * L^(-r)`.
- Boundary cases are sound. For `b = 0`, `r = 0`, and `L = 1`, the scale
  `1+b+log L` is still one, so the variance is strictly positive. Real
  powers are used at arbitrary nonnegative real exponents and positive
  bases. Empty physical factors make the normalization hypothesis
  impossible; no existence assertion for normalized vectors on an empty
  coordinate type is made. The underlying constructor allows zero
  variance, where the Gaussian is a point mass and its totalized tail
  bound is coarse but valid; the uniform theorem never uses that case.

The manuscript also discusses interaction range, support, regional
hypotheses, and subsequent locality estimates. These are outside the
reviewed Gaussian statement and are not concluded by it. This review does
not certify the complete reset lemma.

## Consumers and audit drivers

`QICLeanTest/PhysicalBufferUniform.lean` contains:

1. A dimension-uniform consumer at the noninteger exponent `1/2`, using
   one `a,T₀` before all register and original-system data and one `W,z`
   simultaneously at `L = 1` and `L = 4`. Both actual truncated operators
   are contractions, both forward and adjoint errors are retained, and
   positivity of the shared overlap is derived from its lower bound.
2. A concrete complex-phase state on three one-dimensional registers at
   ground energy `-3` and lower gap `2`. Its normalization, original
   eigenvector equation, positive gap residual, and zero mutual
   information are proved. The consumer applies the uniform theorem at
   `b = r = 0`, including exact conversion of the positive variance to a
   nonnegative real, and retains the actual filter estimates for every
   real `L ≥ 1`.
3. An empty-buffer check showing directly that the normalized-state
   hypothesis cannot hold.
4. A guarded standard-axiom report for the uniform declaration.

The raw driver `drivers/PhysicalBufferUniformRawAxioms.lean` prints the
dependencies of the Hermiticity deduction, the derived ground-state pair,
the original-buffer Gaussian constructor, and the uniform result. The
expected dependencies are only `propext`, `Classical.choice`, and
`Quot.sound`; the raw output must be checked independently of the guarded
report.

The existing `PhysicalBufferGaussianFilter.lean` consumers already exercise
nontrivial registers, a complex entangled ground vector, the coordinate
distinction between an `R`-only and whole-`R × C` swap, negative ground
energy, and zero variance. The new file complements those checks rather
than importing or duplicating their private state construction. Its proof
organization follows the existing uniform-ground consumer's extraction of
one set of constants at multiple scales. No external Lean proof text was
copied, and no new axiom, proof hole, or linter-budget change is introduced.
