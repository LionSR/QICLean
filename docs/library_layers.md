# Library layers below ManyBody and Circuit

Status: adopted 2026-11-21 (QICLean #1172, with #1173 for the spectral layer
and #1174 for the many-body modules of `Analysis` and `Entropy`). This document
orders the directories of QICLean that sit below the many-body and circuit
layers of `docs/import_structure.md`, and records where every module of
`Algebra`, `Analysis`, `Spectral`, `Topology`, `Probability`, `QPF`, `Entropy`
and `Representation`, and of the top level of `Channel` and `Kraus`, went. The
principles are those of the TNLean document *Many-body layer and circuit
library* (sections "Principles", "Where a declaration goes", "Directories and
namespaces", "Enforcement").

## Principles

1. A layer is defined by the objects its statements mention, not by the paper
   or proof a module was written for. A declaration lives in the lowest layer
   whose objects suffice to state it.
2. Imports point downward. Two layers at the same height do not import each
   other; what both need moves down.
3. A directory is a layer or part of one, and its name states objects, never
   a proof technique or a source. A directory holds at most about forty
   modules at its top level and is divided by object beyond that. A module of
   one lemma is merged into the module that defines the object it is about.
4. The rules are checked by `scripts/check_import_layers.py`; recorded
   violations may only shrink.

## Layers

```mermaid
flowchart BT
  AL["Algebra<br/>matrices over a ring, Kronecker products, polynomials, words, star subalgebras, partial trace"]
  AN["Analysis<br/>norms, order, functional calculus, exponentials, convexity, real analysis"]
  SP["Spectral<br/>eigenvalues, gaps, spectral projections and filters of one matrix"]
  CH["Channel<br/>linear maps on matrix algebras: positive, completely positive, Choi, dilations"]
  KR["Kraus<br/>finite families of matrices: words, transfer maps, Wielandt"]
  EN["Entropy<br/>entropies and information of one, two or three systems"]
  PR["Probability<br/>measures, random matrices and subspaces, concentration"]
  RE["Representation<br/>group actions on tensor powers, Schur–Weyl, characters"]
  S["ManyBody/Sites, Dynamics, Hamiltonian<br/>docs/import_structure.md"]
  ME["ManyBody/Entropy<br/>entropy of regions, filters on regions, regional typical states"]
  MS["ManyBody/Subspace<br/>viable subspaces of a many-body system and their sampling"]
  MR["ManyBody/Replica<br/>copies of a many-body system: metrics, labels, Bell insertions"]
  C["Circuit<br/>docs/import_structure.md"]
  AL --> AN --> SP --> CH --> KR --> EN --> PR --> RE
  EN --> S
  S --> ME
  ME --> MS
  ME --> MR
  PR --> MS
  RE --> MR
  CH --> C
  S --> C
```

The eight single-system layers form a chain: each may import every layer
before it. `ManyBody/Sites` and the layers above it may import the
single-system layers up to `Entropy` (matrices, channels and entropy of one or
two systems, as in the TNLean architecture); `ManyBody/Subspace` adds
`Probability`, `ManyBody/Replica` adds `Probability` and `Representation`.
Subspaces and replicas are siblings. The circuit layers are unchanged: they may
import the matrix layers (`Algebra`, `Analysis`, `Spectral`), the channel
layers (`Channel`, `Kraus`) and `ManyBody/Sites`.

| Layer | Objects its statements mention | May import |
|---|---|---|
| `Algebra` | matrices over a ring or `ℂ`, entries, reindexing, rank, ranges, Kronecker products, permutations, polynomials and power sums, words and counts, star subalgebras of matrix algebras, the partial trace; no norms, limits or real functions | — |
| `Analysis` | norms, the Loewner order, functional calculus, exponentials and logarithms, convexity, majorization, scalar real analysis, optimization | Algebra |
| `Spectral` | eigenvalues and eigenvectors of one matrix, gaps above a kernel or a ground energy, spectral projections, spectral filters and truncations, low-energy subspaces, Jordan forms, spectral radius | Algebra, Analysis |
| `Channel` | linear maps between matrix algebras: positive and completely positive maps, their Kraus representations, Choi matrices, dilations, conditional expectations, operator systems, measurements, Schmidt decomposition and entanglement of bipartite vectors | the matrix layers |
| `Kraus` | a finite family of matrices `A : ι → Matrix`: its words and word spans, transfer map, blocking, injectivity and primitivity, mixed transfer maps of two families | the matrix layers, Channel |
| `Entropy` | von Neumann, relative, Rényi and Shannon entropy, mutual and conditional information, strong subadditivity and its equality case, typical subspaces | the layers above |
| `Probability` | measures, random variables, Haar and Gaussian random matrices and subspaces, Poisson words, concentration, measurability | the layers above |
| `Representation` | permutation and unitary group actions, Schur–Weyl duality, characters, Young diagrams, coherent states, copies of a system | the layers above |
| `ManyBody/Entropy` | entropy and information of regions, filters supported on regions, typical states of regions, cuts of the regional tensor product | single systems up to Entropy, Sites, Dynamics, Hamiltonian |
| `ManyBody/Subspace` | viable subspaces of a many-body system, their trimming and sampling | as ManyBody/Entropy, with Probability and ManyBody/Entropy |
| `ManyBody/Replica` | copies of a many-body system: replica metrics, labels of subsystems, Bell insertions, band metrics | as ManyBody/Entropy, with Probability, Representation and ManyBody/Entropy |

### Kraus and Channel

Both directories hold Kraus operators; the rule is the object of the statement.
A statement about a linear map `Φ : Matrix → Matrix` (positivity, complete
positivity, trace preservation, a Kraus representation of `Φ`, the freedom and
rank of that representation) belongs to `Channel`, in `Channel/KrausMap` when
the map is given by its Kraus family. A statement about the family itself, as a
tuple of matrices, belongs to `Kraus`: its words `A_{i₁} ⋯ A_{iₙ}`, the spans
of words, the transfer map as a function of the family, blocking, injectivity,
primitivity and Wielandt bounds, and the mixed transfer map of two families.
`Kraus` is the higher layer: it may import `Channel` (the transfer map of a
family is a channel), and `Channel` never imports `Kraus`. Of the seven modules
of `Channel` that imported `Kraus`, six are about words of a family and moved to
`Kraus/Wielandt`, with `WielandtLowDim`, which imports them; the seventh,
`Irreducible/KrausGauge`, imported `Kraus/InvariantProjection`, whose
statements are about invariant projections of a map and which moved down to
`Channel/Irreducible`.

### Spectral, QPF and Topology

The three modules of the former `Spectral` directory are mixed transfer maps of
two Kraus families and moved to `Kraus/MixedMap`; `Spectral` is now the layer
of one matrix's spectrum, made of 121 modules from `Analysis` and `Algebra`.
`QPF` (quantum Perron–Frobenius for primitive Kraus families) moved to
`Kraus/PrimitiveFixedPoint`, and `Topology` (fixed-point theorems, compactness
of matrix sets) to `Analysis/FixedPoint` and `Analysis/Topology`. Neither
remains a directory.

A follow-up placed three modules of `Analysis` at their content and merged two one-lemma modules
of `Spectral/Gap`. `Analysis/Order/GlobalGap` (a gap `H - E₀ ≥ Δ (1 - |Ω⟩⟨Ω|)` above a ground
energy) moved to `Spectral/Eigenvalue/GlobalGap`, the lowest part of the layer, since
`Spectral/Perturbation` imports it. `Analysis/Norm/ContractionWordDecay` and
`ContractionWordDecaySpectator`, which bound words of contractions by such a gap and were the
reason `GlobalGap` stayed in `Analysis`, moved to `Spectral/Gap`. `Spectral/Gap/KernelSpectralGap`
was merged into `Spectral/Gap/EigenvalueGap`, which states the gap above a kernel in eigenvalue,
quadratic and norm form, and `Spectral/Gap/GroundProjection` into
`Spectral/Filter/Gaussian/SpectralGap`, which proves the ground-or-excited dichotomy it uses; this
removed one import against the order inside `Spectral`. `Analysis/Resolvent/PhaseGap` stays: its
phase gap is the vector `A^z a₀ - V B^z b₀` of a resolvent compression, not a spectral gap. The
module map records the moves.

## Directories

Counts are modules with declarations; aggregators are generated.

| Directory | Modules | Holds |
|---|---|---|
| `Algebra` | 115 | `PartialTrace` (partial traces of matrices on product index types) at the top level |
| `Algebra/Combinatorics` | 12 | finite sums, counts, `Fin` and `ZMod` index bookkeeping, finite graphs |
| `Algebra/Hermitian` | 10 | Hermitian, positive semidefinite and projection matrices without norms |
| `Algebra/Kronecker` | 5 | Kronecker products, tensor maps, overlapping lifts on three factors |
| `Algebra/Matrix` | 17 | entries, reindexing, rank, ranges, traces, Minkowski-selfadjoint matrices |
| `Algebra/MatrixAlgebra` | 9 | homomorphisms of full matrix algebras: Skolem–Noether, Burnside, centralizers |
| `Algebra/Nilpotent` | 4 | nilpotent subspaces and nilpotent matrices |
| `Algebra/OperatorSchmidt` | 15 | the operator Schmidt decomposition and its rank |
| `Algebra/PerronFrobenius` | 6 | nonnegative matrices |
| `Algebra/Polynomial` | 10 | matrix polynomials, interpolation, power sums, Newton–Girard |
| `Algebra/SpinCover` | 1 | the spin cover of the Lorentz group (Euler angles are in `Analysis/Real`) |
| `Algebra/StarSubalgebra` | 12 | star subalgebras of matrix algebras, block forms, isotypic decompositions |
| `Algebra/Unitary` | 5 | unitary matrices between index types, Gram unitaries, permutation matrices |
| `Algebra/Word` | 8 | ordered words, letter counts and word coefficients |
| `Analysis/Calculus` | 11 | derivatives and integrals of scalar and matrix functions, Fourier transforms |
| `Analysis/ClusterExpansion` | 6 | the cluster expansion of the exponential of a sum of matrices |
| `Analysis/Complex` | 4 | holomorphic functions on strips, interpolation |
| `Analysis/Convexity` | 9 | operator convexity and concavity, Lieb's integrals, Jensen's inequality |
| `Analysis/CyclicInequality` | 8 | cyclic functionals of positive vectors (Nowosad, Yamagami) |
| `Analysis/Exponential` | 12 | matrix exponentials, unitary evolutions, commutator series |
| `Analysis/FilterFunction` | 5 | scalar profiles and kernels of spectral filters |
| `Analysis/FixedPoint` | 4 | Brouwer-type fixed-point theorems, retracts of density matrices |
| `Analysis/FunctionalCalculus` | 25 | the continuous functional calculus of matrices |
| `Analysis/Isometry` | 12 | isometries, compressions by isometries, polar corrections |
| `Analysis/Logarithm` | 5 | matrix logarithms |
| `Analysis/Majorization` | 7 | majorization of vectors and spectra, doubly stochastic matrices |
| `Analysis/Metric` | 3 | ball kernels and distance profiles in metric spaces |
| `Analysis/Norm` | 23 | operator, Frobenius and Schatten norms, contractions |
| `Analysis/OperatorMean` | 12 | operator means and mean trees |
| `Analysis/Optimization` | 7 | semidefinite and conic programs, duality |
| `Analysis/Order` | 16 | the Loewner order, density matrices, positive cones |
| `Analysis/Parameter` | 32 | real parameter choices and budgets with no matrices |
| `Analysis/Projection` | 26 | projections, two-projection geometry, closeness of subspaces |
| `Analysis/Real` | 35 | scalar real analysis: special functions, series, decay, inequalities |
| `Analysis/Resolvent` | 6 | resolvents and their integrals |
| `Analysis/Subspace` | 7 | closeness and viability of subspaces of a tensor product |
| `Analysis/Support` | 9 | support projections, inverses on the support |
| `Analysis/TensorProduct` | 5 | tensor products of subspaces and coordinates of matrices on them |
| `Analysis/Topology` | 4 | closedness and continuity of matrix sets and maps |
| `Analysis/TraceInequality` | 15 | trace inequalities (Hölder, Klein, fidelity) |
| `Analysis/TraceNorm` | 15 | the trace norm and trace distance |
| `Spectral/Eigenvalue` | 28 | eigenvalues, eigenvectors, extremal eigenvalues, singular values |
| `Spectral/Filter` | 29 | spectral filters and truncations of one matrix; `Filter/Gaussian` |
| `Spectral/Gap` | 18 | gaps above a kernel in eigenvalue, quadratic and norm form, and their transfer and perturbation |
| `Spectral/Jordan` | 9 | Jordan blocks and Fitting decompositions |
| `Spectral/LowEnergy` | 21 | low-energy subspaces of one matrix; `LowEnergy/Basis` |
| `Spectral/Perturbation` | 9 | perturbation of eigenvalues and spectral clusters |
| `Spectral/Projection` | 5 | spectral projections and cutoffs |
| `Spectral/Radius` | 4 | spectral radius and power decay |
| `Channel` | 399 | 17 top-level modules: the definitions of positive, completely positive and trace-preserving maps and their general properties |
| `Channel/Choi` | 10 | Choi and Jamiołkowski matrices, Doeblin minorization |
| `Channel/ConditionalExpectation` | 5 | conditional expectations onto subalgebras |
| `Channel/Convexity` | 4 | Lieb concavity and convexity proved with positive maps |
| `Channel/Dilation` | 13 | Stinespring and environment dilations, open systems |
| `Channel/Entanglement` | 10 | entanglement witnesses, the maximally entangled vector, PPT |
| `Channel/FixedPoint/MeanErgodic` | 4 | Cesàro means, the mean-ergodic projection and its adjoint, the limiting Gram metric |
| `Channel/FixedPoint/Stationary` | 10 | stationary states, their spans and supports, maximal-rank fixed points |
| `Channel/FixedPoint/Algebra` | 7 | the fixed-point algebra of a Schwarz map, its block form and conditional expectation |
| `Channel/FixedPoint/DensityBlock` | 4 | the density-block form of the fixed points (Wolf Theorem 6.14) |
| `Channel/FixedPoint/DirectSum` | 8 | maps on finite direct sums of matrix algebras and their fixed points |
| `Channel/FixedPoint/Weighted` | 10 | fixed points in corners and with weights, canonical gauges, maximal supports of Kraus maps |
| `Channel/Gluing` | 5 | gluing states across a tripartite cut |
| `Channel/KrausMap` | 20 | maps given by Kraus families: CPTP, rank, freedom, gauges |
| `Channel/Measurement` | 4 | effects and instruments |
| `Channel/OperatorMean` | 20 | derivatives of operator means, which are n-positive maps, and transport along mean trees |
| `Channel/OperatorSystem` | 4 | operator systems and their extensions |
| `Channel/PartialTrace` | 13 | marginals: supports, ranks and contractions under the partial trace |
| `Channel/Peripheral/Spectrum` | 12 | the peripheral spectrum: eigenvalues of modulus one, spectral radius, powers, conjugations, primitivity |
| `Channel/Peripheral/Projection` | 4 | Jordan blocks, the peripheral spectral projection, Cesàro recurrence |
| `Channel/Peripheral/Asymptotic` | 6 | the asymptotic image and the convergence of states |
| `Channel/Peripheral/Irreducible` | 13 | irreducible Schwarz maps: their peripheral group, cyclic projections and cyclic decomposition |
| `Channel/Peripheral/Cycles` | 10 | permutations of density blocks and the structure of cycles (Wolf Theorem 6.16) |
| `Channel/Positive` | 13 | positive and k-positive maps, decomposability, examples |
| `Channel/Recovery` | 2 | Petz recovery maps |
| `Channel/Schmidt` | 21 | Schmidt decomposition, rank and number of bipartite vectors |
| `Channel/Twirl` | 2 | Weyl twirls |
| `Channel/…` | | `ChoiTypeMap`, `Determinant`, `Irreducible`, `KoashiImoto`, `LorentzNormalForm`, `PerronFrobenius`, `POVM`, `PSDConeAutomorphism`, `Schwarz`, `Semigroup`, `Wigner` as before |
| `Kraus` | 63 | 14 top-level modules: words, word spans, transfer maps, blocking, injectivity |
| `Kraus/MixedMap` | 7 | mixed transfer maps of two families and their gaps |
| `Kraus/PrimitiveFixedPoint` | 7 | fixed points of primitive families |
| `Kraus/Wielandt` | 34 | the quantum Wielandt inequality and primitivity criteria |
| `Entropy/Classical` | 5 | Shannon entropy and classical mutual information |
| `Entropy/Conditional` | 22 | conditional entropy and its continuity and movement |
| `Entropy/Markov` | 9 | states with equality in strong subadditivity and their block forms |
| `Entropy/MutualInformation` | 10 | mutual information |
| `Entropy/Recovery` | 4 | recovery and the equality case of data processing |
| `Entropy/Relative` | 23 | relative entropy and its integral representations |
| `Entropy/Renyi` | 9 | Rényi entropies |
| `Entropy/StrongSubadditivity` | 12 | strong subadditivity and its equality case |
| `Entropy/Surprisal` | 3 | surprisal moments of a bipartite vector |
| `Entropy/Typical` | 11 | typical subspaces and states of i.i.d. sources |
| `Entropy/VonNeumann` | 16 | von Neumann entropy and its bounds |
| `Probability` | 74 | `FiniteUniformConditioning` at the top level |
| `Probability/Concentration` | 6 | matrix Bernstein, second moments, covariances |
| `Probability/Gaussian` | 10 | complex Gaussian vectors and matrices |
| `Probability/Haar` | 5 | Haar random unitaries and subspaces |
| `Probability/Measurable` | 13 | measurability of matrix-valued maps |
| `Probability/Measure` | 2 | product measures |
| `Probability/PoissonWord` | 23 | the Poisson word law and its counts |
| `Probability/Sampling` | 14 | random sampling of subspaces and images |
| `Representation/Bell` | 3 | Schur labels on tensor powers of the maximally entangled pair |
| `Representation/Character` | 6 | characters, irreducible labels, regular trace |
| `Representation/Coherent` | 8 | coherent states, Husimi functions, symbols |
| `Representation/Partition` | 8 | Young diagrams, hook and Weyl dimension formulas |
| `Representation/Permutation` | 15 | permutation representations, label projectors, isotypic parts |
| `Representation/Replica` | 11 | copies of a tripartite system with copy permutations, no regions |
| `Representation/SchurWeyl` | 12 | Schur–Weyl duality and highest weights |
| `Representation/SymmetricGroup` | 4 | branching, Casimir and Jucys–Murphy elements |
| `Representation/TensorPower` | 10 | actions on tensor powers, splitting copies |
| `Representation/Twirl` | 3 | unitary twirls |
| `Representation/YoungSubgroup` | 6 | Young subgroups acting on grouped copies |
| `ManyBody/Entropy` | 52 | regional entropy and information at the top level; `Cut`, `Filter`, `Typical` |
| `ManyBody/Subspace` | 20 | viable subspaces and their trimming; `Sampling` |
| `ManyBody/Replica` | 143 | `AddedSite`, `BandMetric`, `Bell`, `CompressedSite`, `Configuration`, `Label`, `LowDefect`, `Metric`, `Symbol` |

Before the move: `Algebra` 172 modules (164 at the top level), `Analysis` 604
(544), `Channel` 152 at the top level, `Entropy` 192 (137), `Representation` 181
(161), `Probability` 45 (34), `Kraus` 19 at the top level, `Spectral` 3,
`Topology` 4, `QPF` 4. After it, no directory of these layers has more than 17
modules at its top level.

## The module map

`scripts/library_layers_module_map.txt` lists 1,211 moves of modules, 119
merges of one-lemma modules into the module of their object, 306 moves of
`QICLeanTest` files that follow their modules, and the 52 modules of these
directories that stay. `scripts/apply_library_layers.py` applies it with
`git mv`, appends the merged modules, and rewrites the module names and paths in
`QICLean`, `QICLeanTest`, `scripts`, `blueprint`, `docs` and the workflows. It is
idempotent, and it leaves alone, and reports, a module of these directories
that the map does not know, so it can be applied again after another branch is
merged:

```sh
python3 scripts/apply_library_layers.py            # this repository
python3 scripts/generate_import_aggregators.py     # then the aggregators
python3 scripts/apply_library_layers.py --downstream ../TNLean   # a dependent
```

The downstream mode rewrites every reference in the tracked text files of the
dependent repository and then lists each `import QICLean.…` that names no module
of this checkout.

Later sections of the map divide `Channel/FixedPoint` (43 moves) and `Channel/Peripheral` (45
moves and two test files) into subdirectories by object. The import-only module
`Channel.Peripheral.CyclicDecomposition` was deleted; its six modules are now in
`Channel/Peripheral/Irreducible`, whose aggregator replaces it. The import ratchet reads the recorded entries of its base revision under the moves of
the map, so that moving a module renames its entries instead of adding new ones.

## How the modules were placed

Each module was read by its statements (a script over the declaration
signatures, then a reading of the modules by directory) and given the lowest
layer whose objects state it. Placing every module at its content layer is not
consistent with the imports: 153 imports lead from a module to one whose
statements belong to a higher layer, usually for one lemma of a proof. The final layer of each
module minimizes the number of layers by which modules are displaced from their
content, subject to imports pointing downward. Four declaration groups were
moved first because their modules caused the largest displacements:

- the density matrices left `Channel/Basic` for `Analysis/Order/DensityMatrix`;
- the tripartite partial traces and the Hermiticity and positivity of partial
  traces left `Analysis/Entropy` for the partial-trace module, which then
  moved to `Algebra/PartialTrace` (a partial trace of matrices on product
  indices is algebra);
- `commute_permOp_of_apply_eq` left `Representation/ReplicaSiteOp` for the
  module that defines `permOp`, and the lemmas on one-copy operators
  (`siteOp_eq_reindex`, `l2_opNorm_siteOp_le`, `siteOp_sum`,
  `conjTranspose_siteOp`) left it for `Representation/SchurWeyl/Commutant`, which
  defines `siteOp`, so that the coherent-state modules no longer import a module
  about sites.

155 modules remain in a layer other than that of their statements; 200 modules
hold declarations of two layers. Both lists, with the import that places each
module and the declarations that should move, are in
`docs/library_layers_inventory.md`; they are the candidates for the splits that
would let each module sit at its content. The inventory also lists the moved
modules that failed the strict Lean check at the base revision; they are repaired.

### Modules about sites and regions (#1174)

In all, 41 modules of `Analysis`, 79 of `Entropy` and 96 of `Representation`
moved to `ManyBody`, because their statements mention sites, regions or
supported operators. Of the regional, physical-buffer and replica families
that #1174 lists by name, 54 moved: 7 to `ManyBody/Entropy`, 2 to
`ManyBody/Subspace` and 45 to `ManyBody/Replica`. Fourteen state nothing about
sites and stay below: the
nine replica modules of `Representation/Replica`, whose copies are copies of a
tripartite system indexed by `Fin k`; the three physical-buffer modules of
`Entropy/MutualInformation`, whose statements are mutual information of
marginals of a fixed tripartite state; `RegionalEnergyCalibration`
(`Analysis/Projection`, scalar budgets and closeness of subspaces) and
`ReplicaComponentUniformRate` (`Analysis/Parameter`, a scalar inequality).

## Directories that imported each other

The base revision recorded eight pairs of directories importing each other.
Each disappeared because the modules carrying the upward edges moved:

| Pair | Upward edges before | Removed by |
|---|---|---|
| Algebra ↔ Channel | 4 from Algebra | the partial trace and `swapMatrix` users moved to Channel, the partial trace to Algebra |
| Analysis ↔ Channel | 22 from Analysis | operator means, Lieb concavity and trace-norm contraction moved to Channel; entropy modules to Entropy |
| Analysis ↔ Entropy | 10 from Analysis | the entropy modules of Analysis moved to Entropy, the regional ones to ManyBody |
| Analysis ↔ Probability | 4 from Analysis | the sampling modules moved to Probability |
| Analysis ↔ Representation | 47 from Analysis | the replica modules moved to ManyBody/Replica and Representation |
| Channel ↔ Entropy | 3 from Channel | the relative-entropy modules of Channel/Schwarz moved to Entropy |
| Channel ↔ Kraus | 13 from Channel | the Wielandt modules of Channel moved to Kraus/Wielandt |
| Entropy ↔ Representation | 7 from Entropy | the regional Schur-label modules moved to ManyBody/Replica |

`MUTUAL_DIRECTORIES` is now empty.

## Order inside each layer

Inside a layer the subdirectories are ordered: a subdirectory imports only the ones before it.
The table is `scripts/library_sublayers.json`; `scripts/check_import_layers.py` reads it, and an
import against the order is an entry of `SUBLAYER_DEBT`, which may only shrink. "(top)" stands
for the modules directly below the layer.

The order was fixed by listing the subdirectories of each layer from the objects that need no
other (numbers, sets, subspaces) to the statements that use all of them, and then moving single
subdirectories while that lowered the number of imports against the order. An import that
remains against the order marks a module filed under the wrong object, or a lemma to move down;
it is repaired by moving the module or the lemma, never by changing the order to fit.

| Layer | Order | Imports against the order |
|---|---|---|
| `Algebra` | Combinatorics < Polynomial < Module < PerronFrobenius < Matrix < Unitary < (top) < Hermitian < Word < OperatorSchmidt < Nilpotent < MatrixAlgebra < StarSubalgebra < Kronecker < SpinCover < Cohomology | 2 |
| `Analysis` | Complex < Calculus < Metric < Subspace < Projection < Topology < Order < FixedPoint < Real < FunctionalCalculus < Support < Logarithm < Isometry < Norm < TraceNorm < Resolvent < TensorProduct < Convexity < OperatorMean < TraceInequality < Majorization < Optimization < FilterFunction < Exponential < ClusterExpansion < CyclicInequality < Parameter < Cohomology < (top) | 1 |
| `Spectral` | Eigenvalue < Projection < Radius < Jordan < Perturbation < Gap < Filter < LowEnergy < (top) | 0 |
| `Channel` | Choi < KrausMap < Twirl < (top) < Dilation < PartialTrace < Convexity < Schmidt < Schwarz < Positive < Entanglement < OperatorMean < Determinant < FixedPoint < ConditionalExpectation < Irreducible < Wigner < Peripheral < Semigroup < PerronFrobenius < KoashiImoto < Recovery < POVM < Measurement < OperatorSystem < PSDConeAutomorphism < LorentzNormalForm < ChoiTypeMap < Gluing | 14 |
| `Kraus` | Tactic < (top) < MixedMap < PrimitiveFixedPoint < Wielandt | 0 |
| `Entropy` | Classical < VonNeumann < Relative < Renyi < MutualInformation < Recovery < Markov < StrongSubadditivity < Conditional < Surprisal < Typical < (top) | 13 |
| `Probability` | Measurable < Measure < Concentration < (top) < Gaussian < Haar < PoissonWord < Sampling | 1 |
| `Representation` | Partition < SymmetricGroup < Permutation < TensorPower < YoungSubgroup < Character < Replica < SchurWeyl < Twirl < Coherent < Bell < (top) | 17 |

48 imports are recorded. `ManyBody` and `Circuit` keep the orders of
`docs/many_body_circuit_architecture.md`, which the same script checks.

### Order inside a subdirectory

A subdirectory of a layer that is divided by object orders its own subdirectories in the same
way. The orders are the tables under "inside" in `scripts/library_sublayers.json`. The script
checks them between two modules of that subdirectory, in addition to the order of the layer,
and an import against them would be an entry of `SUBLAYER_DEBT`.

| Subdirectory | Order | Imports against the order |
|---|---|---|
| `Channel/FixedPoint` | MeanErgodic < Stationary < Algebra < DensityBlock < DirectSum < Weighted | 0 |
| `Channel/Peripheral` | Spectrum < Projection < Asymptotic < Irreducible < Cycles | 0 |

In `Channel/FixedPoint` one import went against the order when it was divided:
`Stationary/TraceNonincreasingProductSpan` imported `DirectSum/DirectSumBlockRetraction` for the
reindexing of a matrix endomorphism and the facts that positivity, trace preservation, trace
nonincrease and positive definiteness survive it. These mention no direct sum, so they moved to
the modules of their objects: the endomorphism and positive definiteness to
`Algebra/Matrix/MatrixReindex`, its trace adjoint to `Algebra/Matrix/MatrixTracePairing`, the
positivity and trace facts to `Channel/Basic`, and the Schwarz inequality to
`Channel/Schwarz/AbstractMultiplicativeDomain`.

## Enforcement

`scripts/check_import_layers.py` assigns every module of these directories to
its layer and rejects an import outside the table above; its `DEBT` record is
empty and may only shrink, and so is `MUTUAL_DIRECTORIES`.
`scripts/test_architecture_policies.py` tests the chain, the many-body layers
and the siblings. A new module goes into the lowest layer whose objects state
it; a module that needs one lemma of a higher layer is split instead of placed
higher.
