# Trace-pairing duality for families of matrix algebras

Date: 2026-09-21

The word-span argument in
`QICLean/Kraus/Wielandt/Primitivity/StronglyIrreducibleToFullWordSpan.lean`
carried its own proof that every linear functional on a finite complex matrix
algebra is a trace pairing, together with the criterion that the representing
matrix vanishes exactly when the functional does. Both facts are instances of
the duality induced by a nondegenerate bilinear form on a finite-dimensional
space, which the library already owns for the trace pairing of a single matrix
algebra. This pass routes the span argument through that duality and adds the
two indexed trace pairings that the analogous block-indexed and paired span
arguments need.

## Added

`QICLean/Algebra/TraceFormDuality.lean` collects the duality criterion and its
trace-pairing instances.

| Declaration | Content |
|---|---|
| `LinearMap.BilinForm.eq_top_of_forall_apply_eq_zero` | a subspace of a finite-dimensional space is everything once the only vector pairing to zero with all of it under a nondegenerate form is the zero vector |
| `Matrix.eq_top_of_trace_separating` | the same criterion for the trace pairing of one finite complex matrix algebra |
| `Matrix.piTraceForm`, `Matrix.piTraceForm_apply`, `Matrix.piTraceForm_nondegenerate`, `Matrix.eq_zero_of_forall_sum_trace_mul_eq_zero`, `Matrix.eq_top_of_pi_trace_separating` | the trace pairing of a finite family of matrix algebras, summed over the blocks, with its nondegeneracy and span criterion |
| `Matrix.prodTraceForm`, `Matrix.prodTraceForm_apply`, `Matrix.prodTraceForm_nondegenerate`, `Matrix.eq_zero_of_forall_trace_mul_add_eq_zero`, `Matrix.eq_top_of_prod_trace_separating` | the trace pairing of a product of two matrix algebras, with its nondegeneracy and span criterion |

The block-indexed and product pairings are separate because a product of two
matrix algebras of different sizes is not a dependent family over a two-element
index type, so neither pairing is an instance of the other.

## Removed

| Declaration | Replacement |
|---|---|
| `linearMap_apply_eq_sum` (private) | none needed: it existed only to expand a functional over matrix units inside the representation proof |
| `phi_eq_trace_mul` (private) | `Matrix.eq_top_of_trace_separating`, which supplies the representation step through `Matrix.traceBilinForm_nondegenerate` and the induced equivalence with the dual space |
| `rep_eq_zero_iff` (private) | same: the span criterion consumes the vanishing statement directly, so the representing matrix is never named |

All three were private and referenced only inside their own file, by the single
span lemma rewritten below. No public name, statement, or proof changed, and no
blueprint tag names any of them.

## Rewritten

`wordSpan_eq_top_of_tracePairBilin_re_pos` (private) no longer argues by
contradiction through a nonzero functional in the dual annihilator. It applies
the trace span criterion directly: a matrix whose trace pairing against every
word of the given length vanishes is shown to be zero, because otherwise its
adjoint makes the left-hand side of the trace-pairing identity vanish while the
positivity hypothesis makes the right-hand side strictly positive.

## Checked

* The new module and the rewritten module build with the package linter options,
  as does the whole library root.
* The text style linter reports nothing on the branch.
* No `sorry`, `axiom`, or `native_decide` appears in either module.
* The import aggregators were regenerated and verified, and the module-policy
  checkers pass.

## Deferred

The block-indexed and product span criteria are stated here but not yet consumed
inside this library; they exist for the downstream separation arguments over
families of matrix algebras, which will adopt them once the dependency pin moves.
