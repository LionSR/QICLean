# Soft residuals from hard residuals of the same positive matrix

The contribution proves three steps. First, pointwise domination by a
nonnegative real spectral function dominates vector norms under the real
functional calculus. The proof constructs the bounded ratio of the two
functions, treating zeros of the denominator explicitly. It uses no
comparison for noncommuting matrices and no operator-monotonicity premise.
The real functional calculus makes the generic comparison valid for every
finite square matrix; the intended application is Hermitian, and the soft
residual application explicitly requires a positive semidefinite matrix.

Second, the actual finite-series soft function is increasing on nonnegative
inputs. Its scalar remainder is at most the hard remainder at any nonnegative
cutoff plus `E = (t / m) * (T / t)^m`, with `t > 0` and `m >= 1` explicit.
Below the cutoff this uses the existing polynomial remainder. Above the
cutoff it uses monotonicity and the same remainder evaluated at the cutoff.
Monotonicity of the soft function alone is not used to infer monotonicity
of its remainder. The scale and order remain independent, including the
source's fixed order four and large scale. At order four the error is
exactly `T^4 / (4*t^3)`, not an exponentially small error in the scale.

Third, functional calculus and the triangle inequality yield the actual
vector-norm comparison between the soft and hard residuals of the same
positive matrix. There is no assumed successful approximation, small global
norm error or soft residual bound. The cutoff may be zero and the matrix
index may be empty. A physical application must still substitute the actual
energy-centered regional matrix and derive its hard-tail bound on the
original low-energy space. No reverse soft-to-original comparison is proved.

These are auxiliary results for ALVV, arXiv:1602.08828v2,
Definitions `def:hard-trunc`, `def:soft-trunc`, and `lem:exp-approx`,
lines 873–886, 1178–1185 and 1195–1255. They do not establish the printed
uniform energy estimate, the printed cluster estimate, or the final GEN
or running-time conclusions. Existing source-error records and their
counterexamples remain unchanged.
