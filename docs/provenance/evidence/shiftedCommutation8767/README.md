# Shifted-power commutation verification

The source revision and command logs are recorded in `checks.json` and the
three-row provenance shard. The package build, strict exponent-zero regression,
and all three public axiom reports passed. The kernel reports use only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`.

The proof recovers commutation from a nonzero power of a positive definite
matrix, then applies this to a positive shift of a positive semidefinite x.
The concrete inverse-filter implication assumes a > 0, b > 0 and commutation
with the actual shifted power; ρ is arbitrary. The regression exhibits a
singular positive x and a non-Hermitian ρ that commutes with the zero-exponent
filter but does not commute with x. Thus the exponent restriction is essential.

`check_provenance.py` applies the frozen TNLean policy and schema at
`c738e87489bc1b4ae1d58a6bdefb2c1cbd654114`, asserting their hashes. It checks
this three-row shard, immutable production bytes, complete original notices,
log hashes and exact kernel reports; inherited shards are not re-audited here.
The same policy lexer checks production and regression code for forbidden proof
commands. Mathematical source text is original; no upstream Lean proof text
was reused. Codex (GPT-6) assisted proof preparation and verification.

Native descending stationarity, the commutation of the actual filter and
marginal, and the identification of the simplex derivative remain separate
obligations. These three results supply only the spectral implications that
follow those steps. Router and full-book integration checks are recorded in a
separate later record; they are not attributed to this immutable source leaf.
