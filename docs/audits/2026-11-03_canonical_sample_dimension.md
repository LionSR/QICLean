# Exact dimension of the canonical range sample

The actual canonical range sample has dimension exactly the retained
coordinate count min(s, rank P), for every seed, including rank zero and
zero nominal size. Every linear image of the sample therefore has dimension
at most s. These are the original existing sampler and actual submodule
image, without a viability hypothesis.

The proof reuses the established dimension theorem for basis-parametrized
randomSubspace. It changes the dependent finrank expression to the literal
existing sampler before rewriting; this preserves the induced submodule
instances. The linear-image consequence then uses Mathlib's dimension
monotonicity under a linear map. The target may be any complex module.

This is the deterministic sample dimension in ALVV, arXiv:1602.08828v2,
Lemma l:rs, lines 530–558. It is used twice by the physical canonical-parent
argument: unconditional output size and transfer of a successful sample
through the deterministic iteration. No probability bound is asserted by
these two dimension lemmas alone.
