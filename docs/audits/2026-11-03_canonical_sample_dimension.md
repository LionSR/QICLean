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

The source-only branch starts from frozen QIC 8bf0495a. Exact-name private
checking used held TN 435cbe7fe5 and its own QIC b2ea12a0, with exact selected
source/object, root-input, prebuilt-Mathlib and importer-closure guards.
The final module passed in 4.763 seconds with 32 protected pairs. The
combined four-public imported foundation inspection, including the physical
canonical-parent factory, passed in 8.269 seconds with 765 pairs, using
only propext, Classical.choice and Quot.sound. Its temporary source was
deleted. Generated imports, source blueprint synchronization, reader prose,
proof integrity and whitespace checks passed.

The worktree has no .lake. No provider or cache was modified, no compiled
artifact was copied and no Mathlib source was built. Default proof budgets
were retained. Ordinary companion and compiled-book gates remain part of
the coordinated integration.
