# Uniform logarithmic absorption

The Mathlib-only module `LogPowerAbsorption` supplies a large constant beyond
any prescribed threshold, absorbing a logarithm into any positive power. Its
cubic consequence chooses the constant needed for independent interleaved
filter scales. The existing TN logarithm-square-root lemma is an active
specialization at exponent one half.

Strict actual-module verification passed in 4.528 s against TN5e19c052 and its
own QIC518e8d20, with protected root inputs and Mathlib artifacts. No provider
or cache was changed. The imported foundation inspection and combined ordinary
build are pending in the next canonical cohort; no new local check was started
after the requested safe point.
