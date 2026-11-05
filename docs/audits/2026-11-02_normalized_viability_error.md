# Projection preimages and normalized viability error

The projection-preimage argument in Arad, Landau, Vazirani and Vidick,
*Rigorous RG algorithms and area laws for low energy eigenstates in 1D*
(arXiv:1602.08828v2, Lemma l:2, lines 449–465) admits the following refinement.
If a subspace S is δ-close to T and δ<1, every t in T has a projection
preimage s in S satisfying both

    ‖s‖ ≤ ‖t‖/(1−δ),        ‖s‖² ≤ ‖t‖²/(1−δ).

Both estimates hold for the same vector. The proof inverts the positive
compression of the projection and uses its quadratic form. The original
public theorem retains its statement and follows by selecting the first
estimate.

Weighted composition similarly refines Lemma l:close (lines 484–489):
errors δ and ε compose to (1+θ)δ+(1+1/θ)ε for every θ>0, provided δ≥0.
The existing factor-two theorem is the specialization θ=1.

For nested targets T contained in T₊, an operator preserving T and sending
T₊⊥ into T⊥, expanding norms on T and contracting squared norms on T₊⊥ by
Δ≥0, improves an initial error 0≤δ<1 to

    δ′ = Δδ/(1−δ+Δδ).

The proof writes a suitable preimage as r+q with q perpendicular to T₊,
uses the sharper norm estimate to bound ‖q‖², and applies Cauchy–Schwarz
to the actual image vector. For a single target, the ratio δ/(1−δ)
therefore contracts by Δ. No gap between nested targets is assumed.
These are auxiliary refinements of Lemma l:er (lines 597–622) and
Theorem t:aisgapless (lines 1037–1041), rather than assertions that the
complete algorithms have been formalized.
