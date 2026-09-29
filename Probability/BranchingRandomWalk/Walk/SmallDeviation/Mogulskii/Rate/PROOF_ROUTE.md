# Mogulskii α = 2 proof route

This route follows Mogulskii's 1974 proof structure. The completed Lean
modules are ingredients; they do not yet imply the full theorem.

## Target reduction

First prove the sharp logarithmic asymptotic for a horizontal interval tube
of a centered finite-variance random walk, at every scale `aₙ → ∞` with
`aₙ / √n → 0`. Then use Mogulskii's finite partition argument to pass from
horizontal tubes to the paper's piecewise regular corridors. Keep strict and
closed corridor events separate for the two Portmanteau directions.

## Proof stages (following the original lemmas and sections)

1. **Horizontal prototype, stable input.** Mogulskii's Lemma 1 derives the
   small-deviation rate of the strictly stable process from self-similarity
   and the block inequalities in Lemma 2. At `α = 2` the stable process is
   Brownian motion. The corresponding path convergence input is the
   functional CLT already formalized in the Donsker modules.
2. **Transfer from the stable process to the walk.** Formalize the discrete
   counterparts of Lemma 2, collected as Lemma 3 in the paper. They compare
   a whole horizontal-tube event with products of independent block events,
   including the shifted endpoint bands needed for the lower bound. Combine
   these inequalities with the functional CLT for blocks of length
   `⌊c aₙ²⌋`, then take the block ratios in the order used in Lemma 4. This
   yields the horizontal rate for every centered finite-variance increment
   law. In kernel language, the lower half is a uniform core-to-core return
   estimate; its source and target must be the same core for iteration.
3. **General corridors.** With the horizontal rate in hand, §3 partitions
   time at the boundary discontinuities. The upper estimate is a product of
   horizontal block probabilities. The lower estimate uses strictly
   shrunken block corridors, endpoint margins, and the lower half of Lemma 4.
   Then extend by finite unions and inner/outer approximation to the stated
   corridor class.
4. **Compute the `α = 2` constant.** In §4 Mogulskii evaluates the horizontal
   constant using the exact killed-interval transition formula for the
   symmetric `±1` walk. The principal cosine modes give `-π²/2`. The existing
   `Spectral/Scaling/` results formalize this lattice calculation. This
   supplies the constant in the stable-process estimate; a separate Brownian
   Dirichlet-kernel spectral theorem is not the original route.
5. **Variance and theorem statement.** Standardize increments by the
   standard deviation, transport the rate back, and state the result for the
   original scale and corridor functional. The general `α`-stable extension
   is separate and is not needed to finish the `α = 2` case.

## Current verified status

- The symmetric lattice spectral asymptotic, finite-variance Donsker input,
  corridor Portmanteau interfaces, block-scale arithmetic, and general
  sub-Markov blocking lemmas compile.
- `Rate/Upper.lean` adds an endpoint-CLT row bound. It is intentionally
  non-sharp: the endpoint event loses the principal spectral information.
- `Spectral/Diffusive/Return.lean` transfers a Brownian centered-tube event
  to a wider return target. Its current uniform estimate does **not** bound
  every row on that target interval, so it cannot by itself be iterated as a
  self-map kernel.
- The finite-partition lower-rate interface still has Gaussian-product and
  maximal-error hypotheses. It proves a nontrivial lower rate, not the sharp
  Mogulskii constant.

**Next proof obligation:** formalize the paper's discrete Lemma 3 bounds for
the horizontal tube. The lower block inequality must return mass to the
same compact core, uniformly in its starting point; the upper inequality
must retain the correct interval width. Feed these into Lemma 4's scaling
argument, then use the existing finite-partition corridor layer. The exact
`±1` spectral theorem supplies the constant, not a substitute proof of the
general finite-variance transfer.

The tempting forced-sign entrance construction is not a substitute: a cost
`exp(-C aₙ)` is negligible only if `aₙ³/n → 0`, which is not part of the
Mogulskii scale assumptions.
