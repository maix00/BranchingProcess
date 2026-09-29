# Mogulskii α = 2 proof route

This route follows Mogulskii's 1974 proof structure. The completed Lean
modules are ingredients; they do not yet imply the full theorem.

## Target reduction

First prove the sharp logarithmic asymptotic for a horizontal interval tube
of a centered finite-variance random walk, at every scale `aₙ → ∞` with
`aₙ / √n → 0`. Then use Mogulskii's finite partition argument to pass from
horizontal tubes to the paper's piecewise regular corridors. Keep strict and
closed corridor events separate for the two Portmanteau directions.

## Proof stages

1. **Sharp lattice model.** The simple symmetric walk is handled by the exact
   killed-interval eigenvalue formula. Its principal eigenvalue gives the
   `-π²/2` rate. The existing `Spectral/Scaling/` results formalize this
   special model.
2. **One diffusive block for a general finite-variance law.** For fixed
   `c > 0`, take a block of length `⌊c aₙ²⌋`. Donsker convergence, applied at
   this block scale, must give lower and upper bounds for the killed
   transition from a compact core of the interval back into that core. The
   bounds must be uniform over the starting point; obtain uniformity from
   compactness and continuity of the limiting Brownian killed transition.
3. **Sharp block exponent.** Identify the limiting Brownian killed
   transition on the interval and prove that its core-to-core mass has
   logarithmic rate `-π² c / (2 w²)` as `c → ∞`, where `w` is the interval
   width. This is the principal Dirichlet eigenvalue step. A survival bound
   or endpoint CLT alone does not establish this transition estimate.
4. **Iterate the core-to-core kernel.** Compose the uniform block bounds and
   discard the incomplete final block. First take `n → ∞` for fixed `c`,
   then take `c → ∞`. This yields the sharp horizontal-tube rate without
   paying a macroscopic entrance cost.
5. **Mogulskii's finite partition step.** Partition time at the corridor's
   regularity points. The upper bound multiplies the corresponding
   horizontal killed-block bounds. For the lower bound, shrink each
   sub-corridor by a positive margin, enforce endpoint margins, and use the
   block estimates to concatenate. Finally send the partition mesh and
   margins to zero.
6. **Variance and stable-law specialization.** Standardize by the square
   root of the variance and transport the rate back. The general stable-law
   theorem remains a separate extension; it is not needed to establish the
   `α = 2` result.

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

**Next proof obligation:** formalize the uniform, fixed-`c` Brownian
core-to-core killed-transition limit and its principal-eigenvalue asymptotic.
Only after that lemma compiles should the existing blocking interface be
used to claim the sharp finite-variance horizontal theorem.

The tempting forced-sign entrance construction is not a substitute: a cost
`exp(-C aₙ)` is negligible only if `aₙ³/n → 0`, which is not part of the
Mogulskii scale assumptions.
