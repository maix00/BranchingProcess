# Mogulskii α = 2 proof route

This document records the proof dependencies for the horizontal small-
deviation theorem and the later corridor theorem. A compiled component is not
evidence that the full asymptotic has been proved.

## Target and normalization

For centered, unit-variance IID increments and a scale `aₙ` satisfying
`aₙ → ∞` and `aₙ / √n → 0`, first prove the sharp logarithmic asymptotic for
the probability that the walk stays in a horizontal interval of width
`aₙ`. Keep the interval width and its half-width explicit: the principal
Dirichlet exponent for a centered interval of width `w` is
`-π²/(2 w²)` per unit time. The corridor theorem then follows from the
finite partition argument in Mogulskii's §3.

## Source proof and formalization route

The route below follows the 1974 paper's lemmas and equations, rather than
using a forced entrance path.

1. **Stable-process horizontal rate (Lemma 1 and §4).** For `α = 2`, the
   stable process is Brownian motion. The paper obtains its horizontal
   small-deviation constant using the exact interval-survival calculation
   for the symmetric `±1` walk. The repository's `Spectral/` development
   formalizes that lattice calculation. With interval width one, the rate is
   `-π²/2`; with interval `(-1,1)`, it is `-π²/8`. These are the same
   eigenvalue under different width conventions.
2. **Discrete block comparisons (Lemma 3).** Equation (32) is the upper
   comparison: confinement of the full path forces bounded oscillation on
   each complete increment block, and disjoint IID blocks factor. Equation
   (33) is the lower comparison. For block ratio `c = m/n`, it uses
   `k = ⌊c⁻¹⌋ + 1` blocks and the minimum over the seven endpoint bands
   indexed by `i ∈ {-3,…,3}`. A block event combines confinement to the
   inner interval with its endpoint in the band
   `((i-1)ε,(i+1)ε)`; the finite shifts cover every starting point in the
   return core. The source and target core coincide only to make this
   endpoint-band iteration composable.
3. **Transfer to the walk (Lemma 4, equations (38)–(44)).** In the paper's
   general stable-domain setting, fixed-scale functional convergence is
   extended to a variable block length `y(n)` and then to every admissible
   spatial scale by a slowly diverging diagonal. For the unit-variance
   `α=2` specialization, the block-scale part has a direct two-limit
   implementation: for each fixed `c > 0`, take `mₙ = ⌊c aₙ²⌋`. Since
   `aₙ → ∞`, `mₙ → ∞`, so Donsker transfers the fixed Brownian endpoint-band
   events along this sequence; since `aₙ²/n → 0`, the number of blocks
   satisfies `(⌊n/mₙ⌋+1) aₙ²/n → 1/c`. First take `n → ∞` with `c` fixed,
   then let `c → ∞`. The Brownian endpoint-band input below has its own
   auxiliary diffusive limit, used to transfer the finite Rademacher spectral
   estimates to Brownian closed events. Thus this is a finite-variance
   specialization of the source's variable-block/diagonal step, not a claim
   that the general Lemma 4 diagonal has been formalized.
4. **Sharp lower constant.** The preceding fixed-`c` bound is only useful
   for the sharp rate after proving a Brownian lower estimate for every one
   of the seven endpoint-band events. Keep the starting point at the center;
   no spatial translation or entrance estimate is needed. For each
   `i ∈ {-3,…,3}`, the spectral target is a narrower closed band
   `[(i - 1/2) ε, (i + 1/2) ε]`, strictly inside the block event's open band
   `((i - 1) ε, (i + 1) ε)`. Restrict paths to a closed centered interval of
   radius `R`, strictly smaller than the open block radius `ρ`. Thus the
   spectral event is a subset of the desired open endpoint-band event, with
   strict slack at both the path boundary and endpoint boundary. Choose
   `R(c), ρ(c), ε(c) > 0` with
   `R(c) < ρ(c)` and `7 ε(c) < R(c)`,
   `2 (ρ(c) + 4 ε(c)) √c < 1`,
   `R(c) √c → 1/2`, and `ε(c) / R(c) → 0`; for large `c`, every target
   band lies well inside the spectral interval, where the sine ground state
   is uniformly bounded below. The target contains a positive proportion of
   parity-compatible lattice sites of order `ε(c) / R(c)`. The finite
   spectral estimate has principal factor
   `cos(π / (2 R(c) √N + o(√N)))^N`, whose logarithm tends to
   `-π² / (8 R(c)^2)` for a unit-time Brownian block. Thus its logarithm,
   divided by `c`, tends to `-π²/2` as `c → ∞`; the target-density
   prefactor is negligible when, for example, `ε(c) / R(c)` is a reciprocal
   power of `c`. These parameter requirements are compatible: for
   `t = c^(-1/8)`, one may take
   `R = (1 - 10t) / (2√c)`, `ε = t R`, and `ρ = R + ε` for all sufficiently
   large `c`. Then
   `2 (ρ + 4 ε) √c = (1 - 10t)(1 + 5t) < 1`,
   `7 ε < R`, `R√c → 1/2`, and `log(ε/R) / c → 0`.

   For each fixed `c` and each of the seven targets, let the Rademacher
   interval radius tend to infinity with its diffusive width tending to `R`.
   The proof bridge must be explicit: identify the killed matrix target mass
   with the IID Rademacher event “all partial sums lie in the closed lattice
   interval and the final site lies in the chosen band”; center the lattice
   interval and scale that path event; apply the closed-event Portmanteau
   inequality in its `limsup ≤ Brownian closed mass` direction; then use the
   strict inclusions above to bound the desired open band mass from below.
   `Spectral/Target/LowerBound.lean`
   already supplies the sine-eigenstate estimate for targets with positive
   parity-compatible density. The missing pieces are the band-specific
   target finset and its density/weight bounds, plus the path-event
   identification and its Donsker/Portmanteau connection. A survival-only
   Brownian estimate does not prove these seven separate endpoint bounds.
5. **General corridors (§3).** Once the horizontal rate is established,
   partition at the finitely many boundary discontinuities. Apply the
   horizontal upper estimate to outer block corridors and the lower estimate
   to strictly shrunken corridors with endpoint margins. Then use the
   paper's finite-union and approximation steps for the stated corridor
   class.

In Lean, `returnKernel` is an implementation of the probability of a block
starting in a core, staying in the outer interval, and ending in that same
core. The kernel interface expresses the iteration in (33); it is not an
additional probabilistic entrance argument and it is not the source of the
sharp spectral constant.

## Verified components

- `Discrete/Horizontal.lean` proves the upper block comparison from block
  oscillation and independence, including the incomplete-block upper bound.
  It also proves the abstract implication from a uniform one-block return
  bound to its iterated lower bound.
- `Discrete/EndpointBands.lean` formalizes measurability of each endpoint
  band, the seven-shift covering of the return core, the containment in the
  larger corridor, and the resulting core-to-core return estimate. The
  corridor radius and endpoint-band spacing are parameters. The return bound
  also covers an arbitrary requested horizon by taking enough complete
  blocks and restricting the longer-path event to its prefix.
- `Discrete/DonskerEndpointBands.lean` transfers a fixed open-radius,
  fixed-band Brownian endpoint event to a lower bound for the corresponding
  normalized IID block probability. It intersects the seven eventual bounds
  and combines them with the return-kernel iteration for block counts and
  horizons that may vary with the ambient index. This result is conditional
  on explicit Brownian endpoint-band mass bounds and keeps the normalized
  block radius and band spacing fixed.
- `Rate/EndpointBands.lean` composes that estimate with blocks of length
  `⌊c aₙ²⌋` and proves the logarithmic liminf bound for every
  `IsMogulskiiScale`. It is a genuine scale-transfer theorem, but remains
  conditional on the Brownian band masses and is not yet the sharp lower
  Mogulskii rate.
- `Rate/Upper.lean` gives an endpoint-CLT upper bound. It is non-sharp and
  does not establish the upper half of the Mogulskii rate.
- `Spectral/` proves the symmetric nearest-neighbor interval calculation and
  a generic target-mass lower bound. The remaining task is the explicit
  finite-target construction and path-event/Portmanteau bridge that turns
  this spectral bound into the seven fixed-scale Brownian endpoint-band
  estimates used by Lemma 4.

## Remaining proof obligations

1. Prove the Brownian small-radius exponent for each of the seven endpoint
   bands, with common parameter choices satisfying the corridor-fit
   inequality. The spectral API already gives target-mass bounds for
   finite-state intervals, but the band targets and the closed-event
   Portmanteau bridge have not yet been connected. Mere positivity is not
   enough for the sharp constant.
2. Use those bounds in `Rate/EndpointBands.lean`, then take `c → ∞` and
   remove the small corridor slack to obtain the sharp horizontal lower rate.
3. Prove the sharp horizontal upper rate by applying the discrete
   oscillation-block comparison and the fixed-scale path limit, then passing
   to arbitrary subdiffusive scales. The existing endpoint CLT bound is not
   enough for the sharp constant.
4. Combine the horizontal upper and lower rates with the already separated
   finite-partition corridor argument, checking the open/closed Portmanteau
   directions and endpoint margins.

Do not use a forced run of same-sign increments to enter the core: a cost
`exp(-C aₙ)` is negligible on the target scale only under the extra condition
`aₙ³/n → 0`, which is not among the theorem's assumptions.
