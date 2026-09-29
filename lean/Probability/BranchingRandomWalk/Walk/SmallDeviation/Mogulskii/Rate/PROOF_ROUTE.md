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
   `α=2` specialization, there is a direct two-limit implementation of that
   step: for each fixed `c > 0`, take `mₙ = ⌊c aₙ²⌋`. Since `aₙ → ∞`,
   `mₙ → ∞`, so Donsker transfers the fixed Brownian endpoint-band events
   along this sequence; since `aₙ²/n → 0`, the number of blocks satisfies
   `(⌊n/mₙ⌋+1) aₙ²/n → 1/c`. First take `n → ∞` with `c` fixed, then let
   `c → ∞`. This avoids the invalid forced-entry cost and is a finite-variance
   specialization of the source's variable-block/diagonal step, not a claim
   that the general Lemma 4 diagonal has been formalized.
4. **Sharp lower constant.** The preceding fixed-`c` bound is only useful
   for the sharp rate after proving a Brownian lower estimate for every one
   of the seven endpoint-band events with a small inner radius. Choose
   `radius(c), ε(c) > 0` so
   `2 (radius(c) + 4 ε(c)) √c < 1` and
   `radius(c) √c → 1/2`, while the seven endpoint bands remain in a compact
   subinterval of the rescaled corridor. The needed estimate is that their
   minimum mass has logarithm at least
   `-(π²/2 + o(1)) c`. Its prefactor may depend on `c` subexponentially.
   A concrete spectral reduction is available. For a fixed shift
   `i ∈ {-3,…,3}`, translate the increment path by `-i ε`: the translated
   path starts at `-i ε` and the endpoint band becomes `(-ε,ε)`. A path
   confined to the smaller centered interval of radius `R` translates back
   into the required centered interval of radius `R + 3 ε`. Thus it is
   enough to lower-bound, uniformly over these seven central starting sites,
   the killed finite-interval mass from a central start into a central target
   band. `Spectral/Target/LowerBound.lean` already supplies the sine-eigenstate
   estimate for targets with positive parity-compatible density; the missing
   construction is the band-specific target finset, its density/weight
   bounds, and its path-event identification. Transfer that closed
   Rademacher path event to Brownian motion using the endpoint closed-event
   Portmanteau theorem, then include it in the desired open band event. Choose
   `ε/R → 0` slowly (for example a reciprocal power of `c`): the corridor
   slack and the logarithm of the target-density prefactor then vanish after
   division by `c`. A survival-only Brownian estimate does not prove these
   seven separate endpoint bounds.
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
- `Spectral/` proves the symmetric nearest-neighbor interval calculation.
  The remaining task is to connect its asymptotic to the fixed-scale
  Brownian horizontal and endpoint-band estimates used by Lemma 4.

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
