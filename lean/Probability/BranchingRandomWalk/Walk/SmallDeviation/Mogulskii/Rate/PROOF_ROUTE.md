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
3. **Transfer to the walk (Lemma 4, equations (38)–(44)).** First apply
   functional convergence at a fixed normalized scale. Then use the paper's
   norming functions `B` and `B*`, with `B*(u)=u²/L*(u)` at `α=2`, and a
   slowly diverging diagonal to pass from fixed-scale convergence to every
   prescribed subdiffusive scale. The diagonal must preserve the logarithmic
   rate after multiplication by `aₙ²/n`; a fixed diffusive-scale estimate
   alone does not do this. In the finite-variance, unit-variance
   specialization, `B(t) ~ √t` and `B*(u) ~ u²`, so this step must be stated
   directly for `IsMogulskiiScale` and its rounded block lengths.
4. **General corridors (§3).** Once the horizontal rate is established,
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
- `Rate/Upper.lean` gives an endpoint-CLT upper bound. It is non-sharp and
  does not establish the upper half of the Mogulskii rate.
- `Spectral/` proves the symmetric nearest-neighbor interval calculation.
  The remaining task is to connect its asymptotic to the fixed-scale
  Brownian horizontal and endpoint-band estimates used by Lemma 4.

## Remaining proof obligations

1. Prove positivity and the sharp small-radius logarithmic lower bound for
   the seven Brownian endpoint-band events, uniformly over the finite shift
   set. Their positivity is currently an explicit hypothesis of the Donsker
   interface.
2. Formalize the `α=2` specialization of Lemma 4: the norming/inverse-norming
   relations, the slowly diverging diagonal, and the passage from fixed
   normalized blocks to every `IsMogulskiiScale`. The current endpoint-band
   theorem does not yet perform this scale transfer.
3. Prove the sharp horizontal upper rate by applying the discrete
   oscillation-block comparison and the fixed-scale path limit, then passing
   to the same arbitrary subdiffusive scales. The existing endpoint CLT
   bound is not enough for the sharp constant.
4. Combine the horizontal upper and lower rates with the already separated
   finite-partition corridor argument, checking the open/closed Portmanteau
   directions and endpoint margins.

Do not use a forced run of same-sign increments to enter the core: a cost
`exp(-C aₙ)` is negligible on the target scale only under the extra condition
`aₙ³/n → 0`, which is not among the theorem's assumptions.
