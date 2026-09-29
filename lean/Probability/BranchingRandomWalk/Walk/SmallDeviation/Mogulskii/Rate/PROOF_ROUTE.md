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
   (33) is the lower comparison. For block ratio `θ = m/n`, it uses
   `k = ⌊θ⁻¹⌋ + 1` blocks and the minimum over the seven endpoint bands
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
   implementation: for each fixed `C > 0`, take `mₙ = ⌊C aₙ²⌋`. Since
   `aₙ → ∞`, `mₙ → ∞`, so Donsker transfers the fixed Brownian endpoint-band
   events along this sequence; since `aₙ²/n → 0`, the number of blocks
   satisfies `(⌊n/mₙ⌋+1) aₙ²/n → 1/C`; equivalently the source's block
   ratio `θₙ = mₙ/n` tends to zero. First take `n → ∞` with `C` fixed,
   then let `C → ∞`. The Brownian endpoint-band input below has its own
   auxiliary diffusive limit, used to transfer the finite Rademacher spectral
   estimates to Brownian closed events. Thus this is a finite-variance
   specialization of the source's variable-block/diagonal step, not a claim
   that the general Lemma 4 diagonal has been formalized.
4. **Sharp lower constant.** The preceding fixed-`C` bound is only useful
   for the sharp rate after proving a Brownian lower estimate for every one
   of the seven endpoint-band events. Keep the starting point at the center;
   no spatial translation or entrance estimate is needed. For each
   `i ∈ {-3,…,3}`, the spectral target is a narrower closed band
   `[(i - 1/2) ε, (i + 1/2) ε]`, strictly inside the block event's open band
   `((i - 1) ε, (i + 1) ε)`. Restrict paths to a closed centered interval of
   radius `R`, strictly smaller than the open block radius `ρ`. Thus the
   spectral event is a subset of the desired open endpoint-band event, with
   strict slack at both the path boundary and endpoint boundary. Choose
   `R(C), ρ(C), ε(C) > 0` with
   `R(C) < ρ(C)` and `7 ε(C) < R(C)`,
   `2 (ρ(C) + 4 ε(C)) √C < 1`,
   `R(C) √C → 1/2`, and `ε(C) / R(C) → 0`; for large `C`, every target
   band lies well inside the spectral interval, where the sine ground state
   is uniformly bounded below. For each fixed `C`, the target contains a
   positive proportion of parity-compatible lattice sites, bounded below by
   a constant of order `ε(C) / R(C)`. The finite
   spectral estimate has principal factor
   `cos(π / (2 R(C) √N + o(√N)))^N`, whose logarithm tends to
   `-π² / (8 R(C)^2)` for a unit-time Brownian block. Thus its logarithm,
   divided by `C`, tends to `-π²/2` as `C → ∞`; the target-density
   prefactor is negligible when, for example, `ε(C) / R(C)` is a reciprocal
   power of `C`. These parameter requirements are compatible: for
   `t = C^(-1/8)`, one may take
   `R = (1 - 10t) / (2√C)`, `ε = t R`, and `ρ = R + ε` for all sufficiently
   large `C`. Then
   `2 (ρ + 4 ε) √C = (1 - 10t)(1 + 5t) < 1`,
   `7 ε < R`, `R√C → 1/2`, and `log(ε/R) / C → 0`.

   For each fixed `C` and each of the seven targets, let the Rademacher
   interval radius tend to infinity with its diffusive width tending to `R`.
   The proof bridge must be explicit: identify the killed matrix target mass
   with the IID Rademacher event “all partial sums lie in the closed lattice
   interval and the final site lies in the chosen band”; center the lattice
   interval and scale that path event; place it inside the fixed closed
   Brownian corridor/endpoint event; apply the closed-event Portmanteau
   inequality in its `limsup ≤ Brownian closed mass` direction; then use the
   strict inclusions above to bound the desired open band mass from below.
   The target finset and its density/ground-state bounds are still missing.
   A survival-only Brownian estimate does not prove these seven separate
   endpoint bounds.
5. **Sharp upper constant (Lemma 1 and Lemma 3(c)).** The upper block
   comparison is driven by the *range* of one increment block, not by its
   endpoint alone. With block length `mₙ = ⌊C aₙ²⌋`, confinement to a tube
   of width `aₙ` forces each complete block to have range at most `aₙ`.
   After diffusive normalization, the threshold tends to `w = 1/√C`.
   For every fixed slack `δ > 0`, the eventual block event is contained in
   `range ≤ w+δ`; Donsker and the closed-set Portmanteau inequality bound its
   `limsup` by the Brownian probability of that closed range event.

   The required Brownian small-range *upper* estimate must itself be proved;
   the closed-corridor lower estimate is not enough. Follow Mogulskii's
   α=2 Lemma 1 calculation through the exact symmetric-walk spectrum. For a
   Rademacher path of `N` steps, if its range is less than `W √N`, its minimum
   is one of `-N,…,0`, and the path is contained in the corresponding integer
   interval of span `D_N = ⌈W √N⌉`. Union over these `N+1` possible minima and
   apply the existing uniform row-sum upper bound for an interval with
   `D_N+1` sites:
   `cos(π/(D_N+2))^N / sin(π/(D_N+2))`. The polynomial union factor and sine
   prefactor vanish after division by `N`; the eigenvalue term gives
   `-π²/(2 W²)`. To transfer this *upper* bound to Brownian motion, use the
   open range event: `Brownian range < W` has probability at most the `liminf`
   of the approximating Rademacher probabilities. Bound a closed Brownian
   range event `range ≤ w` by applying the open estimate at `W>w` and then
   letting `W ↓ w`. Consequently the block `limsup` is at most
   `exp(-π²/(2(w+δ)^2))`; let `δ ↓ 0` for each fixed `C`, and only then send
   `C → ∞`.
   This is the opposite Portmanteau direction from the lower endpoint-band
   argument in step 4.

   Now let `C → ∞`: the block exponent is asymptotic to
   `-π² C/2`, while the number of blocks times `aₙ²/n` tends to `1/C`.
   Their product gives the sharp upper rate `-π²/2`. This range estimate and
   its Portmanteau transfer are still unformalized; `Rate/Upper.lean` currently
   proves only the non-sharp endpoint-CLT bound.
6. **General corridors (§3).** Once the horizontal rate is established,
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
  `⌊C aₙ²⌋` and proves the logarithmic liminf bound for every
  `IsMogulskiiScale`. It is a genuine scale-transfer theorem, but remains
  conditional on the Brownian band masses and is not yet the sharp lower
  Mogulskii rate.
- `Rate/Upper.lean` gives an endpoint-CLT upper bound. It is non-sharp and
  does not establish the upper half of the Mogulskii rate.
- `Spectral/` proves the symmetric nearest-neighbor interval calculation and
  a generic target-mass lower bound. The remaining task is the explicit
  finite-target construction, its path-event/Portmanteau connection, and the
  seven fixed-scale Brownian endpoint-band estimates used by Lemma 4.
- `Spectral/Target/Path.lean` proves that a killed interval kernel's mass on
  any finite target equals the IID Rademacher probability of staying in the
  lattice interval and ending in that target. Its matrix-power sum version
  also identifies the exact spectral quantity used by `Target/LowerBound.lean`.
- `Spectral/SurvivalBounds.lean` already gives a uniform row-sum upper bound
  `cos(π/(D+2))^N / sin(π/(D+2))` for survival in a finite interval with
  `D+1` sites. The range-event upper route needs to turn it into a bound on
  the union over the possible integer minima.

## Remaining proof obligations

1. Construct, for each of the seven endpoint bands, parity-compatible
   lattice target finsets and prove their asymptotic density and uniform
   ground-state lower bounds. Embed their Rademacher path events in the
   fixed closed Brownian corridor/endpoint events and use the existing
   closed-event Portmanteau theorem. Then prove the common small-radius
   exponent with parameters satisfying the corridor-fit inequality. Mere
   positivity is not enough for the sharp constant.
2. Use those bounds in `Rate/EndpointBands.lean`, then take `C → ∞` and
   remove the small corridor slack to obtain the sharp horizontal lower rate.
3. Formalize the sharp Brownian range upper estimate described in step 5:
   the finite union over possible Rademacher minima, the spectral row-sum
   bound, and the open-set Portmanteau transfer. Then use Donsker's closed-set
   bound on general IID block oscillations, Lemma 3(c), and the fixed-`C`
   scale transfer to prove the sharp horizontal upper rate. The existing
   endpoint-CLT bound is not enough for the sharp constant.
4. Combine the horizontal upper and lower rates with the already separated
   finite-partition corridor argument, checking the open/closed Portmanteau
   directions and endpoint margins.

Do not use a forced run of same-sign increments to enter the core: a cost
`exp(-C aₙ)` is negligible on the target scale only under the extra condition
`aₙ³/n → 0`, which is not among the theorem's assumptions.
