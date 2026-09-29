# Mogulskii α = 2: corrected proof route

This note is the proof plan and status ledger for the horizontal small-deviation
rate and its later extension to piecewise corridors. It follows the proof
architecture in Mogul'skii's 1974 paper ([original article record and full
text](https://www.mathnet.ru/eng/tvp3978)), specialized to centered
variance-one increments. A compiled component does not imply that the
horizontal rate or the full theorem has been completed.

## Target and normalization

Let `S₀ = 0` and let the increments be IID, centered, and of variance one. For
`aₙ → ∞` with `aₙ / √n → 0`, define the horizontal tube to have total width
`aₙ` (half-width `aₙ / 2`). The target is

```text
(aₙ² / n) * log P(∀ k ≤ n, |Sₖ| ≤ aₙ / 2)  →  -π² / 2.
```

The constant is for total width `aₙ`: Brownian survival in an interval of
width `w` has principal exponent `-π²/(2 w²)`. For the interval `(-r,r)`,
whose width is `2r`, this is `-π²/(8r²)`.

## Source proof and the α = 2 specialization

The source's dependency order is:

1. Lemma 1 establishes the horizontal stable-process small-deviation rate.
   Lemma 2 supplies the finite-shift covering and comparison inequalities
   used in that proof.
2. Lemma 3 transfers those comparisons to the discrete walk. Its part (c),
   equation (32), is the upper block-oscillation comparison; part (d),
   equation (33), is the lower return-core comparison using finitely many
   endpoint bands. Lemma 4 transfers fixed-scale process estimates to the
   moving small-deviation scale.
3. Section 4 computes the horizontal constant for `α = 2` from the explicit
   symmetric `±1` walk formula. In Lean, the interval-killed transition matrix
   and its full spectral sum provide the corresponding finite-walk estimate.
4. Theorem 1 then passes from horizontal intervals to the stated finite
   piecewise corridors by partitioning at their finitely many boundary
   discontinuities and applying the horizontal estimates on each block.

For the present finite-variance specialization, Donsker's theorem replaces
Mogul'skii's general stable-domain diagonal in Lemma 4: for each fixed block
constant `C`, use `mₙ = ⌊C aₙ²⌋`, first take `n → ∞`, and only then take
`C → ∞`. This is not the invalid forced-entry argument and does not require
`aₙ³/n → 0`.

## Corrected horizontal upper proof

This is the route currently being formalized.

1. **Mogul'skii Lemma 3(c): reduce to block oscillation.** A path confined to
   a tube of total width `aₙ` has range at most `aₙ` on each complete block.
   For fixed `C > 0`, take `mₙ = ⌊C aₙ²⌋`. IID disjoint blocks give

   ```text
   P(tube through n) ≤ pₙ(C) ^ ⌊n/mₙ⌋,
   pₙ(C) = P(range of the first mₙ increments ≤ aₙ).
   ```

2. **Donsker at fixed `C`.** Since `mₙ → ∞`, the normalized polygonal path on
   one block converges to Brownian motion. The block oscillation event is
   closed. Its normalized width tends to `1/√C`, so for each fixed relative
   slack `η > 0`, eventual inclusion in the closed event of width
   `(1 + η)/√C` and Portmanteau bound `limsup pₙ(C)` by that Brownian range
   mass. The Lean bridge proves directly that the range of the polygonal
   interpolation is attained at grid vertices; no factor-two enlargement is
   introduced here.

3. **Brownian range upper bound by a fixed finite cover.** On the event
   `range(B) ≤ w`, Brownian motion starts at zero and its minimum lies in
   `[-w,0]`. For a fixed integer `K`, cover that interval by `K` pieces and
   enlarge each to an open corridor of width `(1 + 3/K)w`. This cover is
   fixed before taking the Donsker limit. For each corridor, open-set
   Portmanteau bounds its Brownian mass by the `liminf` of the normalized
   Rademacher corridor probabilities. Translate each discrete corridor to a
   finite Dirichlet interval and use the complete-spectrum geometric bound

   ```text
   4 q_N^N / (1 - q_N^N),   q_N = cos(π/(D_N + 1)).
   ```

   Summing over the `K` corridors gives, for small `w`, a bound of the form

   ```text
   K · 8 · exp(-π² / (2 ((1 + 3/K)w)²)).
   ```

4. **Take limits in this order.** First take the Donsker index `n → ∞` with
   `K`, `η`, and `C` fixed. For the outer rate, fix `K` and a relative Donsker
   slack `η > 0`. The one-block probability is eventually at most
   `2K·8·exp(-π² C /(2(1 + 3/K)²(1 + η)²))`. The number of complete blocks
   satisfies `(aₙ²/n)⌊n/mₙ⌋ → 1/C`. Thus, for fixed `K, η, C`, the normalized
   logarithmic limsup is bounded by the block exponent divided by `C`.
   Let `C → ∞` to remove the fixed prefactor `16K`; then let `η ↓ 0` and
   `K → ∞`. This yields `-π²/2`. Equivalently, for an epsilon proof, choose
   `K` and `η` first, then one sufficiently large fixed `C`, and finally
   apply the fixed-parameter `n → ∞` theorem.

The route does **not** union-bound over all possible discrete minima. Such a
union has a number of terms growing like the interval width and cannot be
absorbed in the fixed-width Donsker limit. It also does not use an endpoint
sine row bound with a width-dependent prefactor.

## Corrected horizontal lower proof

This follows Mogul'skii Lemma 3(d), not a forced run of increments.

1. Fix `C > 0` and a block length asymptotic to `C aₙ²`. Use a return core and
   the seven finite endpoint bands (the source's shifts `i = -3,…,3`) so a
   block can be iterated from every starting point in the core. This is the
   return-kernel implementation of equation (33).
2. For each fixed `C`, prove positive Brownian mass for each of the seven
   open corridor/endpoint-band events. Donsker's open-set Portmanteau
   inequality gives a lower bound for the discrete one-block return
   probabilities; independence / the return kernel iterates that bound.
3. For the sharp `C → ∞` rate, lower-bound each Brownian band mass using a
   strictly smaller closed corridor and a closed endpoint band. Transfer a
   finite-interval Rademacher spectral target-mass estimate through the
   closed-set Portmanteau inequality. The corridor radius is asymptotic to
   `1/(2√C)`; the endpoint-band width is a vanishing fraction of that radius,
   with its logarithmic cost `o(C)`. For example, relative width `C^(-1/8)`
   has logarithmic cost `O(log C) = o(C)`. The resulting per-block
   logarithmic rate divided by `C` tends to `-π²/2`.
4. Apply the scale-transfer theorem at each fixed `C`, then take `C → ∞`.
   This lower bound supplies eventual positivity and lower coboundedness for
   the real logarithmic sequence used by the upper-rate limsup comparison.

The lower route still needs the explicit finite target construction and its
uniform ground-state/density estimates. A survival-only estimate or mere
positivity of the seven band events does not give the sharp constant.

## From horizontal intervals to corridors

After both horizontal rates are proved, apply them to each interval of a
finite partition of the corridor boundary. For the upper bound use enclosing
horizontal intervals; for the lower bound use strictly shrunken corridors
and endpoint margins, then apply the finite-shift return estimate. Finally
refine the partition as in the source's proof of Theorem 1. The open/closed
Portmanteau directions and all endpoint margins must be explicit.

## Lean components already checked

- `Discrete/Horizontal.lean`: the upper block comparison from block
  oscillation and independence, plus the abstract return-kernel iteration.
- `Discrete/EndpointBands.lean`: endpoint-band measurability, the seven-shift
  cover of the return core, corridor containment, and core-to-core return
  estimate.
- `Discrete/DonskerEndpointBands.lean` and `Rate/EndpointBands.lean`: fixed
  open Brownian endpoint-band lower bounds transfer to moving blocks and
  scales, conditional on the actual Brownian band-mass estimates.
- `Spectral/Range/Rate.lean`: the fixed finite cover of Brownian minima, the
  full-spectrum geometric corridor bound, and the sharp small-width Brownian
  range upper exponent, with the cover count kept fixed first.
- `Spectral/Range/BlockDonsker.lean`: polygonal interpolation preserves the
  block range exactly; closed-set Portmanteau transfers the oscillation
  probability to Brownian range mass.
- `Spectral/Range/BlockBound.lean`: for fixed cover count, enlargement, and
  block constant, the one-block oscillation probability is eventually
  bounded by the explicit finite-cover spectral bound; independent blocks
  give the horizontal tube power bound.
- `Spectral/Range/LogRate.lean`: transfers that power bound to the normalized
  logarithmic limsup for fixed parameters. It explicitly assumes eventual
  positivity and lower coboundedness; the lower proof must discharge them.
- `Spectral/Range/Parameters.lean`: proves the exact affine logarithmic
  parameter formula and selects a finite cover, positive Donsker slack, and a
  sufficiently large block constant in the required order.
- `Spectral/Range/SharpUpper.lean`: combines the preceding results into the
  sharp upper limsup `≤ -π²/2`, conditional only on eventual tube positivity
  and lower coboundedness of the normalized logarithms.

## Remaining obligations before claiming the horizontal theorem

1. Finish the lower endpoint-band spectral target construction and prove its
   uniform ground-state and density bounds. Use it to establish the sharp
   lower rate and discharge the two explicit hypotheses of
   `SharpUpper.lean` (eventual positivity and lower coboundedness).
2. Assemble the horizontal liminf and limsup into the actual limit theorem.
3. Only then compose with the finite-partition corridor approximation to get
   the full `α = 2` Mogul'skii theorem.

## Explicitly rejected route

Do not force `O(aₙ)` consecutive increments of one sign to enter the core.
Its probability cost is `exp(-c aₙ)`, whose normalized logarithm is of order
`-aₙ³/n`; the theorem assumes only `aₙ → ∞` and `aₙ/√n → 0`, which do not
imply `aₙ³/n → 0`. The return-core endpoint bands replace that invalid step.
