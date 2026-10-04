# Mogulskii stable theorem: source-ordered proof route

This note is the proof plan and status ledger for the general stable-domain
Mogul'skii theorem. It follows the dependency order in the 1974 paper
([original article record and full text](https://www.mathnet.ru/eng/tvp3978)).
The Gaussian/`α = 2` calculation in the paper's §4 comes only after the
general stable-process and random-walk theorems; it is a later specialization,
not the active first proof target. A compiled component does not imply that
either theorem has been completed.

## Active target: the general stable theorem first

Let `Fα` be a strictly `α`-stable law with `0 < Fα(0) < 1`, and let the
increment law lie in its domain of attraction with norming `B(n)`. The paper
uses

```text
L*(u) = u^(α - 2) ∫_{[-u,u]} x² ν(dx),
B*(u) = u^α / L*(u),
B*(B(n)) / n → 1,
```

and a small-deviation scale `x(n) → ∞` with `x(n) / B(n) → 0`. The main
target is the random-walk Theorem 1,
`log P(sₙ(·) ∈ G) ~ C Hα(G) n x(n)⁻α L*(x(n))`. Its companion process
Theorem 2 states `log P(x⁻¹ ξ(·) ∈ G) ~ C Hα(G) x⁻α`. Here `C < 0` is the
stable-process escape constant from Lemma 1(I), and `Hα` is the paper's
path-set functional. Both general-α results precede computing `C` for `α=2`.

The formalization order follows the source's sections and proof dependencies.
The active target is the theorem for every stable index `0 < α ≤ 2`; the
current Gaussian/Donsker files are not used to prove it. Stable-process Lemma 2,
relations (21)--(25), and Lemma 1, relations (18)--(20), are already proved.

1. The source path classes `M₁`, `M₂`, `M₃`, approximation class `M`, and
   finite-union energy are represented under
   `Probability/RandomWalk/SmallDeviation/Mogulskii/PathClass/`. The conditional
   `M₃` rate-to-`M` assembly is now formalized in `PathClass/Rate/`: component
   rates imply the finite-union rate, order the inner and outer energies, give
   a common energy limit, and make that value independent of the approximation
   witness. Theorem 2 is assembled for `IsM`, still conditional on the `M₃`
   rates and measurability of the target event. Those hypotheses have not yet
   been discharged from the stable-process assumptions.
2. Lemma 2 estimates (21)--(25) are proved in the public stable-process
   entries `Stable/SmallDeviation/{ShiftedCorridor,RangeComparison,
   BlockBounds,EndpointComparison}.lean`. The statements preserve the source's
   strict and half-open event conventions.
3. Lemma 1 (18)--(20) is proved in `Stable/SmallDeviation/EscapeRate.lean`
   and its `EscapeRate/{Corridor,Endpoint,Law}` modules. It establishes a
   finite strictly negative escape rate and transfers the same rate to the
   translated and endpoint-constrained events. The separate statement-layer
   bridge to the `CadlagPath` packaging remains open.
4. Complete the domain-of-attraction foundation before the discrete Lemma 3/4
   argument. General attraction definitions and finite-sum characteristic-
   function formulas are owned by `Probability.Distributions.DomainOfAttraction`;
   the stable specialization proves (6)--(7) with one coefficient shared by
   all frequencies. The norming-ratio implication (E), compact-frequency
   uniform convergence (I), and continuous small-frequency regular variation
   (J) are now proved in `Stable/Attraction/NormingRatios/`; the norming-sequence
   proofs do not assume monotonicity. **The inverse Tauberian chain for
   `0 < α < 2` is now proved.** The exact inverse cosine-kernel identity is in
   `Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail`;
   squared-modulus defect is identified with the cosine defect of the
   symmetrized increment law. Analysis-owned modules provide the nonmonotone
   Potter envelope, the common Mellin-kernel DCT, the positive and exactly
   normalized signed Mellin moment, and the second-tail Karamata ratio. These
   yield the second-tail/defect limit, regular variation of the symmetrized
   tail, transfer to the original two-sided tail, and the exact truncated
   second-moment/defect ratio. The Mellin integrability proof calls Mathlib's
   general Mellin convergence theorem rather than reproving it. The analysis
   kernel and Mellin-DCT layer is owned by `Analysis.Fourier.CosineTauberian`;
   the probability-facing second-tail identity imports that layer directly,
   while the defect and symmetrized-tail bridge does not import Fourier
   inversion. CI now compiles point-mass and general-attraction API examples,
   checks the `α = 1` Mellin case, audits the full inverse-Tauberian chain's
   dependencies against the standard axiom allowlist, and enforces those
   import boundaries. The remaining
   domain-of-attraction work is the separate `α = 2` normal-attraction branch,
   compatible truncated-moment norming and its asymptotic inverse, and the
   functional limit needed for fixed block events. The reusable Gaussian
   smoothing identity alone does not replace the `α = 2` argument.
5. Then formalize Lemma 3's discrete analogues, including both directions of
   the block inequalities. Preserve Lemma 4's fixed-parameter limits and
   source-ordered slow-growth diagonal (38)--(44), then assemble the general
   random-walk Theorem 1. Only after the general-α theorem should §4's
   Rademacher calculation specialize the constant to `α = 2`.

The inverse Tauberian necessary direction is complete for `0 < α < 2`: the
kernel-integral limit, nonmonotone Potter control, tail transfer from the
symmetrized law, and truncated-moment ratio are proved. This still does not
close the general stable-domain random-walk theorem. The separate `α = 2`
normal-attraction branch, compatible norming, asymptotic inverse, functional
limit, discrete Lemma 3/4, path-class energy well-definedness, and final
Theorem 1/2 assembly remain open.

## Later specialization: the horizontal `α = 2` target

Let `S₀ = 0` and let the increments be IID, centered, and of variance one. For
`aₙ → ∞` with `aₙ / √n → 0`, define the horizontal tube to have total width
`aₙ` (half-width `aₙ / 2`). The target is

```text
(aₙ² / n) * log P(∀ k ≤ n, |Sₖ| ≤ aₙ / 2)  →  -π² / 2.
```

The constant is for total width `aₙ`: Brownian survival in an interval of
width `w` has principal exponent `-π²/(2 w²)`. For the interval `(-r,r)`,
whose width is `2r`, this is `-π²/(8r²)`.

## Source proof dependency check

The source's dependency order is:

1. Lemma 1 establishes the stable-process small-deviation rate and its
   translated/endpoint comparisons; Lemma 2 proves the finite-shift
   inequalities used there.
2. These process estimates yield Theorem 2. Lemma 3 proves the corresponding
   discrete comparisons, and Lemma 4 transfers the fixed-scale estimates to
   the moving small-deviation scale; together they yield the general
   domain-of-attraction Theorem 1 for the path classes defined in §1.
3. Only after those general results, §4 computes the constant for `α = 2`
   from the explicit symmetric `±1` walk formula (Theorem 3). The finite
   interval kernel and spectral development belongs at this later stage.

The finite-variance Donsker route below is a later specialization/alternate
component. It does not replace the general stable-process Lemma 1, the
discrete Lemma 3, or Lemma 4 in the current proof order.

## Deferred `α = 2` horizontal upper component

This component remains useful after the general stable theorem is established,
but it is not the current first proof target.

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

## Deferred `α = 2` horizontal lower component

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

## Later `α = 2` application to piecewise corridors

Once the general Theorem 1 has been formalized and the `α = 2` constant has
been computed, this is the route for its concrete piecewise-corridor
specialization. It must not be mistaken for the proof of the general Theorem
1 itself. Apply the horizontal rate on each interval of a finite partition;
for the upper bound use enclosing horizontal intervals, and for the lower
bound use strictly shrunken corridors and endpoint margins. The open/closed
Portmanteau directions and all endpoint margins must be explicit.

## Existing Lean components and their actual status

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
- `Spectral/Range/SharpUpper.lean`: combines the preceding α=2 components into the
  sharp upper limsup `≤ -π²/2`, conditional only on eventual tube positivity
  and lower coboundedness of the normalized logarithms.

These α=2 components are not evidence that the general stable theorem has
been formalized. The general stable-process Lemma 1 and Lemma 2, including
relations (18)--(25), are complete. The rational-time event and exact
self-similar tube-probability bridge are also present. The domain-of-attraction
tail implication, path-set functional, discrete Lemma 3/4, and assembly of
Theorems 1 and 2 remain open.

## Remaining obligations before claiming the general stable theorem

1. Handle the normal-attraction case `α = 2` separately. Establish the
   compatible truncated-moment norming, asymptotic inverse, and functional
   limit needed for fixed block events. The inverse-Tauberian implication for
   `0 < α < 2` is complete above.
2. Prove the stable-process rate and measurability for the exact `M₂` corridor
   event. Preserve the source's pointwise strict inequalities: the existing
   `Skorokhod.rangeInOpenInterval` is the uniformly interior event and is not
   a replacement for a finite-step `M₂` corridor. Then apply the conditional
   finite-union and approximation results in `PathClass/Rate/` to discharge
   the hypotheses of Theorem 2. The energy limit and its witness-independence
   are already proved conditional on those component rates; the remaining
   gap is their derivation for the actual stable process, including exact
   event measurability. `tendsto_log_probability_ratio_of_IsM_of_M2Rates`
   now exposes the full conditional chain from single `M₂` corridor rates
   through finite `M₃` unions and class `M`.
3. Prove Lemma 3's discrete comparisons and Lemma 4's norming-scale transfer;
   then prove Theorem 1 for the stated domain-of-attraction hypotheses.
4. Calculate the escape constant in the `α = 2` case by the source's explicit
   symmetric-walk formula, connect it to the finite-interval spectral API,
   and derive the Gaussian small-deviation specialization.
5. Complete the separate α=2 horizontal liminf/limsup assembly and the
   finite-partition corridor theorem if those stronger forms are still needed.

## Explicitly rejected route

Do not force `O(aₙ)` consecutive increments of one sign to enter the core.
Its probability cost is `exp(-c aₙ)`, whose normalized logarithm is of order
`-aₙ³/n`; the theorem assumes only `aₙ → ∞` and `aₙ/√n → 0`, which do not
imply `aₙ³/n → 0`. The return-core endpoint bands replace that invalid step.
