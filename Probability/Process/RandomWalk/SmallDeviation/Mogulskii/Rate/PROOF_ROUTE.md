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
theorem coefficient and `Hα` is the paper's path-set functional. To keep the
normalization unambiguous, write `C₀ < 0` for the Lemma 1(I) escape constant
of the base corridor `a I₋₁¹`; since `Hα(I₋₁¹) = 2⁻α`, the coefficient in
Theorems 1 and 2 is `C = 2^α C₀`. Lean's positive rate coefficient is
`κ = -C = -2^α C₀`. Both general-α results precede computing the coefficient
for `α=2`.

The formalization order follows the source's sections and proof dependencies.
The active target is the theorem for every stable index `0 < α ≤ 2`; the
current Gaussian/Donsker files are not used to prove it. Stable-process Lemma 2,
relations (21)--(25), and Lemma 1, relations (18)--(20), are already proved.

## Fixed mathematical proof scheme

The target is Mogul'skii's source theorem for the path classes `M₂`, `M₃`,
and `M`, with the paper's strict path-set convention and normalization. The
later continuous-boundary formulation in modern references is a useful
corollary, but it is not a substitute for this theorem or its proof. The proof
will follow the original discrete comparison lemmas and will not assume
convergence of every corridor probability or impose a blanket boundary-null
hypothesis.

The source notation used below is: `I_c^b` is the pinned path event
`f(0)=0`, `inf f > c`, `sup f < b`; `J_a` is the pinned range event
`sup f - inf f < 2a`; `Y_c^b(t)G` additionally restricts the value at time
`t` to `(c,b)`; and `X(s,t)G` imposes `G` on the path restriction to the
closed time interval `[s,t]`. These strict and endpoint conventions are part
of the statements and must be preserved when identifying them with Lean events.

For a fixed small-deviation scale `x(n)`, write
`ρ(n) = n * x(n)^(-α) * L*(x(n)) = n / B*(x(n))`. The block transfer is:

1. Fix `A > 0` and use block length
   `mₙ(A) = ⌊B*(A * x(n))⌋`, where `B*(u) = u^α / L*(u)`. The stable norming
   inverse gives `B(mₙ(A)) / (A * x(n)) → 1`. The stable `J₁` path limit and
   open/closed Portmanteau bounds transfer a block corridor to the corresponding
   stable-process corridor at width `1/A`; lower bounds use an open inner
   corridor, upper bounds a closed outer corridor. A probability-equality
   adapter is used only when its boundary-null premise has actually been
   proved.
2. Lemma 1 gives the fixed-`A` base-corridor rate
   `A^α * C₀` for `A⁻¹ I₋₁¹`. Stable time and space scaling then give rate
   `A^α * C * (tᵢ₊₁ - tᵢ) / (bᵢ - aᵢ)^α` on a constant-boundary segment.
   The endpoint-constrained versions are supplied by source Lemma 4(36)--(37),
   not by asserting a rate for an arbitrary `G` at this point. Choose a
   source-ordered slowly increasing diagonal `A(n) → ∞` so the fixed-parameter
   transfers remain eventual and
   `A(n) * x(n) / B(n) → 0`. The regular-variation inverse gives
   `B*(A(n) * x(n)) / (A(n)^α * B*(x(n))) → 1`. Thus the number of complete
   blocks is asymptotic to `n / B*(A(n) * x(n))`; multiplying the one-block
   logarithmic rate yields `C * Hα(G) * ρ(n)` after finite-partition assembly.
3. Prove and apply every discrete Lemma 3 comparison, with the source's exact
   event conventions: (30) compares shifted unit-width corridors with a
   slightly wider translated corridor; (31) squeezes a range event `J₁`
   between centered corridors; (32) bounds a confined path by independent
   oscillation events on complete equal subblocks; (33) gives the converse
   return-core lower bound using finitely many endpoint bands; and (34)
   compares an endpoint-constrained corridor with a base corridor on the
   logarithmic scale. The proof of (33) uses a finite cover of the return core
   and uniform positive one-block band probabilities, not a deterministic
   choice of endpoint. Equations (30), (31), and (34) are logarithmic
   asymptotic comparisons, so their exact eventual hypotheses must be proved
   before multiplying probabilities or taking logarithms.
4. For `G ∈ M₂`, partition `[0,1]` at the union of the finitely many boundary
   jump times. Set `nᵢ = ⌊n tᵢ₊₁⌋ - ⌊n tᵢ⌋`, so
   `nᵢ / n → tᵢ₊₁ - tᵢ`; the same moving spatial scale is admissible on each
   positive-length segment. The upper bound drops inter-segment endpoint
   constraints and factors the unequal independent increment blocks. The lower
   bound chooses a continuous path strictly inside `G`, uses positive trace
   separation at each partition time to choose a small endpoint core, and
   iterates the segment return kernels. Floor remainders are included in the
   endpoint/terminal-block comparison. Send the path margin and endpoint-core
   widths to zero after taking `n → ∞`. The logarithmic sum is the Riemann sum
   `Σᵢ (tᵢ₊₁ - tᵢ) / (bᵢ - aᵢ)^α = Hα(G)`.
5. Pass from `M₂` to finite unions `M₃` by the finite-union rate lemma, then to
   `M` by the source's inner/outer approximation and energy squeeze. Theorem 2
   uses the same finite partition with stable-process independent increments
   and exact stable scaling; Theorem 1 uses the block transfer above.

The dependency order is therefore: source-stable path law and process escape
rate; fixed-`A` block transfer; source Lemma 3 in both directions; the
Lemma 4 slow diagonal; finite-partition `M₂` estimate; then the `M₃` and `M`
closures. A standalone lemma is a useful next coding step only if it closes one
of these dependencies. The infinite-variance `α = 2` attraction bridge remains
a separate hypothesis-discharge issue; the Rademacher constant calculation is
later still.

1. The source path classes `M₁`, `M₂`, `M₃`, approximation class `M`, and
   finite-union energy are represented under
   `Probability/Process/SmallDeviation/Mogulskii/PathClass/`. The conditional
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
   translated and endpoint-constrained events. The unit-interval
   `CadlagPath` transfer in `EscapeRate/PathLaw.lean` is also proved, by
   comparison with a reference stable Lévy process having the same increment
   specification; it does not construct a full-time process extension from an
   arbitrary unit-interval law.
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
   import boundaries. The remaining domain-of-attraction gap at `α = 2` is
   deriving the truncated second-moment condition and compatible norming from
   infinite-variance Gaussian attraction. The rounded block inverse is proved
   for `0 < α ≤ 2` when slow variation of `L*` and `IsStableNorming` are
   supplied. The source-regime stable random-walk path-law limit and its
   variable-block transfer are proved under zero-center scalar attraction, a
   matching stable path law, and the stated tightness, norming, and
   slow-variation hypotheses. Corridor probability equality still
   needs a null-boundary premise; the one-sided open lower bound used by M2
   does not.
The fixed-parameter upper transfer is now also available in
`Stable/Corridor.lean`: closed range-oscillation probabilities pass through
closed-set Portmanteau and are bounded by a slightly wider stable-process
range tube using the almost-sure zero start. This preserves the range-diameter
normalization and needs no boundary-null premise. The finite
`blockOscillationLTEvent` has been proved to lie in the path-space closed
range-oscillation event, and the resulting one-block bound is combined with
Lemma 3(c)'s independent-block power estimate. The generic stable escape-rate
module now also converts the small-radius limit to the large block-parameter
scale `c⁻ᵅ log P(tube (r / c)) → C / r^α`. The exact rate for a centered
constant-width random-walk tube is now proved from both sides in
`Stable/Rate/Upper.lean` and `Stable/Rate/Lower.lean`. The upper proof uses
closed-set Portmanteau and shrinking outer corridors; the lower proof uses
the source's seven endpoint-return bands, open-set Portmanteau, and the
source block count. Both now require slow variation of `L*` but no upper
bound on its values along the shrinking scale. The lower route also supplies
the eventual positivity and lower coboundedness needed by the upper real-log
argument. This closes the one-segment horizontal case only. Still needed are
the joint slow-diagonal applications for arbitrary fixed-parameter step
corridors and the upper/lower finite-partition assembly for general
boundaries.
5. Then formalize Lemma 3's discrete analogues, including both directions of
   the block inequalities. Preserve Lemma 4's fixed-parameter limits and
   source-ordered slow-growth diagonal (38)--(44), then assemble the general
   random-walk Theorem 1. Only after the general-α theorem should §4's
   Rademacher calculation specialize the constant to `α = 2`.

The inverse-Tauberian implication is complete for `0 < α < 2`: it transfers
the characteristic-function defect to regular variation of the two-sided
increment tail and gives the truncated-moment/defect ratio. For `α = 2`, the
finite-variance branch is formalized in
`Probability/Distributions/Stable/Attraction/Normal.lean`: a centered
probability law with integrable square and positive second moment has
standard-Gaussian attraction and `IsStableNorming` under the canonical
normalization `sqrt (n * secondMoment)`. This does not cover infinite-variance
normal attraction. `Probability/Distributions/Moments/Truncated/RegularVariation.lean`
proves a fixed-positive-rescaling tail estimate from slow variation and the
negligible-tail hypothesis; it does not derive these assumptions from
Gaussian attraction. The `α = 2` block inverse is conditional on slow variation
of `L*` and `IsStableNorming`; it does not derive those hypotheses from
Gaussian attraction.

The stable random-walk `J₁` limit is proved under the three source centering
regimes. Its path-law identification uses Mathlib's tight-family compactness,
probability-measure almost-everywhere continuous mapping, and projective-limit
uniqueness, with a repository-specific Fubini argument to choose dense
continuity times for each weak cluster law. Fubini is an auxiliary step in
this path-space identification, not a step attributed to Mogul'skii's paper.
The arbitrary-center finite-dimensional theorem keeps the block-center ratio
explicit; the source wrappers use zero scalar centering, so that ratio vanishes.
The variable-block path-law limit follows by a deterministic-parameter
product with a Dirac law and continuous mapping, then the rounded norming
inverse. M2's open-event lower transfer needs no boundary-nullity, while the
equality adapter for a fixed corridor event does. The discrete Lemma 3/4
applications, the positive limiting endpoint-band inputs, the stable-process
`M₂` rate inputs, and final Theorem 1/2 assembly remain open.

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
self-similar tube-probability bridge are also present. The tail implication
from the characteristic defect is complete for `0 < α < 2`; the `α = 2`
infinite-variance normal-attraction bridge, exact stable-process `M₂` rate
inputs, the remaining discrete Lemma 3/4 applications, and assembly of
Theorems 1 and 2 remain open.

One conditional general-α discrete upper subcase is now proved in
`Stable/Discrete/UpperEndpoint.lean`: stable norming and slow variation give
the endpoint limit at the rounded stable block length, and an explicit strict
bound on the limiting mass of `[-1,1]` yields a uniform killed-block row
bound. Iteration gives `P(horizontal tube through n) ≤ q^(n / mₙ)`, where
`mₙ = ⌊constant · κν(aₙ)⌋₊`. This is an endpoint-based, non-sharp upper
estimate; it does not control excursions between block endpoints or supply
the stable one-block corridor estimate. The strict endpoint-mass inequality is now derived from
strict stability for
`0 < α < 2`, and from the source condition `0 < F(0) < 1` when `α = 2`, by
`Stable/Discrete/UpperEndpointSource.lean`. The centering limit and block-center
ratio remain explicit inputs.

A conditional stable-block endpoint-return lower estimate is now proved in
`Stable/Discrete/EndpointReturn.lean`. Seven explicit one-block endpoint-band
lower bounds under the normalized increment law imply a horizontal-tube lower
bound through any horizon covered by complete stable-length blocks. A second
theorem chooses the source count `horizon / blockLength + 1`, including one
extra block for the final incomplete segment. This formalizes the discrete
return-core gluing step of Lemma 3(d)/(33) at the stable block scale.
`Stable/Discrete/EndpointBandTransfer.lean` derives eventual lower bounds from a variable-length
path-law limit and positive mass of the limiting open endpoint corridors.
`Stable/Discrete/SourceLower.lean` now supplies those masses from the stable-process entrance
estimate and connects the block path-law limit to a zero-centered stable domain-of-attraction
limit, stable norming, and the rounded inverse at block parameter one. Its three source-regime
corollaries derive the base-law tightness for `0 < α < 1`, for `α = 1` under sine-centering, and
for `1 < α < 2` under integrable centering. This one-sided estimate uses open-set Portmanteau
and requires neither boundary-nullity nor separately assumed endpoint-band positivity. The
The strict source path-class comparison (32) is proved in `Discrete/Horizontal.lean`: an open
horizontal corridor forces strict range control on every complete IID block, and the event
probabilities factor by the generic consecutive-block result in `Path/Block/Law.lean`, using
Mathlib's `iIndepFun` and `Measure.pi` APIs. `MeasureTheory/Measure/FiniteCover.lean` and
`Path/Block/Corridor/Comparison.lean` now prove the
generic finite-cover estimate `q · P(U) ≤ |F| · P(T)` from prefix-cell coverage, independent
next-block events of mass at least `q`, and a pathwise gluing inclusion. The generic lemma in
`Analysis/Asymptotics/NegativeRatio.lean` converts the resulting finite multiplicative comparison
into the logarithmic-ratio lower bound when both probabilities are eventually positive and the
target probability tends to zero. The source-specific layer now supplies the missing pieces:
`BridgeComparison/SourceGeometry.lean` identifies the prefix/bridge cells and proves their
gluing inclusion; `BridgeComparison.lean` transfers positive entrance mass to a uniform finite
family of open bridge events; `BridgeComparison/CdfEntrance.lean` discharges the entrance input
for every stable index using the CDF condition; and `BridgeComparison/SourceDecay.lean` proves
base positivity, endpoint decay, and equation (34) under the stable-domain and slow-variation
hypotheses. The remaining Lemma 3 gap is the use of these fixed-relative-time comparisons in
the upper and lower finite-partition corridor estimates, including their floor remainders and
endpoint cores.

## Remaining obligations before claiming the general stable theorem

1. Complete the infinite-variance normal-attraction case `α = 2`. The
   finite-variance theorem in
   `Probability/Distributions/Stable/Attraction/Normal.lean` shows that
   centered laws with integrable square and positive second moment have
   Gaussian attraction and the canonical `sqrt (n * secondMoment)` norming.
   The floor-block inverse is already proved for `0 < α ≤ 2` under
   slow variation of `L*` and `IsStableNorming`; the open step is deriving the
   needed truncated-second-moment behavior and norming from infinite-variance
   Gaussian attraction. The source-regime stable random-walk path-law theorem and
   variable-block transfer are available under their stated hypotheses. The
   inverse-Tauberian implication for `0 < α < 2` is complete above.
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
3. Complete Lemma 3's discrete probability comparisons and Lemma 4's
   application of the fixed-parameter limits to the source norming scale; then
   prove Theorem 1 for the stated domain-of-attraction hypotheses. The
   `Stable/Discrete/UpperEndpointSource.lean` derives the strict endpoint-mass
   input from strict stability for `0 < α < 2`, or from `0 < F(0) < 1` when
   `α = 2`; `Stable/Discrete/UpperEndpoint.lean` still gives only a conditional,
   non-sharp horizontal upper block bound. `Stable/Discrete/EndpointReturn.lean` proves return-core
   iteration at stable block lengths, conditional on explicit lower bounds
   for the seven one-block endpoint bands, including the source count
   `horizon / blockLength + 1`. `Stable/Discrete/EndpointBandTransfer.lean`
   derives those eventual lower bounds from a variable-block path-law limit
   and strict positive mass of the limiting open endpoint corridors. The
   variable-block limit is available under the explicit F0 and scale
   hypotheses in `Stable/Corridor.lean`; the seven positive-mass inputs, the
   source's path-class and logarithmic comparisons, remaining stable one-block
   corridor probabilities, and the fixed-relative-time partition application
   remain open. `Order/Filter/SlowDiagonal.lean` supplies the generic
   order/filter selector, `Analysis/Asymptotics/SlowDiagonal.lean` adds its
   real-valued vanishing-product estimate, and
   `Analysis/Asymptotics/RegularVariation/SlowScale.lean` transfers the
   fixed-multiplier regular-variation limit to a slowly diverging multiplier;
   `Stable/Scale.lean` instantiates this to prove the source conditions
   `a(n) x(n) / B(n) → 0` and `B*(a(n)x(n)) / (a(n)^α B*(x(n))) → 1`, assuming
   slow variation of `L*`. The fixed-parameter probability limits and their
   Lemma 4 application remain open. The normalized-step endpoint
   Portmanteau transfer in
   `FunctionalLimit/NormalizedStep/Endpoint.lean` is already proved conditional
   on the path-law limit; F0 and `PathLimit/Block.lean` supply that limit under
   their explicit hypotheses.
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
