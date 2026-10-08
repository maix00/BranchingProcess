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

The proof follows the source's sections and dependency order. The stable
process theorem and the random-walk theorem for `0 < α < 2` are now assembled
under the source regimes recorded below. The normal-attraction endpoint now
has the truncated-moment norming and infinite-variance `J₁` tightness proof;
the normal-domain functional limit is assembled whenever its standard Brownian
path law is supplied. The remaining `α = 2` bridge is constructing that
measurable path law from Mathlib's almost-surely continuous Brownian predicate
without strengthening its hypotheses. Stable-process Lemma 2, relations
(21)--(25), and Lemma 1, relations (18)--(20), are formalized.

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
   positive-length segment. The process upper bound uses the range event on
   each open cell, which removes the random starting position: values in a
   corridor of width `wᵢ` have pairwise differences at most `wᵢ`. The endpoint
   belongs to the cell on its right; at each fixed partition time the stable
   process has no jump almost surely, so the left-cell range has diameter at
   most `wᵢ` after taking left limits. Enlarge to width `wᵢ + ε`, factor the
   resulting cell range events by independent increments, apply the stable
   range escape rate cell by cell, then send `ε ↓ 0`. The lower bound chooses
   a continuous path strictly inside `G`, uses positive trace separation at
   each partition time to choose a small endpoint core, and iterates the
   segment return kernels. Endpoint return rates are available from the stable
   endpoint comparison. Floor remainders are included in the
   endpoint/terminal-block comparison. Send the path margin and endpoint-core
   widths to zero after taking `n → ∞`. The logarithmic sum is the Riemann sum
   `Σᵢ (tᵢ₊₁ - tᵢ) / (bᵢ - aᵢ)^α = Hα(G)`.

   The deterministic partition is formalized: `PathClass/Boundary/Partition.lean`
   forms the union of the two knot sets with the time endpoints, assigns each
   nonterminal knot its least later common knot, and proves the resulting open
   cells are disjoint and cover `[0,1]` away from the finite knot and endpoint
   set. `PathClass/Energy.lean` proves the exact finite sum of each cell's
   constant width cost times its length. This establishes the deterministic
   `Hα` decomposition.
   The probabilistic independence input is now available in
   `Probability/Process/IndepIncrements/DisjointPaths.lean`:
   `HasIndepIncrements.iIndepFun_finiteAdjacentPaths` proves mutual
   independence of translated paths on any fixed finite sequence of adjacent
   intervals, for countable coordinate families containing the left endpoint.
   `PathClass/Partition/Independence.lean` specializes it to the nonuniform
   common-knot partition and also provides the half-open cell family needed
   for right-continuous boundary jumps. `PathClass/Partition/Range.lean`
   proves the strict-corridor-to-range containment, omitting the terminal
   point of each cell, and factors the selected range events. The stable cell
   adapter in `PathClass/Partition/Stable.lean` translates and normalizes each
   cell, transfers its rational-coordinate law to the unit-time stable law,
   uses fixed-time continuity only to recover the terminal left limit, and
   widens the closed range bound before applying the open tube event. Its
   finite-product theorem gives the stable tube upper bound cell by cell.
   `PathClass/Partition/Scaled.lean` proves the deterministic scaling
   implication and the relative-enlargement form with radii `rᵢ / c`; from
   `HasStableProcessEscapeRate` it derives the logarithmic upper rate, under
   the explicit premise that the corridor probability is eventually positive.
   The lower-bound construction is formalized in
   `PathClass/Partition/LowerCores.lean`, `LowerGeometry.lean`,
   `LowerProduct.lean`, `LowerAssembly.lean`, `LowerRate.lean`, and
   `LowerApproximation.lean`. At every
   common knot it chooses a core centered in the intersection of the two
   boundary trace strips. The core radii start at zero, increase strictly,
   and can all be made smaller than any prescribed positive tolerance.
   Each cell gets finite inner bounds even when an original trace is infinite.
   The endpoint-return event has the source's `Ioc` terminal convention; its
   deterministic concatenation handles the right-continuous jump value only
   in the cell on its right. Independent cell events factor exactly, and the
   zero-start condition is intersected only on its almost-sure set. Hence a
   fixed choice of cores and finite inner bounds gives the eventual logarithmic
   lower estimate with cell rate
   `C * cellLength / (((innerUpper - innerLower - 2 * incomingRadius) / 2)^α)`.
   The incoming-core contraction is essential at this stage. Uniformly
   shrinking all cores removes that loss for each fixed inner corridor.
   `LowerApproximation.lean` proves that each cell admits finite inner bounds
   containing both endpoint cores and having any prescribed width strictly
   below its boundary width; if either boundary trace is infinite, any finite
   target width is allowed. It also proves the stable lower estimate for the
   sum of rates at arbitrary such target widths. This is the correct
   finite-truncation direction for infinite-width cells and the finite-width
   sharpness direction without exchanging boundary and core limits.
   `Energy.lean` now reindexes the integral as a finite sum over common-knot
   cells and converts it to a real-valued cell sum, preserving zero cost on
   infinite-width cells. `Partition/LowerEnergy.lean` chooses target widths
   increasing to each finite cell width and to infinity on infinite-width
   cells, proves convergence of the rate sum to `2^α C · Hα`, and derives the
   stable-process `M₂` lower-rate bound with the exact energy. `Partition/UpperEnergy.lean`
   proves the matching upper bound using exactly the finite-width cells;
   infinite-width cells impose no range restriction and contribute zero energy.
   The lower construction supplies eventual positivity from the positive
   endpoint-core product, not from a real-log inequality. Thus
   `HasStableProcessEscapeRate.tendsto_scaledCorridorLog_eq_energyRate` now
   proves the exact stable-process `M₂` limit, with the source-normalized
   coefficient `2^α C` because the stable unit-tube escape coefficient `C`
   uses half-width one. `PathClass/Rate/StableProcess.lean` converts this to
   the positive coefficient `κ = -2^α C`, proves the `M₃` finite-union rate,
   and assembles the process theorem for `M` under explicit null-measurability
   of the exact target event. Its measurable-set corollary gets this condition
   from continuity of spatial scaling. No corridor boundary-null assumption
   is used.
   The stable uniform-block adapter uses it in
   `Stable/SmallDeviation/Blocks/Independence.lean`, and the uniform-tube upper
   bound consumes the finite-family product theorem in `Blocks/Upper.lean`.
   For a general step corridor, the upper estimate uses half-open cell
   restrictions and range-diameter events; a closed-cell corridor event would
   incorrectly impose the old boundary at a jump knot. The lower-bound
   pathwise gluing, fixed-core logarithmic estimate, and arbitrary target-width
   estimate and exact-energy limit are available on the stable-process side.
   On the random-walk side, `Discrete/PartitionEndpoint.lean` now defines the
   contracted cell event with an open outgoing core band, proves its coordinate
   measurability, and factors adjacent variable-length IID cell events.
   `Discrete/PartitionLowerGeometry.lean` proves by induction that these
   floor-indexed endpoint bands propagate knot cores and imply the global
   strict corridor event, including the right-continuous values at jump knots.
   `Discrete/PartitionLowerProbability.lean` combines this inclusion with the
   exact IID product identity to give a finite-product lower bound for the
   corridor probability. The knot-index maps used here now live with the
   deterministic common partition in `PathClass/Boundary/Partition.lean`, so
   the random-walk proof does not depend on the stable-process geometry layer.
   The exact floor-cell remainder is now covered by a balanced partition:
   `Analysis/Asymptotics/BlockScale.lean` distributes the remainder over all
   blocks, proves their exact sum, and shows both adjacent block lengths are
   asymptotic to the reference length when the block count diverges. The
   stable lower adapter proves that the quotient count diverges for every
   positive-duration cell, and that both balanced lengths have the same
   stable-time ratio and hence the same variable-block path limit. The
   seven-band return-kernel estimate now composes over this exact list, giving
   a sharp exponential lower bound for survival in a fixed interval with no
   discarded suffix. The bridge work now adds measurable arbitrary endpoint
   windows, transfers finite window families through the stable path limit,
   and chooses one amplitude for all same-core returns and all translated
   windows needed between distinct cores. On the discrete side, each such
   finite window family gives a uniform row lower bound for a killed bridge
   between equal-radius cores. A generic kernel lemma composes a variable
   list of return blocks followed by a final bridge and bounds it by the
   killed walk over the exact sum of their lengths. The endpoint bridge, balanced partition, variable-list kernel composition,
   and finite-cell IID identification are now assembled in
   `Stable/Discrete/PartitionLower/`. `PartitionLower/EnergyLower.lean`
   removes the finite core margins in the exact energy limit.
5. The process theorem is now proved for `M₂`, `M₃`, and measurable targets in
   `M`; the general `M` interface states null-measurability explicitly. The
   remaining process-side check is to align this premise with the source's
   class definition and intended theorem statement. The random-walk Theorem 1 rate is now assembled for measurable targets in
   `M` under the source regimes `0 < α < 2`; the remaining source-statement
   audit is the measurability convention for `M` and the `α = 2` endpoint.

The dependency order is therefore: source-stable path law and process escape
rate; fixed-parameter block transfer; source comparisons in both directions;
balanced floor partition and finite-partition `M₂` limit; then the `M₃` and
`M` closures. The complete chain is now built for `0 < α < 2`. The remaining
normal endpoint bridge is recorded below; the Rademacher constant calculation
is a later specialization.

1. The source path classes `M₁`, `M₂`, `M₃`, approximation class `M`, and
   finite-union energy are represented under
   `Probability/Process/SmallDeviation/Mogulskii/PathClass/`. The conditional
   `M₃` rate-to-`M` assembly is now formalized in `PathClass/Rate/`: component
   rates imply the finite-union rate, order the inner and outer energies, give
   a common energy limit, and make that value independent of the approximation
   witness. `PathClass/Partition/UpperEnergy.lean` completes the matching
   stable-process `M₂` upper rate; together with `LowerEnergy.lean`, it proves
   the exact `M₂` limit and eventual positivity. `PathClass/Rate/StableProcess.lean`
   discharges the `M₃` component rates and assembles Theorem 2 for `IsM`, with
   null-measurability of the exact target event as an explicit premise. Its
   measurable-set corollary derives this from continuity of scaling. Whether
   the source's definition of class `M` supplies measurability without that
   explicit assumption is the remaining statement-alignment question; the
   probabilistic rate proof itself no longer assumes component rates.
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
   import boundaries. At `α = 2`, the new
   `Probability/Distributions/Stable/Attraction/Normal/TruncatedMoment.lean`
   proves Feller's quadratic-tail condition, eventual positivity and slow
   variation of the truncated second moment, and the real-part cosine-defect
   asymptotic directly from Gaussian attraction, including infinite variance.
   The remaining domain-of-attraction gap is identifying the squared-modulus
   defect with that real-part defect under the source's zero-centering
   convention, then deriving the compatible quadratic norming and the needed
   J₁ tightness from the original hypotheses. The rounded block inverse is proved
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
argument. The range-event estimate has now also been carried through the
fixed-parameter logarithmic argument to arbitrary positive cell width and
macroscopic duration. It uses the stable block path limit and closed range
event directly, without choosing a tube center. `Discrete/PartitionRange.lean`
proves the finite IID product estimate for variable-length half-open cells.
Each cell constrains only offsets strictly before its right endpoint; the
terminal increment remains in the adjacent block, and the cell factor is the
range probability through time `m - 1`. This matches the right-continuous step
path at a boundary jump. Still needed are the exact bridge from `M₂` boundary
paths to these floor-indexed discrete cells, lower endpoint-core gluing across
the partition, and the finite logarithmic sum/slow-diagonal assembly for
general boundaries.
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
normalization `sqrt (n * secondMoment)`. For infinite-variance normal
attraction, `Normal/TruncatedMoment.lean` derives Feller's quadratic-tail
condition, slow variation and positivity of the truncated second moment, the
real-part cosine-defect asymptotic, and the comparison with the squared-modulus
characteristic defect under zero centering. It derives the compatible
`IsStableNorming 2` relation and the required tail and variance profiles.
`Normal/BlockTail.lean` proves negligible hard-truncation bias without a
finite-second-moment assumption. `Normal/{Oscillation,OscillationPartitions,
PathRange,Tightness}.lean` combine the local estimates into `J₁` tightness.
`Normal/PathLimit.lean` assembles the path-law limit from this tightness and
Gaussian-domain finite-dimensional convergence. The generic
`HasStableClockIncrements.law_of_pathMap` transfer and
`Stable/Brownian/PathLaw.lean` identify the law of a pointwise-continuous
pre-Brownian version as the standard exponent-two path law. Thus the analytic
normal-attraction/FCLT branch is proved. The remaining source interface is
that Mathlib's `IsBrownianReal` gives continuity only almost surely, while the
current measurable continuous-path embedding asks for a pointwise-continuous
version. The existing `BrownianMotion` dependency contains a continuous
modification construction, but its pinned source currently fails to rebuild
with the repository's Lean/Mathlib versions (duplicate declarations and
outdated `Chaining` proofs); it cannot presently be used as a passing import.

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
equality adapter for a fixed corridor event does. The endpoint-band positive
mass inputs, source comparison (32), and equation-(34) bridge comparison are
now proved. The unfinished part is applying these block estimates and the
fixed-parameter limits across all cells of the source's finite partition,
including the shifted/range comparisons and lower endpoint cores. The
stable-process Theorem 2 rate is proved for `M₂` and `M₃`, and for measurable
targets in `M`; source-definition measurability alignment remains to be
checked.

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

These α=2 components do not replace the source-ordered stable proof. The
stable-process Lemma 1 and Lemma 2, including relations (18)--(25), are
complete. The rational-time event and exact self-similar tube-probability
bridge are also present. The characteristic-defect implication for
`0 < α < 2` and the infinite-variance normal-attraction norming/tightness
bridge are proved. The finite-partition assembly of random-walk Theorem 1 is
available for `0 < α < 2`; the process-side Theorem 2 rate is assembled
through `M₂`, `M₃`, and measurable targets in `M`.

The discrete random-walk theorem now has an exact finite-partition proof.

- `Discrete/Horizontal.lean` proves the strict range-event block inequality
  used for the upper estimate, without choosing a random corridor center.
  `Stable/Corridor.lean` transfers the closed range event by closed-set
  Portmanteau. The endpoint-return construction and seven open endpoint bands
  give the matching one-block lower estimate; `SourceLower.lean` derives the
  endpoint masses and J₁ block limit in the three source regimes below index
  two. `BridgeComparison/SourceDecay.lean` proves the source equation-(34)
  logarithmic comparison from the finite bridge cover, entrance mass, base
  positivity, and endpoint decay.
- For a finite-partition `M₂` corridor, `Discrete/PartitionEndpoint.lean`
  defines the contracted local event with an open outgoing core band and proves
  measurability and the incoming/outgoing core implications.
  `Discrete/PartitionLowerProbability.lean` factors these events across the
  exact floor-indexed IID cells and proves their inclusion in the whole
  right-continuous corridor event. This preserves the endpoint convention at
  partition knots.
- `Stable/Discrete/EndpointBandTransfer/StableLower/` supplies the open
  endpoint-mass transfer, cell entrance and exit bridges, and their path-limit
  bounds. `Stable/Discrete/PartitionLower/` composes these with the balanced
  floor partition, obtains eventual positivity, and derives the sharp lower
  energy rate. `Stable/Discrete/PartitionUpper.lean` proves the matching
  selected-cell upper rate. `PartitionLimit.lean` combines both sides into the
  exact logarithmic limit for every admissible `M₂` step corridor.
- `PathClassRate.lean` passes the exact `M₂` rates through finite `M₃` unions
  and the approximation class `M`. `PathClassRegimes.lean` supplies the slow
  variation, stable-process escape rate, and base tightness for `0 < α < 1`,
  `α = 1` with the source sine-centering condition, and `1 < α < 2` with
  integrable centered increments. Thus the random-walk rate theorem for
  measurable targets in `M` is assembled throughout `0 < α < 2`, under the
  stated stable norming, attraction, stable-process, and path-class
  hypotheses. The exact alignment of the formal `M` measurability premise
  with the paper's convention remains to be checked.

The proof order used in the code is the source order: stable path limit and
escape rate; fixed-parameter block transfers; endpoint-return comparisons;
balanced floor partition and finite-cell product; exact `M₂` energy; then the
`M₃` and `M` approximation closure. The lower proof controls the rounded
endpoint in the cell on its left, since that value is observed immediately
before a boundary jump. Open endpoint bands make the lower transfer depend only
on open-set Portmanteau. The upper proof uses half-open cells and range
diameter, so a right-continuous jump at a partition knot is constrained by the
cell on its right.

## Remaining obligations before claiming the complete theorem

1. Finish the `α = 2` source-law bridge. The truncated-moment comparison,
   norming, negligible truncation bias, infinite-variance `J₁` tightness, and
   functional limit to an explicit standard Brownian path law are proved. A
   pointwise-continuous pre-Brownian version is also transferred to the
   `IsStableClockProcessLaw` interface. The remaining point is to obtain the
   measurable càdlàg path law from Mathlib's `IsBrownianReal` hypothesis,
   which only gives almost-sure path continuity. The BrownianMotion dependency
   has the needed continuous-modification theorem in source, but its locked
   checkout does not build against this project's current Lean/Mathlib API.
2. Align the stable-process Theorem 2 and random-walk Theorem 1 interfaces
   with the source's measurability convention for class `M`. The exact `M₂`
   rate, finite-union `M₃` rate, and measurable-target `M` assembly are proved;
   verify whether the paper's definition of `M` itself supplies the explicit
   null-measurability premise used by the Lean theorem.
3. Finish the source-level statement audit: check that the theorem hypotheses,
   path-set convention, normalization, and the intended continuous-boundary
   instances match the paper exactly. The general random-walk proof chain for
   `0 < α < 2` is assembled; this audit must not be confused with the open
   `α = 2` analytic bridge above.
4. Complete the source's separate `α = 2` constant calculation and its
   horizontal/finite-partition Gaussian specialization after the general
   stable theorem's hypotheses are discharged.

## Explicitly rejected route

Do not force `O(aₙ)` consecutive increments of one sign to enter the core.
Its probability cost is `exp(-c aₙ)`, whose normalized logarithm is of order
`-aₙ³/n`; the theorem assumes only `aₙ → ∞` and `aₙ/√n → 0`, which do not
imply `aₙ³/n → 0`. The return-core endpoint bands replace that invalid step.
