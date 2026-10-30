# Mogulskii stable theorem: source-ordered proof and status

This note records the proof route and verified status for the general
stable-domain theorem of A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081 ([original article record and full text](https://www.mathnet.ru/eng/tvp3978)).
Lean module paths without the prefix
`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/` are relative to
that subtree; modules outside it are written with their source-root paths.
The Gaussian/`α = 2` calculation in Theorem 3, Section 4 comes only after the
general stable-process and random-walk theorems; it is a later specialization,
not the active first proof target. The theorem chains described here are
kernel-checked under their stated hypotheses and probability semantics.

## The general stable theorem

Let `Fα` be a strictly `α`-stable law with `0 < Fα(0) < 1`, and let the
increment law lie in its domain of attraction with norming `B(n)`. Mogul'skii
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
theorem coefficient and `Hα` is Mogul'skii's path-set functional. To keep the
normalization unambiguous, write `C₀ < 0` for the Lemma 1(I) escape constant
of the base corridor `a I₋₁¹`; since `Hα(I₋₁¹) = 2⁻α`, the coefficient in
Theorems 1 and 2 is `C = 2^α C₀`. Lean's positive rate coefficient is
`κ = -C = -2^α C₀`. Both general-α results precede computing the coefficient
for `α=2`.

The proof follows Mogul'skii's sections and dependency order. The stable
process theorem and the random-walk theorem for `0 < α < 2` are now assembled
under the source regimes recorded below. The normal-attraction endpoint has
the truncated-moment norming, infinite-variance `J₁` tightness, and
normal-domain functional limit. Its path-law bridge uses Mathlib's
almost-surely continuous Brownian process directly. The sharp horizontal
`α = 2` theorem is proved for every centered unit-second-moment increment
law. The full `α = 2` normal-domain path-class rate is assembled, including
infinite-variance laws. The Brownian escape constant is identified as
`C₀ = -π²/8`; the full-width coefficient is `-π²/2`. The source endpoint
convention `S_(n−1)` has its own exact variable-horizon M₂ rate and M₃/M
closures. Stable-process Lemma 2, relations (21)--(25), and Lemma 1,
relations (18)--(20), are formalized.

## Fixed mathematical proof scheme

The target is Mogul'skii's Theorems 1 and 2 for the path classes `M₂`, `M₃`,
and `M`, with the strict path-set convention and normalization stated there. The
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

   The deterministic partition is formalized in
   `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/Boundary/Partition.lean`
   forms the union of the two knot sets with the time endpoints, assigns each
   nonterminal knot its least later common knot, and proves the resulting open
   cells are disjoint and cover `[0,1]` away from the finite knot and endpoint
   set. `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Energy.lean`
   proves the exact finite sum of each cell's constant width cost times its
   length. This establishes the deterministic `Hα` decomposition.
   The probabilistic independence input is now available in
   `Probability/Process/IndepIncrements/FiniteObservations/DisjointPaths.lean`:
   `HasIndepIncrements.iIndepFun_finiteAdjacentPaths` proves mutual
   independence of translated paths on any fixed finite sequence of adjacent
   intervals, for countable coordinate families containing the left endpoint.
   `Probability/Process/Path/PathClass/StepCorridor/Probability/Partition/Independence.lean`
   specializes it to the nonuniform
   common-knot partition and also provides the half-open cell family needed
   for right-continuous boundary jumps.
   `Probability/Process/Path/PathClass/StepCorridor/Probability/Partition/Range.lean`
   proves the strict-corridor-to-range containment, omitting the terminal
   point of each cell, and factors the selected range events. The stable cell
   adapter in
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Core/Stable.lean`
   translates and normalizes each
   cell, transfers its rational-coordinate law to the unit-time stable law,
   uses fixed-time continuity only to recover the terminal left limit, and
   widens the closed range bound before applying the open tube event. Its
   finite-product theorem gives the stable tube upper bound cell by cell.
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Core/Scaled.lean`
   proves the deterministic scaling
   implication and the relative-enlargement form with radii `rᵢ / c`; from
   `HasStableProcessEscapeRate` it derives the logarithmic upper rate, under
   the explicit premise that the corridor probability is eventually positive.
   The lower-bound construction is split by semantic layer. Common endpoint
   cores and their deterministic geometry are formalized in
   `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/Partition/LowerCores.lean`
   and `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/Partition/LowerGeometry.lean`.
   Choosing finite inner widths and identifying their limiting energy are in
   `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Partition/LowerApproximation.lean`
   and `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Partition/LowerEnergy.lean`.
   Stable-process cell geometry, return kernels, independence, probability
   assembly, and logarithmic limits are in
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Lower/Geometry.lean`,
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Lower/Kernel.lean`,
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Independence.lean`,
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Lower/Assembly.lean`,
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Lower/Rate.lean`,
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Lower/EnergyRate.lean`,
   and `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Lower/ApproximationRate.lean`.
   At every
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
   `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Partition/LowerApproximation.lean`
   proves that each cell admits finite inner bounds
   containing both endpoint cores and having any prescribed width strictly
   below its boundary width; if either boundary trace is infinite, any finite
   target width is allowed. The stable lower estimate for the sum of rates at
   arbitrary target widths is proved in
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Lower/ApproximationRate.lean`.
   This is the correct
   finite-truncation direction for infinite-width cells and the finite-width
   sharpness direction without exchanging boundary and core limits.
   `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Energy.lean` now
   reindexes the integral as a finite sum over common-knot
   cells and converts it to a real-valued cell sum, preserving zero cost on
   infinite-width cells.
   `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Partition/LowerEnergy.lean`
   chooses target widths
   increasing to each finite cell width and to infinity on infinite-width
   cells, proves convergence of the rate sum to `2^α C · Hα`, and derives the
   stable-process `M₂` lower-rate bound with the exact energy.
   `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/Partition/UpperEnergy.lean`
   proves the matching upper bound using exactly the finite-width cells;
   infinite-width cells impose no range restriction and contribute zero energy.
   The lower construction supplies eventual positivity from the positive
   endpoint-core product, not from a real-log inequality. The exact
   stable-process `M₂` limit is
   `HasStableProcessEscapeRate.tendsto_scaledCorridorLog_eq_energyRate` in
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Upper/EnergyRate.lean`;
   it has the source-normalized
   coefficient `2^α C` because the stable unit-tube escape coefficient `C`
   uses half-width one. `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Rate.lean` converts this to
   the positive coefficient `κ = -2^α C`, proves the `M₃` finite-union rate,
   and assembles the process theorem for `M` under explicit null-measurability
   of the exact target event. Its measurable-set corollary gets this condition
   from continuity of spatial scaling. No corridor boundary-null assumption
   is used.
   The stable uniform-block estimate is in
   `Probability/Process/Stable/SmallDeviation/Blocks/Upper/Basic.lean`; its
   product and stationarity inputs are owned by
   `Probability/Process/Path/Skorokhod/Corridor/UniformBlocks/Probability/Independence.lean`
   and `Probability/Process/Path/Skorokhod/Corridor/UniformBlocks/Probability/Stationarity.lean`.
   For a general step corridor, the upper estimate uses half-open cell
   restrictions and range-diameter events; a closed-cell corridor event would
   incorrectly impose the old boundary at a jump knot. The lower-bound
   pathwise gluing, fixed-core logarithmic estimate, and arbitrary target-width
   estimate and exact-energy limit are available on the stable-process side.
   On the random-walk side,
   `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Lemmas/Partition/Endpoint.lean`
   now defines the
   contracted cell event with an open outgoing core band, proves its coordinate
   measurability, and factors adjacent variable-length IID cell events.
   `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Lemmas/Partition/LowerGeometry.lean`
   proves by induction that these
   floor-indexed endpoint bands propagate knot cores and imply the global
   strict corridor event, including the right-continuous values at jump knots.
   `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Lemmas/Partition/LowerProbability.lean`
   combines this inclusion with the
   exact IID product identity to give a finite-product lower bound for the
   corridor probability. The knot-index maps used here now live with the
   deterministic common partition in
   `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/Boundary/Partition.lean`, so
   the random-walk proof does not depend on the stable-process geometry layer.
   The exact floor-cell remainder is now covered by a balanced partition:
   `Analysis/Asymptotics/Scale/Block/Partition.lean` distributes the remainder over all
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
   `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Discrete/Partition/Lower/`.
   The finite-product logarithmic rate transfer is stated independently in
   `Probability/MeasureTheory/FiniteProduct.lean`; the lower chain then removes
   the finite core margins in
   `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Discrete/Partition/Lower/EnergyLower.lean`.
5. The process theorem is proved for `M₂`, `M₃`, and `M`. For arbitrary `IsM`
   targets, the API states matching inner and outer probability rates; it does
   not infer measurability from energy approximation. Ordinary probability
   limits retain an explicit null-measurability premise. The random-walk
   Theorem 1 rate is assembled under the source regimes `0 < α < 2` and the
   normal-domain regime `α = 2`, including the source `S_(n−1)` endpoint and
   the explicit Brownian coefficient.

The dependency order is therefore: source-stable path law and process escape
rate; fixed-parameter block transfer; source comparisons in both directions;
balanced floor partition and finite-partition `M₂` limit; then the `M₃` and
`M` closures. The complete chain is built for `0 < α ≤ 2`; the exponent-two
path-class rate uses the coefficient identified from the explicit horizontal
calculation.

1. The source path classes `M₁`, `M₂`, `M₃`, approximation class `M`, and
   finite-union energy are represented under
   `Probability/Process/Path/PathClass/StepCorridor/Probability/`. The conditional
   `M₃` rate-to-`M` assembly is now formalized in
   `Probability/Process/Path/PathClass/StepCorridor/Probability/Rate/`:
   component rates imply the finite-union rate, order the inner and outer energies, give
   a common energy limit, and make that value independent of the approximation
   witness. The generic
   `Probability/Process/Path/PathClass/StepCorridor/Probability/Rate/Approximation.lean`
   and `Probability/Process/Path/PathClass/StepCorridor/Probability/Rate/InnerOuter.lean`
   contain the `M₃`-to-`M` approximation
   closure. Stable-specific component rates are in
   `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Rate.lean`.
   Arbitrary `IsM` targets have matching inner/outer rates; ordinary
   probability theorems state their null-measurability premise explicitly.
2. Lemma 2 estimates (21)--(25) are proved in the public stable-process
   entries `Probability/Process/Stable/SmallDeviation/{ShiftedCorridor,
   RangeComparison,BlockBounds,EndpointComparison}.lean`. The statements preserve the source's
   strict and half-open event conventions.
3. Lemma 1 (18)--(20) is proved in
   `Probability/Process/Stable/SmallDeviation/EscapeRate/Basic.lean` and its
   `Probability/Process/Stable/SmallDeviation/EscapeRate/{Corridor,Endpoint,Law}.lean`
   modules. It establishes a
   finite strictly negative escape rate and transfers the same rate to the
   translated and endpoint-constrained events. The unit-interval
   `CadlagPath` transfer in
   `Probability/Process/Stable/SmallDeviation/EscapeRate/PathLaw/Transfer.lean`
   is also proved, by
   comparison with a reference stable Lévy process having the same increment
   specification; it does not construct a full-time process extension from an
   arbitrary unit-interval law.
4. Complete the domain-of-attraction foundation before the discrete Lemma 3/4
   argument. General attraction definitions and finite-sum characteristic-
   function formulas are owned by `Probability.Distributions.DomainOfAttraction`;
   the stable specialization proves (6)--(7) with one coefficient shared by
   all frequencies. The norming-ratio implication (E), compact-frequency
   uniform convergence (I), and continuous small-frequency regular variation
   (J) are now proved in `Probability/Distributions/Stable/Attraction/NormingRatios/`; the norming-sequence
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
   `Probability/Distributions/Stable/Attraction/Normal/QuadraticTail.lean`
   proves Feller's quadratic-tail condition, eventual positivity and slow
   variation of the truncated second moment directly from Gaussian attraction,
   including infinite variance. `Normal/Centering.lean` proves integrability
   and centering, while `Normal/Norming.lean` derives the real-part
   cosine-defect asymptotic, quadratic norming, and the required tail profiles.
   The general discarded-first-moment estimate is in
   `Probability/Distributions/Moments/Truncated/TailIntegral.lean`.
   The centered normal-domain bridge is complete: the squared-modulus defect,
   quadratic norming, and infinite-variance `J₁` tightness follow from the
   original zero-centering and truncated-moment assumptions. The rounded block
   inverse is proved for `0 < α ≤ 2` when slow variation of `L*` and
   `IsStableNorming` are supplied. The source-regime stable random-walk
   path-law limit and its variable-block transfer are also proved under their
   stated attraction, tightness, norming, and slow-variation hypotheses.
   Corridor probability equality still needs a null-boundary premise; the
   one-sided open lower bound used by M2 does not.
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
`Stable/Rate/Upper.lean` and `Stable/Rate/Lower/`. Its lower modules expose
the block endpoint-return estimate, logarithmic liminf consequences, eventual
positivity, and the final rate limit as separate mathematical interfaces. The upper proof uses
closed-set Portmanteau and shrinking outer corridors; the lower proof uses
the source's seven endpoint-return bands, open-set Portmanteau, and the
source block count. Both now require slow variation of `L*` but no upper
bound on its values along the shrinking scale. The lower route also supplies
the eventual positivity and lower coboundedness needed by the upper real-log
argument. The range-event estimate has now also been carried through the
fixed-parameter logarithmic argument to arbitrary positive cell width and
macroscopic duration. It uses the stable block path limit and closed range
event directly, without choosing a tube center. `Probability/Process/RandomWalk/Path/Block/Partition/StepCorridor.lean`
proves the finite IID product estimate for variable-length half-open cells.
Each cell constrains only offsets strictly before its right endpoint; the
terminal increment remains in the adjacent block, and the cell factor is the
range probability through time `m - 1`. This matches the right-continuous step
path at a boundary jump. The exact `M₂` boundary-to-cell bridge, endpoint-core
gluing, and finite logarithmic sum/slow-diagonal assembly are now present in
the partition modules listed above.
5. Lemma 3's discrete analogues, both directions of the block inequalities,
   Lemma 4's fixed-parameter limits, and the source-ordered slow-growth
   diagonal (38)--(44) are assembled into the random-walk Theorem 1. The
   Rademacher calculation in §4 identifies the `α = 2` constant after the
   general stable rate has been established.

The inverse-Tauberian implication is complete for `0 < α < 2`: it transfers
the characteristic-function defect to regular variation of the two-sided
increment tail and gives the truncated-moment/defect ratio. For `α = 2`, the
finite-variance branch is formalized in
`Probability/Distributions/Stable/Attraction/Normal/Basic.lean`: a centered
probability law with integrable square and positive second moment has
standard-Gaussian attraction and `IsStableNorming` under the canonical
normalization `sqrt (n * secondMoment)`. For infinite-variance normal
attraction, `Probability/Distributions/Stable/Attraction/Normal/QuadraticTail.lean`
derives Feller's quadratic-tail condition, slow variation and positivity of
the truncated second moment. `Normal/Centering.lean` proves finite first
moment and zero centering; `Normal/Norming.lean` derives the real-part
cosine-defect asymptotic, the comparison with the squared-modulus
characteristic defect under zero centering, the compatible `IsStableNorming 2`
relation, and the required tail and variance profiles. The reusable
discarded-first-moment estimate is in
`Probability/Distributions/Moments/Truncated/TailIntegral.lean`.
`Probability/Process/RandomWalk/FunctionalLimit/Normal/BlockTail.lean` proves
negligible hard-truncation bias without a finite-second-moment assumption.
`Probability/Process/RandomWalk/FunctionalLimit/Normal/{Oscillation,
OscillationPartitions,PathRange,Tightness}.lean` combine the local estimates
into `J₁` tightness.
`Probability/Process/RandomWalk/FunctionalLimit/Normal/PathLimit/Basic.lean`
assembles the path-law limit from this tightness and
Gaussian-domain finite-dimensional convergence. The generic
`HasStableClockIncrements.law_of_pathMap_ae` transfer in
`Probability/Process/Stable/PathLaw/Basic.lean` and
`Probability/Process/Stable/Brownian/PathLaw.lean` identify Mathlib's actual `IsBrownianReal`
path law through the almost-sure càdlàg path map. Thus the analytic
normal-attraction/FCLT branch and its Mathlib Brownian interface are proved.

The stable random-walk `J₁` limit is proved under the three source centering
regimes. Its path-law identification uses Mathlib's tight-family compactness,
probability-measure almost-everywhere continuous mapping, and projective-limit
uniqueness, with a repository-specific Fubini argument to choose dense
continuity times for each weak cluster law. Fubini is an auxiliary step in
this path-space identification, not a step attributed to Mogul'skii's paper.
The arbitrary-center finite-dimensional theorem keeps the block-center ratio
explicit; source wrappers use zero scalar centering. The variable-block limit
follows by a deterministic-parameter product with a Dirac law and continuous
mapping, then the rounded norming inverse. M2's open-event lower transfer
needs no boundary-nullity, while an equality adapter for a fixed corridor
event does. The stable-process and random-walk theorem chains are assembled
for `0 < α ≤ 2`. The final APIs distinguish matching inner/outer rates for
every `IsM` target from ordinary probability limits, which require the exact
target event to be measurable or null-measurable.

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

## `α = 2` horizontal upper component

The sharp upper limsup is formalized conditionally on eventual tube positivity
and lower coboundedness of the normalized logarithms. Those two analytic
conditions must be discharged by the lower bound before the two-sided limit
can be claimed.

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

## Completed `α = 2` horizontal lower component

The assembled Lean proof follows the endpoint-return and seven-window
construction in Mogul'skii's Lemma 3(d). For an interval of Dirichlet width
`8m` and block length `n` with `n / (8m)^2 → C`, the principal eigenvalue satisfies
`cos(π/(8m))^n → exp(-π² C / 2)`. The endpoint windows retain a positive
fraction of the central sine-weighted mass, uniformly at each fixed `C`.

1. `Lemmas/EndpointBands/SpectralMass.lean` defines the central
   starting point, the central core, and `centralEndpointBandTarget`. Its
   spectral estimate bounds the transition mass of the parity-compatible
   sites in an endpoint band, and its diffusive-ratio theorem gives the
   corresponding asymptotic lower bound.
2. `Lemmas/EndpointBands/SevenWindows.lean` places the seven
   endpoint windows and proves one common eventual lower bound for their
   spectral masses. Each target contains exactly `e - 1` parity-compatible
   sites in its prescribed lattice window, and its mass is proportional to
   `(e - 1)/(8m)`.
   Its seven left endpoints are `4m - (3s + e) + js`; under `3s + e ≤ 2m`
   they lie in the central region `[2m,6m]`.
3. `Lemmas/EndpointBands/SpectralLowerBound.lean` converts the seven
   target-mass estimates to Rademacher endpoint-window events and, by Donsker
   and Portmanteau with explicit corridor margins, transfers the lower bound
   to every centered unit-variance increment law.
4. `Rate/Endpoint/Windows.lean` combines those window probabilities with the
   generic return-kernel iteration in
   `Probability/Process/RandomWalk/SmallDeviation/HorizontalTube/EndpointWindow/Iteration.lean`.
   The scale transfer lets `C → ∞`; the choices `p = 1/C`,
   `q = 1 - 10/C`, and `δ = p/(100√C)` give the lower rate `-π²/2`.
   `Rate/Endpoint/Selection/Basic.lean` supplies these parameters and assembles
   the lower bound with the sharp upper bound.

The central-core and arbitrary endpoint-band spectral estimates are the
finite-state inputs to the theorem-specific conversion in
`Lemmas/EndpointBands/SpectralLowerBound.lean`. The seven-window placement
stays under `Lemmas/` because it is specific to Lemma 3(d); the generic
endpoint-band Donsker transfer is in
`Probability/Process/RandomWalk/SmallDeviation/HorizontalTube/EndpointBand/Donsker/Normalized.lean`.

## Later `α = 2` application to piecewise corridors

Once the general Theorem 1 has been formalized and the `α = 2` constant has
been computed, this is the route for its concrete piecewise-corridor
specialization. It must not be mistaken for the proof of the general Theorem
1 itself. Apply the horizontal rate on each interval of a finite partition;
for the upper bound use enclosing horizontal intervals, and for the lower
bound use strictly shrunken corridors and endpoint margins. The open/closed
Portmanteau directions and all endpoint margins must be explicit.

## Existing Lean components and their actual status

- `Probability/Process/RandomWalk/SmallDeviation/HorizontalTube/Blocks/UpperBound.lean`
  proves the finite IID block comparisons for open and closed horizontal tubes.
  Their hypotheses contain no Mogul'skii scale or moment condition.
- `Probability/Process/RandomWalk/Path/Block/Partition/Range.lean`
  proves the strict whole-path range-event block inequality used for the upper
  estimate, without choosing a tube center or imposing a moment condition.
  The common-core return-kernel iteration is in
  `Probability/Process/RandomWalk/SmallDeviation/HorizontalTube/Kernel/BlockIteration.lean`.
- `Probability/Process/RandomWalk/SmallDeviation/HorizontalTube/EndpointBand/{Basic,Iteration}.lean`
  defines the finite
  endpoint-band events and proves their measurability, corridor inclusions,
  and return-kernel consequences.
- `Probability/Process/RandomWalk/SmallDeviation/HorizontalTube/EndpointBand/Donsker/Normalized.lean`
  transfers fixed Brownian endpoint-band bounds to moving blocks. The
  assembled sharp lower rate uses the endpoint-window route in
  `Rate/Endpoint/Windows.lean`; the endpoint-band iteration remains a
  separate reusable interface used by the stable discrete endpoint-return
  module.
- `Probability/Process/Brownian/SmallDeviation/Range/FiniteCover.lean` proves
  the fixed finite spectral-corridor cover estimate;
  `Probability/Process/Brownian/SmallDeviation/Range/UpperRate.lean` derives
  the Brownian small-width rate.
- `Probability/Process/RandomWalk/SmallDeviation/Range/BlockDonsker.lean`
  transfers block oscillation probabilities to Brownian range mass. The proof-specific
  one-block estimate is in `Rate/Bounds/Lemmas/SharpUpper/BlockEstimate.lean`.
- `Rate/Bounds/Lemmas/SharpUpper/LogarithmicTransfer.lean` transfers the
  block bound to the normalized logarithmic limsup with explicit positivity
  and lower-coboundedness hypotheses.
- `Rate/Bounds/Lemmas/SharpUpper/FiniteCoverParameters.lean` chooses the
  cover count, Donsker slack, and block constant in proof order.
- `Rate/Bounds/SharpUpper.lean` assembles the sharp upper limsup
  `≤ -π²/2`; `Rate/Endpoint/Selection/Basic.lean` assembles the matching
  endpoint-window lower rate and the horizontal limit.

These α=2 components do not replace the source-ordered stable proof. The
stable-process Lemma 1 and Lemma 2, including relations (18)--(25), are
complete. The rational-time event and exact self-similar tube-probability
bridge are also present. The characteristic-defect implication for
`0 < α < 2` and the infinite-variance normal-attraction norming/tightness
bridge are proved. The finite-partition assembly of random-walk Theorem 1 is
available for `0 < α < 2`; the process-side Theorem 2 rate is assembled
through `M₂`, `M₃`, and measurable targets in `M`.

The discrete random-walk theorem now has an exact finite-partition proof.

- `Probability/Process/RandomWalk/Path/Block/Partition/Range.lean`
  proves the strict range-event block inequality
  used for the upper estimate, without choosing a random corridor center or
  imposing moments. `Stable/Corridor.lean` transfers the closed range event by
  closed-set Portmanteau. The endpoint-return construction and seven open
  endpoint bands give the matching one-block lower estimate;
  `Stable/Discrete/TerminalLeft/Bounds/Lower.lean` derives the endpoint
  masses and J₁ block limit in the three source regimes below index two.
  `Stable/Discrete/Bridge/Lemmas/TerminalLeftDecay.lean` proves Mogul'skii's equation-(34)
logarithmic comparison from the finite bridge cover, entrance mass, base
positivity, and endpoint decay. This equation-(34) result is currently a
separate proof-support chain: it is not in the import closure of
`Mogulskii/Theorems.lean` or of the finite-partition path-class assembly
described below. The main formal theorem therefore does not yet derive its
rate through this source comparison; keep the two proof routes distinguished
until that connection is established from the paper's argument.
- For a finite-partition `M₂` corridor, `Lemmas/Partition/Endpoint.lean`
  defines the contracted local event with an open outgoing core band and proves
  measurability and the incoming/outgoing core implications.
  `Lemmas/Partition/LowerProbability.lean` factors these events across the
  exact floor-indexed IID cells and proves their inclusion in the whole
  right-continuous corridor event. This preserves the endpoint convention at
  partition knots.
- `Stable/Discrete/Endpoint/BandTransfer/Lower/` supplies the open
  endpoint-mass transfer, cell entrance and exit bridges, and their path-limit
  bounds. `Stable/Discrete/Partition/Lower/` composes these with the balanced
  floor partition, obtains eventual positivity, and derives the sharp lower
  energy rate. `Stable/Discrete/Partition/Upper.lean` proves the matching
  selected-cell upper rate. `Stable/Discrete/Partition/Limit.lean` combines both sides into the
  exact logarithmic limit for every admissible `M₂` step corridor.
- `Stable/Discrete/PathClass/Rate.lean` passes the exact `M₂` rates through finite `M₃` unions
  and the approximation class `M`. `Stable/Discrete/PathClass/Regimes.lean` supplies the slow
  variation, stable-process escape rate, and base tightness for `0 < α < 1`,
  `α = 1` with the source sine-centering condition, and `1 < α < 2` with
  integrable centered increments. Thus the random-walk rate theorem for
  measurable targets in `M` is assembled throughout `0 < α < 2`, under the
  stated stable norming, attraction, stable-process, and path-class
  hypotheses. The normal-domain `α = 2` wrapper also assembles the full path
  class rate, with infinite-variance increments allowed. Its coefficient is
  identified explicitly as `-π²/2` under the full-width normalization.
  Arbitrary `IsM` targets use the inner/outer probability API; the ordinary
  probability theorem keeps the stated measurability premise.

The proof order used in the code is the source order: stable path limit and
escape rate; fixed-parameter block transfers; endpoint-return comparisons;
balanced floor partition and finite-cell product; exact `M₂` energy; then the
`M₃` and `M` approximation closure. The lower proof controls the rounded
endpoint in the cell on its left, since that value is observed immediately
before a boundary jump. Open endpoint bands make the lower transfer depend only
on open-set Portmanteau. The upper proof uses half-open cells and range
diameter, so a right-continuous jump at a partition knot is constrained by the
cell on its right.

## Completed source alignment

The terminal-left source path has an exact variable-horizon M₂ rate. Its last
block uses its true shortened length, not an `o(1)` probability comparison;
the M₂ limit is then passed through the M₃/M approximation closure. For
arbitrary `IsM` targets, the formal conclusion is equality of inner and outer
exponential rates. Ordinary probability limits retain the explicit
measurability or null-measurability premise, since energy approximation alone
does not imply that a target is measurable.

The exponent-two coefficient is identified by comparing the general
path-class limit with the explicit horizontal-tube limit. This gives escape
constant `-π²/8` and full-width coefficient `-π²/2`; the Gaussian source-path
specialization is in `Gaussian/Path/TerminalLeft/Basic.lean`.

The `α = 2` source-law bridge is formalized. A generic rational-coordinate
measurable embedding constructs a Skorokhod-valued realization of every
almost-surely càdlàg real process, with evaluation equalities almost surely at
each fixed time. Mathlib's `IsBrownianReal.cont` supplies the needed
almost-sure continuity, so the normal-domain functional limit targets the
path law of an actual Mathlib Brownian process. The endpoint-window spectral
estimates and Brownian transfer prove the exact horizontal small-deviation
limit for centered unit-variance increments. The normal-domain `α = 2` path-
class rate is assembled for measurable targets, including infinite-variance
laws, and its coefficient is identified explicitly as `-π²/2` under the
full-width normalization.

## Explicitly rejected route

Do not force `O(aₙ)` consecutive increments of one sign to enter the core.
Its probability cost is `exp(-c aₙ)`, whose normalized logarithm is of order
`-aₙ³/n`; the theorem assumes only `aₙ → ∞` and `aₙ/√n → 0`, which do not
imply `aₙ³/n → 0`. The return-core endpoint bands replace that invalid step.
