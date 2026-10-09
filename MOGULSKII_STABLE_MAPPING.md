# Mogulskii (1974) small deviations: the original statements, and where each one lives

Source: А. А. Могульский, *Малые уклонения в пространстве траекторий*, Теория вероятностей и её применения
**XIX**(4), 1974. Local copy at `~/Downloads/Mogulskii_1974_Small_deviations.pdf` (11 pages, 21363 characters of
text layer, extracted to `/tmp/mogul.txt`). The statements below are transcribed from that text; the OCR is
noisy, so formulas are restored to their mathematical reading while the original numbering — (2), (3), (4),
(15), (16), (18)–(20), (30)–(34), (36), (44) — is kept verbatim.

## The original statements

* **(2)** `ξ₁, ξ₂, …` are i.i.d. with increment law `F` and
  `P((ξ₁+…+ξₙ)/B(n) < x) → F_a(x)`, where `F_a` is **strictly stable** and
  **`0 < a ≤ 2`**; for `a = 1` an extra centering is used. In (3), `F` is the
  increment law, while `F_a` is the limiting law.
* **(3)** `L*(u) = u^{a−2} ∫_{−u}^{u} ξ² F(dξ)`, a slowly varying function under the stable-domain assumptions. A finite positive limit is a special case (for example, under a pure power-tail asymptotic); general slow variation does not imply convergence. At `a = 2`, convergence to `E ξ²` requires a finite second moment.
* **(4)** `B*(B(n)) ↝ d·n` with `B*(u) = u^α / L*(u)`; after rescaling,
  `d = 1`. Equivalently `bₙ^α = n·L*(bₙ)·(1 + o(1))`; this does not imply
  `bₙ^α = Θ(n)` unless the slowly varying factor is bounded above and below.
* **(15) Теорема 1.** Let `0 < F_α(0) < 1`. For every `{x(n)}` with
  `x(n) → ∞` and `x(n)·B⁻¹(n) → 0`, and every path set `G ∈ 𝒜` in the
  paper's class,
  `ln P(sₙ(·) ∈ G) ~ C · H_α(G) · n · x(n)^{-α} · L*(x(n))`,
  where `−∞ < C < 0` depends only on the strictly stable limit law `F_α`
  (see Лемма 1). This is not a theorem for arbitrary path sets.
* **(16) Теорема 2.** For a strictly stable process with
  `P(ξ(1) < x) = F_α(x)` and `0 < F_α(0) < 1`, for each `G ∈ 𝒜`,
  `ln P(ε⁻¹ ξ(·) ∈ G) ~ C · H_α(G) · ε^{-α}` as `ε ↓ 0`. This is the
  stable-process (single-block) statement, with the same constant `C` as in
  Теорема 1.
* **Лемма 1. I (18)** `ε^α ln P(ξ(·) ∈ ε𝔘) → C` as `ε ↓ 0`,
  `C ∈ (−∞, 0)`. **II (19)(20)** the tubes
  `ε𝔙_b^c` and `ε𝔙_b^{d(1)}` are asymptotically equivalent to `ε𝔘`.
* **Lemma 2, relations (21)–(25), is proved for the stable-process model** in
  `Probability/Process/Stable/SmallDeviation/{ShiftedCorridor,RangeComparison,Blocks/Upper/ArbitraryHorizon,BlockBounds,EndpointComparison}.lean`.
  The APIs retain the source's endpoint conventions and exponents. **Lemma 3** is the discrete walk version, with **(32)**
  `P(sₙ(·) ∈ 𝔘) ≤ P(sₙ(·) ∈ X(0, c)𝔘)` for `c = m/n`, **(33)**
  `P(sₙ(·) ∈ 𝔘 ∩ ε) ≥ [min_{−3<i<3} P(sₙ(·) ∈ X(0, c)𝔘)]^k` with `k = [c⁻¹] + 1`, and **(34)**
  `ln P(sₙ(·) ∈ Y_c^b(1) ∩ I_{-(1+ε)}^{1+ε}) ≳ ln P(sₙ(·) ∈ 𝔘)`, for fixed `ε > 0` and `−1 ≤ c < b ≤ 1`. In the source's convention, `uₙ ≳ vₙ` means `liminf vₙ/uₙ ≥ 1`; both logarithms are nonpositive, so (34) compares the base-corridor logarithm over the endpoint-constrained widened-corridor logarithm. The discrete block and corridor estimates for the current step-path convention are formalized in the partition and bridge modules listed below. **Лемма 4. I** is (15) at `G = 𝔘`:
  `ln P(sₙ(·) ∈ 𝔘) ~ C · n · x(n)^{-α} · L*(x(n))`.

## What §3 («Доказательство теорем 1 и 2») actually does

Let `G` be a set whose boundary functions `L₁, L₂` have discontinuities at `0 < t₁ < … < 1`. On each interval
`(t_i, t_{i+1})`, `i = 0, …, N` (with `t₀ = 0`, `t_{N+1} = 1`), the set `G` is a **strip with straight
boundaries**: `X(t_i, t_{i+1} − 0)G = X(t_i, t_{i+1} − 0)[a_i, b_i]` with `a_i = L₁`, `b_i = L₂` there. The
upper bound comes from

```
P(sₙ(·) ∈ G) ≤ ∏_{i=0}^{N} P(sₙ(·) ∈ X(t_i, t_{i+1})[c_i]),   c_i = (a_i − b_i)/2,
```

together with Лемма 4, and the lower bound from the same product with a shrink `(1 − δ)` of the strip, together
with Лемма 3. Theorem 2 is proved "in exactly the same way with Лемма 1". Equation **(44)** is the
normalization statement in between: along `x(n) → ∞`, `x(n)B⁻¹(n) → 0` there is `a(n) ↑ ∞` with
`ln P(sₙ(·) ∈ … X(0, a(n)^α n⁻¹ [B*(x(n))]) I⁻¹ …) ~ a(n)^α·C`; equation (44) explicitly has the factor
`a(n)^α` on both sides of its scale comparison. Equation (36) is then obtained from (31)–(34) of Лемма 3.

Two consequences that matter for the formalization:

1. **The blocks are relative sub-intervals of the same `n`-step path**, of relative lengths `t_{i+1} − t_i`
   fixed by the discontinuities of the boundary. The product over blocks is taken over *disjoint step ranges*,
   which is exactly the independence structure the scale-free gluing in
   `Probability/Process/RandomWalk/Path/Block/Partition/Basic.lean` formalizes.
2. **The proof partitions the horizon at the boundary discontinuities.** The finite relative-time partition, balanced floor lengths, variable-cell probabilities, endpoint-core bridges, and their logarithmic Riemann-sum assembly are formalized. The paper's terminal `S_(n−1)` convention also has an exact path/event encoding and a proved variable-horizon rate: the final cell uses exactly `n−1−⌊nt_{m−1}⌋` increments, and the proof does not transfer rates through an `o(1)` probability error.

## Normalisation

```
λ_n := n · L*(x(n)) · x(n)^{-α}          -- the factor in (15) and Лемма 4
```

so that `−(1/λ_n) ln P(sₙ(·) ∈ G) → −C · H_α(G)`. For a corridor with lower boundary `f` and upper
boundary `g`, its energy is `∫₀¹ dt / (g − f)^α`, matching the `corridorEnergy` of
`Probability/Process/RandomWalk/Path/Corridor/Energy.lean`. `λ_n` is available in the library as
`stableRateNormalization α ν scale n`, defined as the reciprocal of `stableSmallDeviationRate` (commit
`7cccf6d4`), so every rate statement has both directions readable at the definition site.

## Where each piece lives

| original | module | state |
| --- | --- | --- |
| (2), (4): domain of attraction, norming | `Distributions/Stable/Attraction/`, `Analysis/Asymptotics/RegularVariation/`, and `RandomWalk/SmallDeviation/Mogulskii/Stable/Scale.lean` | The two-sided inverse-Tauberian implication for `0 < α < 2` and the Gaussian normal-domain truncated-moment/norming branch, including infinite variance, are formalized under the stated attraction conventions. The rounded block inverse is proved when slow variation and stable norming hold. |
| Fixed block endpoint under a domain-of-attraction limit | `Distributions/DomainOfAttraction/Block.lean`, `RandomWalk/SmallDeviation/Mogulskii/Stable/Scale.lean`, `Distributions/Stable/Attraction/Norming/Inverse.lean` | A general Slutsky adapter handles finite partial sums and preserves centering. Under slow variation and stable norming, rounded block scales converge to the required stable-time values. The Gaussian normal-domain branch derives the infinite-variance slow-variation and norming inputs. |
| Unequal finite block sums and their cumulative endpoints | `Probability/Process/RandomWalk/Path/Block/Law/Coordinates.lean`, `Probability/Process/RandomWalk/Path/Block/Law.lean`, `Probability/Process/RandomWalk/FunctionalLimit/FiniteDimensional/IndependentBlocks.lean` | Variable-length coordinate blocks give block-sum independence and joint convergence of unequal block sums and cumulative endpoints, including explicit centering shifts. `FunctionalLimit/Stable/FiniteDimensional.lean` identifies these endpoint laws for `HasStableClockIncrements` processes. The arbitrary-center theorem retains the center shift; the source FCLT applies its zero-center specialization. |
| Stable-clock endpoint identification | `Probability/Process/RandomWalk/FunctionalLimit/Stable/FiniteDimensional.lean` | The independent-block endpoint limit is identified with the endpoint vector of any process satisfying `HasStableClockIncrements`. A second theorem obtains the block spatial ratios from stable norming and positive limiting block-time lengths; the centering error remains explicit. The finite-dimensional result and stable random-walk `J₁` tightness are separate inputs to the generic path-law assembly below. |
| Arbitrary real-time finite-dimensional convergence for normalized step paths | `Probability/Process/RandomWalk/FunctionalLimit/Stable/PathFiniteDimensional.lean` | For every strictly increasing grid `0=t₀<⋯<tₘ≤1`, the theorem constructs the exact floor blocks `⌊ntⱼ⌋−⌊ntⱼ₋₁⌋`, proves their length ratios and divergence, derives their norming ratios from the stable domain-of-attraction theorem, and identifies path evaluations with block endpoints. The generic theorem keeps each block-center ratio explicit; its zero-center specialization removes that premise. `PathLimit/Source.lean` now applies this specialization under the uncentered scalar domain-of-attraction convention and joins it to the three source-specific tightness theorems. An arbitrary nonzero centering sequence still requires its own block-center estimate.
| Fixed-parameter limits and regular-variation transfer along a slowly growing diagonal | `Order/Filter/SlowDiagonal.lean`, `Analysis/Asymptotics/SlowDiagonal.lean`, and `RandomWalk/SmallDeviation/Mogulskii/Stable/Scale.lean` | The source-ordered diagonal preserves the fixed-parameter probability estimates and the regular-variation ratio while keeping the multiplier negligible relative to the norming. Its stable adapter proves the Lemma 4 scale transfer under the stated slow-variation and norming assumptions; the finite-partition probability estimates now consume this adapter. |
| Fixed-time evaluation, continuity times, and path-law identification | `Topology/Cadlag/Skorokhod/Evaluation.lean`, `MeasureTheory/MeasurableSpace/CadlagPath.lean`, `MeasureTheory/Measure/CadlagPath/ContinuityTimes.lean`, `MeasureTheory/Measure/CadlagPath/FiniteDimensional/Dense.lean`, `Probability/ConvergenceInDistribution/CadlagPath/FiniteDimensional.lean` | Mathlib supplies tight-family compactness (`Mathlib.MeasureTheory.Measure.Prokhorov`), the probability-measure almost-everywhere continuous-mapping theorem, and uniqueness of projective limits (`Mathlib.MeasureTheory.Constructions.Projective`). The repository-specific bridge uses these interfaces: after Prokhorov subsequence extraction, Fubini supplies a dense set of continuity times for that cluster law; the almost-everywhere continuous-mapping theorem identifies its finite grid laws, and projective uniqueness identifies the whole path law. The measure uniqueness argument is in `MeasureTheory`; its weak-convergence conclusion is in `Probability/ConvergenceInDistribution`. Thus tightness plus convergence on every strictly increasing finite grid starting at zero imply weak convergence on this local `J₁` path space. The direct theorem `ProbabilityMeasure.tendsto_of_tight_of_separatesPoints` is not applicable to raw time evaluations, since evaluation is not continuous at every path in the `J₁` topology.
| Generic path-space tightness and measure bounds | `MeasureTheory/Measure/CadlagPath/Tightness.lean`, `MeasureTheory/Measure/CadlagPath/RangeCover.lean`, `MeasureTheory/Measure/CadlagPath/Corridor/Weight.lean`, `MeasureTheory/Measure/ContinuousMap/Tightness/` | These estimates concern arbitrary measures on bundled path spaces. They do not require a stochastic-process law, so they live in `MeasureTheory`; random-walk and stable-process modules import them as applications. The separate recurrence lemma for arbitrary measurable sets is in `MeasureTheory/Measure/Recurrence/BlockBounds.lean`.
| Stability of partition oscillation under `J₁` perturbations | `Topology/Cadlag/Skorokhod/Oscillation/Partition/`, `Topology/Cadlag/Skorokhod/Compactness/`, `MeasureTheory/Measure/CadlagPath/Tightness.lean` | The finite oscillation partitions, compactness criteria, fixed-step path-law tightness, and generic probability tightness criterion are proved. `FunctionalLimit/Stable/Tightness.lean` proves asymptotic `J₁` tightness of normalized random-walk path laws for uncentered `0 < α < 1`, the source sine-centering at `α = 1`, and integrable centered increments for `1 < α < 2`, under the corresponding tail/norming hypotheses. `PathLimit/Source.lean` now joins each criterion to finite-grid convergence under the zero-center scalar domain-of-attraction convention and proves the corresponding stable path-law convergence. Nonzero scalar centering remains available through the generic theorem when a block-center estimate is supplied. |
| Endpoint-window Portmanteau transfer, conditional on a path limit | `Probability/Process/RandomWalk/FunctionalLimit/NormalizedStep/Endpoint.lean` | The open-corridor/open-endpoint lower bound uses Mathlib's open-set liminf theorem; the closed-corridor/closed-endpoint upper bound uses its closed-set limsup theorem. Neither requires a null-boundary assumption. The source-specific stable FCLT is now assembled in `FunctionalLimit/Stable/PathLimit/Source.lean`; endpoint estimates and corridor inner/outer approximations are separate inputs to the small-deviation proof. |
| Variable-length normalized block corridors | `Probability/Process/RandomWalk/FunctionalLimit/NormalizedStep/Block.lean`, `Probability/Process/RandomWalk/FunctionalLimit/Stable/PathLimit/Block.lean`, `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Corridor.lean` | The generic random-walk module handles independent step count and spatial scale and identifies open/closed path corridors with the corresponding finite horizontal-tube events. Its open lower and closed upper bounds need no boundary-nullity; the equality adapter uses Mathlib's null-frontier Portmanteau theorem. The stable block path-law limit is derived from F0, tightness, stable norming, and slow variation; `Stable/Corridor.lean` then derives the rounded scale ratio. Boundary-nullity remains an input only for equality of fixed-event probabilities. M2's open lower transfer needs no such input. |
| Fixed-time continuity of the stable target process | `Probability/Process/Stable/PathContinuity.lean` | Almost-sure continuity at every fixed positive time is proved for the stable target process. The current F0 path-law identification instead selects a dense continuity-time set for each weak cluster law, so this fixed-time result is a separate reusable property, not an unproved convergence input. |
| Hard-truncation and local block bounds | `Path/Truncation/`, `Path/Block/Law/Excursions.lean`, `FunctionalLimit/Stable/{BlockTail,Centering,StoppingTime}.lean`, `Distributions/Stable/Attraction/Norming/{Tail,UniformTail}.lean` | Truncated increments have finite moments without assuming moments of the original law. Under the stated tail regular variation and stable norming, the local one-block bound is proved once the appropriate centering-bias bound holds; source centering assumptions supply that bound in the three regimes `0 < α < 1`, `α = 1`, and `1 < α < 2`. Adjacent block and stopping-time excursion estimates provide the probabilistic input to stable `J₁` tightness, which `PathLimit/Source.lean` now combines with the zero-center scalar attraction input to prove the path-law limit. |
| Characteristic functions for the attraction hypothesis | `Probability/Sequence/IID/CharacteristicFunction.lean`, `Probability/Distributions/DomainOfAttraction/CharacteristicFunction.lean`, `Probability/Distributions/Stable/Attraction/`, `Probability/Distributions/CharacteristicFunction/Tauberian/SecondTail.lean` | The finite-sum characteristic-function formula, stable defect limits, inverse-Tauberian tail result for `0 < α < 2`, and the Gaussian normal-domain truncated-moment/norming branch are proved under the source centering assumptions. |
| Integer block-count arithmetic | `Analysis/Asymptotics/BlockScale.lean`; stable interface in `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Partition.lean` | floor length, quotient count, coverage bounds, and the `o(n)` coverage limit are general deterministic results. The stable file supplies definitions and delegates this arithmetic |
| Discrete block scale relations (Lemma 3/4 input) | `Analysis/Asymptotics/RegularVariation/`, `Distributions/Stable/Attraction/Norming/Inverse.lean`, `RandomWalk/SmallDeviation/Mogulskii/Stable/{Scale,Partition}.lean` | The rounded inverse and source-scale diagonal are proved under slow variation and stable norming. The finite-relative-time partition and variable-cell estimates are assembled for the current càdlàg step-path convention. |
| (3): `L*` | `Distributions/Moments/Truncated.lean`, `Distributions/Stable/Attraction/Normal/TruncatedMoment.lean`, `Analysis/Asymptotics/RegularVariation/` | The `0 < α < 2` truncated-moment ratio follows from the inverse-Tauberian tail theorem. At `α = 2`, Gaussian attraction supplies the slowly varying truncated second moment and quadratic norming, including the infinite-variance case. |
| (15)/(16): the factor `λ_n` | `Distributions/Stable/Attraction/Norming.lean` | `stableRateNormalization` (and its reciprocal `stableSmallDeviationRate`) |
| §1: classes `M₁`, `M₂`, `M₃`, and `M` and the corridor energy | `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/` for deterministic path classes; `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/` for the corridor cost; `Probability/Process/Path/PathClass/StepCorridor/Probability/` for event measurability and probability rates; `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/` for stable-process specializations | Path-set definitions and rate estimates have separate dependency layers. Stable-process M₂/M₃/M rates and random-walk path-class rates are proved for both the current right-continuous `S_n` path and the source `S_(n−1)` path. Arbitrary approximation targets have matching inner/outer rates without an automatic measurability claim; ordinary probability interfaces retain an explicit measurability premise. |
| Лемма 1 I: the constant `C = −C*` | `Probability/Process/Stable/SmallDeviation/EscapeRate.lean` and `EscapeRate/PathLaw/{Basic,Transfer}.lean` | The finite negative stable-process escape rate, translated/endpoint-constrained rates, and unit-interval path-law transfer are proved. |
| Лемма 2, Лемма 3: individual and gluing estimates | `Probability/Process/Stable/SmallDeviation/`, `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/`, `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Discrete/` | Stable-process Lemma 2 and exact M₂ step-corridor rates are proved. The random-walk finite-partition lower/upper estimates, endpoint-core gluing, source comparisons, and slow-diagonal assembly cover both endpoint conventions; the source last block uses its exact shortened length. |
| Теорема 2: single stable block | `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Rate.lean` | The stable-process M₂, M₃, and M rates are assembled. For an arbitrary `IsM` set, the event need not be measurable; inner and outer probabilities have matching rates. The ordinary probability API keeps its explicit null-measurability premise. |
| §3: partition, product bound, `(1−δ)`-shrink | `Probability/Process/RandomWalk/Path/Block/Partition/`, `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Partition.lean`, `Analysis/Asymptotics/SlowDiagonal.lean` | Balanced floor partitions, independent cell products, endpoint-core gluing, variable-cell rates, the source-ordered scale diagonal, and the source terminal-index adapter are assembled. |
| the two `ε`-approximations of a corridor | `Probability/Process/RandomWalk/Path/Corridor/{Basic,Energy}.lean` | present (`InOpenCorridorOn.of_shrunk`, `.relax`, `corridorEnergy_add_sub`, `corridorEnergy_sub_add`) |
| Later `α = 2` input | `Probability/Distributions/Stable/Attraction/Normal/`, `Probability/Process/RandomWalk/FunctionalLimit/Normal/`, `RandomWalk/SmallDeviation/Mogulskii/Gaussian/` | The zero-centered normal-domain branch includes infinite-variance truncated-moment asymptotics, quadratic norming, J₁ tightness/FCLT, and path-class rates. `Gaussian/SourcePathClass.lean` applies the explicit Brownian escape constant `−π²/8` to the source endpoint convention. |

## Current proof status

The stable-process M₂/M₃/M rates and random-walk path-class rates are assembled for both endpoint conventions. The deterministic terminal-left path map and its `D₀` domain are in `Topology/Cadlag/TerminalLeft.lean`; its Borel measurability is in `MeasureTheory/MeasurableSpace/CadlagPath/TerminalLeft.lean`. `RandomWalk/SmallDeviation/Mogulskii/SourcePath.lean` defines the source path ending at `S_(n−1)` and proves its exact finite strict-corridor event identity. `Stable/Discrete/SourcePartitionLimit.lean` proves its exact variable-horizon M₂ rate, then the source path-class adapters close M₃/M and the three exponent regimes. No rate is transferred through a merely `o(1)` probability error.

The source class `M` does not by itself ensure that an intermediate target is measurable. Stable-process and random-walk APIs therefore offer matching inner/outer probability rates for arbitrary `IsM` targets, while ordinary probability theorems keep an explicit measurability or null-measurability premise. The source-convention inner/outer adapter is in `Stable/Discrete/SourcePathClassInnerOuter.lean`.

The source endpoint and target class now agree at the domain level. `RelativeFiniteCorridorUnionApproximation` sandwiches a target only after intersecting both approximants with a path domain; `SourcePathClassRelative.lean` instantiates that domain as `terminalLeftPathSpace`. `BranchingProcessTest/Mogulskii/RelativeTerminalLeft.lean` constructs the original strict unit corridor as a relative target and applies the source theorem to it. Thus the missing item is no longer a relative-approximation interface. This test does not construct a stable process or prove that every paper-class target belongs to the relative class.

The raw random-walk assumptions still do not produce the reference stable process passed as `hX : IsStableLevyProcess ...` to the source rate theorem. The finite-dimensional convergence and path tightness results in the repository do not, by themselves, provide this witness: an existence proof must extract and identify a path-law limit without using an FCLT whose target already assumes that process. No such construction or all-time concatenation is currently in the Lean library. The original theorem's source assumptions therefore have not yet been reduced to an independently callable final interface.

The rescaling data in `Stable/Discrete/SourceInputs.lean` produce `d`, `q = d^(1/α)`, and the pushed-forward stable law. `HasStableProcessEscapeRate.spatialScale` now transports the path law by `f ↦ q f` and proves the corresponding escape-constant identity `C ↦ q^α C`. The source theorem still returns its rate information in a large uniqueness/conjunction package. A direct continuous-boundary-to-relative-approximation construction and its integral-energy identification have not been implemented. These are separate remaining application and interface tasks; they are not gaps in the proved finite-partition corridor rate.

The inverse-Tauberian theorem for `0 < α < 2`, the infinite-variance Gaussian normal-domain bridge at `α = 2`, and the explicit exponent-two escape constant `−π²/8` are formalized. The source endpoint adapters derive the unit-interval path law from the actual stable process, give ordinary probability rates with an explicit measurability premise, and give matching inner/outer rates for arbitrary `IsM` targets.

## Corrections to the block-scale interpretation

The implementation defines

```text
stableBlockLength α ν c a n = ⌊c · κν(a n)⌋₊
κν(u) = u^α / L*ν(u)
```

so the slowly varying factor is present in the block length.

The general ratio-limit interface is in `Analysis/Asymptotics/RegularVariation.lean`; compact-uniform convergence and sequential inverses are in `Analysis/Asymptotics/RegularVariation/`. A compact-uniform theorem states its eventual-monotonicity hypothesis explicitly. The generic inverse for `u²/V(u)` uses monotonicity of `V` and does not require monotonicity of the quotient. `Norming/Inverse.lean` applies this result to truncated second moments and stable floor blocks. The integral Karamata theorem is in `Analysis/Asymptotics/RegularVariation/Integral.lean`; it proves product and reciprocal closure, a Potter upper bound when the regularly varying function is eventually nondecreasing, and `stableScaleTime_isRegularlyVaryingAtTop`. The truncated-moment theorem applies Karamata to `Tν(√t)` and proves `Hν(u)/(u²Tν(u)) → α/(2−α)` for a regularly varying two-sided tail. Consequently, `stableSlowVariation_isSlowlyVarying_of_regularlyVaryingTail` establishes slow variation of `L*ν` under that tail hypothesis. The inverse cosine-kernel work and the probability-facing Tauberian bridge prove the defect-to-tail implication for `0<α<2`, including nonmonotone Potter control, the kernel integral limit, transfer from the symmetrized law, and the truncated-moment ratio. The infinite-variance `α=2` normal-attraction implication and path-level stable FCLT are also formalized. The terminal-left source path now has its exact M₂ rate and the assembled M₃/M path-class interfaces.

The code parameter `aₙ` is the corridor scale; the symbol `α` is the stable index. The separate norming sequence `b` compares block lengths with the horizon. The finite relative-time partition and rate sums are formalized for both the current step-path convention and the paper's terminal-index convention.

## The inverse norming function

`κν(u) = u ^ α / L*ν(u)` — the function `B*` of (4), whose asymptotic inverse is the norming `B`, and whose regular variation is used in (43) — is `stableScaleTime` in `Distributions/Stable/Attraction/Norming.lean`. The theorem `stableRateNormalization_eq_natCast_div_stableScaleTime` expresses `λ n = n / κν(aₙ)`.

The formal block length uses corridor scale `aₙ` and includes `L*ν(aₙ)` in its denominator. Under `0 < α ≤ 2`, slow variation of `L*ν`, and stable norming `B`, `IsStableNorming.tendsto_floorBlock_normalization_div_scale` proves `B_{⌊c κν(aₙ)⌋₊}/aₙ → c^(1/α)`. The normal-domain theorem supplies the α=2 slow-variation and norming hypotheses, including infinite variance. Both discrete endpoint conventions consume the resulting variable-block estimates; the source convention shortens only the last block by one increment exactly.

## Finite-prefix API

The project uses Mathlib's Fin.partialSum as the canonical cumulative-sum operator. The former project definitions blockPartialSums and finiteIncrementSums have been removed. The pinned Mathlib version has no `Fin.partialSum_differences` theorem, so Algebra/BigOperators/PartialSum.lean proves the generic telescope identity used by process and block-path results. Variable-length coordinate-block independence lives in Probability/Process/RandomWalk/Path/Block/Law/Coordinates.lean; sums are measurable images in Law.lean.
