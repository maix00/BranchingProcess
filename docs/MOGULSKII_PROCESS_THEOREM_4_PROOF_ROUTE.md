# Mogulskii Theorem 4: process-level proof route and missing interfaces

## Scope and source statement

This note audits the process theorem in §5 of Mogul'skii, “Small deviations
in the sample function space” ([1974 article record and full text](https://www.mathnet.ru/eng/tvp3978), English translation in *Theory of Probability and its Applications* 19 (1975), 726–736).
The theorem concerns a homogeneous process with independent increments
`ξ(t)`, `t ≥ 0`, with almost-surely right-continuous paths and zero mean when
the mean exists. Its one-time laws are in the strict stable domain of
attraction with index `0 < α < 2`; the source also assumes
`B*(B(n)) / n → 1`, where

```text
L*(u) = u^(α - 2) ∫_{[-u,u]} z² ν(dz),
B*(u) = u^α / L*(u),
```

and `ν` is the law of a unit-time increment. For `x(n) → ∞` with
`x(n) / B(n) → 0`, Theorem 4 asserts, for the same source class `A` and
functional `Hα` as Theorem 1,

```text
log P(t ↦ ξ(n t) / x(n) ∈ G)
  ~ C Hα(G) n x(n)^(-α) L*(x(n)),
```

with the same coefficient `C < 0` as Theorem 1. The path convention is the
paper's `D(0,1)` convention: the value at the terminal time is the left limit.
In the repository's normalization, `C = 2^α C₀`, where `C₀` is the stable
unit-range escape coefficient. The exact event convention and `Hα` definition
remain those recorded in `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Rate/PROOF_ROUTE.md`.

## Existing interfaces that can be reused

- `Probability/Process/Levy/Basic.lean` defines `IsLevyProcess`, stationary
  increments, independent increments, and almost-sure càdlàg paths.
- `Probability/Process/IndepIncrements/FiniteDimensional.lean` derives finite
  dimensional laws from independent increments, and
  `Probability/Process/IndepIncrements/DisjointPaths.lean` gives independence
  of paths on adjacent intervals. These are the right inputs for exact
  block-factorization arguments.
- `Probability/Process/Path/Cadlag/MeasurableMap.lean` constructs measurable
  càdlàg path realizations. `Topology/Cadlag/TerminalLeft.lean` provides the
  deterministic terminal-left map and its `D₀` domain;
  `MeasureTheory/MeasurableSpace/CadlagPath/TerminalLeft.lean` proves its
  Borel measurability.
- The stable reference process already has a unit-interval path law and a
  stable-process `M₂` path-class rate. See
  `Probability/Process/Stable/PathLaw/UnitInterval.lean`,
  `Probability/Process/Stable/SmallDeviation/EscapeRate/PathLaw.lean`, and
  `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Partition/Stable.lean`.
  The stable range, endpoint, and inner/outer APIs provide the limit-model
  estimates needed in a block squeeze.
- The random-walk stable-domain functional limit and `M₂` rates are already
  available in `Probability/Process/RandomWalk/FunctionalLimit/Stable/` and
  `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/Discrete/`.
  They concern the step path made from unit-time increments, not the full
  continuous-time path `t ↦ ξ(n t)`.
- The generic Skorokhod tightness and finite-grid identification criteria,
  together with the relative `M₃`/`M` rate adapters, can be reused after the
  missing process-level bounds have been proved.

## Exact missing interfaces

The current APIs do not compose to Theorem 4. The missing pieces are:

1. **A process-level stable functional limit.** There is no theorem deriving
   weak convergence in `J₁` of the full path laws
   `Law(t ↦ ξ(T t) / b(T))` to the stable Lévy path law from the scalar
   stable-domain assumption and `IsLevyProcess`. The current stable path-limit
   theorems take an i.i.d. increment law and prove convergence of its
   piecewise-constant random-walk paths. That does not identify the law of
   `ξ(T·)`: fluctuations and jumps inside unit-time intervals are omitted.
   The finite-dimensional part can use stationary independent increments and
   the scalar domain-of-attraction result. The missing analytic input is
   `J₁` tightness for the full rescaled Lévy paths, including control of
   within-interval oscillations.
2. **A scalar-to-process norming bridge.** The source hypothesis is stated
   for `ξ(B(n)) / B(n)` at real times and includes
   `B*(B(n)) / n → 1`. The existing `IsStableNorming` and inverse-norming
   interfaces are formulated for the law of one i.i.d. increment and natural
   time indices. A verified bridge must identify the unit-time increment law
   `ν = Law(ξ(1) - ξ(0))`, recover the required norming/regular variation
   from the source's continuous-time assumption, and relate real block times
   `B*(A x)` to that norming. This conversion must retain the centering
   convention, especially at `α = 1`.
3. **A full-path one-block squeeze for the nonstable process.** The stable
   process `M₂` rate is a theorem about the limiting stable process; the
   random-walk `M₂` rate is about the discrete skeleton. Neither gives the
   probability that the original process path stays in a corridor throughout
   a long block, with an endpoint in a prescribed core. The missing lemma
   must transfer open inner and closed outer full-path corridors through the
   process-level `J₁` limit, then take the stable small-width limit. It must
   provide both the range upper estimate and the endpoint-core lower estimate
   needed for `M₂` block concatenation.
4. **The paper's path regularity and terminal endpoint.** The paper states
   almost-sure right continuity, whereas `IsLevyProcess` asks for
   almost-sure càdlàg paths. Either prove left limits from the stated
   independent/stationary-increment and continuity assumptions, or expose the
   necessary càdlàg hypothesis explicitly. The `D₀` endpoint convention also
   needs a proof that the process has no jump at each deterministic terminal
   time used in the block argument, or an exact terminal-left path-law
   formulation that avoids assuming this silently.

The integer skeleton cannot close these gaps by asserting that its path event
differs from the full-process event by `o(1)`. The target probability is
exponentially small at scale
`ρ(n) = n x(n)^(-α) L*(x(n))`; an additive `o(1)` error can be much larger than
the probability itself. In addition, a unit-block path excursion can have
probability of order `L*(x) x^(-α)`, which contributes at the target
exponential scale after `n` blocks.

## Non-circular proof dependency order

1. **Package the process input.** From stationary increments, define the
   common unit-time increment law `ν`; derive measurability of every
   increment and the exact finite-grid product law from
   `HasIndepIncrements`. Build the time-restricted path law using the
   existing càdlàg path-map API, then apply the terminal-left map to match
   `D₀`.
2. **Formalize the continuous-time stable functional limit.** Let `T → ∞`
   and let `b(T)` be the stable norming. Prove finite-dimensional convergence
   from the increment laws. Prove full `J₁` tightness from direct
   Lévy-process range and oscillation bounds (or an independently proved
   comparison with the skeleton that controls path oscillations at the
   probability level required by tightness). Apply the existing generic
   tightness-plus-finite-grid identification theorem to obtain convergence
   to the stable path law. This step proves weak convergence only; it does
   not invoke Theorem 4 or a small-deviation rate.
3. **Derive one-block bounds at a fixed `A`.** For `A > 0`, take block time
   `T_x(A) = B*(A x)`. The norming inverse gives
   `b(T_x(A)) / (A x) → 1`. Apply the process functional limit to
   `ξ(T_x(A)·)/(A x)`. Use Portmanteau on an open inner corridor and a closed
   outer range corridor. Apply the already proved stable-process escape and
   endpoint-core rates to these two limiting events. Keep both bounds as
   logarithmic inequalities; do not claim probability convergence unless a
   boundary-null result has been established.
4. **Assemble `M₂` blocks with exact independence.** For fixed `A`, partition
   the full time interval into complete blocks of length `T_{x(n)}(A)` and a
   terminal remainder. For the upper bound, a path in the target corridor
   forces each translated block path to satisfy a range event. For the lower
   bound, impose inner block corridors and endpoint-core events that imply
   the complete path belongs to the target. Use independent adjacent path
   increments to factor these events exactly. Handle the terminal remainder
   by the same corridor/core inequalities, not an additive probability
   approximation.
5. **Pass from `M₂` to the source classes.** Use the existing deterministic
   finite partition decomposition to evaluate `Hα` and sum the block rates.
   Then use the existing finite-union and inner/outer `M₃`/`M` adapters,
   preserving the source's strict membership and measurability assumptions.
6. **Choose a slow diagonal and identify the coefficient.** First take
   `n → ∞` for fixed `A`, then `A → ∞` using the stable escape rate. Choose
   `A = A(n) → ∞` slowly enough that
   `A(n) x(n) / B(n) → 0` and every fixed-`A` estimate remains eventual.
   Regular variation gives
   `B*(A(n) x(n)) / B*(x(n)) ~ A(n)^α`; hence the number of complete blocks
   times the one-block rate is asymptotic to
   `C Hα(G) ρ(n)`. The order of these limits must remain explicit.

## Concrete model to use as an eventual application test

A useful nonstable test case is a symmetric compound-Poisson Lévy process
whose jump distribution has a regularly varying tail of index `-α`, for
`0 < α < 2`. Its unit-time increment law is in the symmetric strictly
`α`-stable domain of attraction, its mean is zero whenever it exists, and
`0 < Fα(0) < 1`. Once the four missing interfaces above exist, instantiate
Theorem 4 with a simple finite-step corridor from `M₂`, then check the
coefficient against the stable unit-range escape API. This is a test plan,
not a claim that the compound-Poisson example has already been constructed
or verified in Lean.

## Status

Theorem 4 is **not implemented**. Existing independent-increment,
càdlàg-path, stable-process escape, and random-walk stable-domain APIs cover
parts of the dependency chain, but the full-process functional limit and its
full-path one-block squeeze are not present. The next proof package should
implement and verify those two interfaces before adding a theorem wrapper;
the source theorem itself should not be introduced with an unproved path
convergence or a skeleton-probability shortcut.
