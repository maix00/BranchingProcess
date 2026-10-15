# Formalization checklist

The statuses below refer to kernel-checked Lean proofs in this repository.
The LaTeX proof is not counted as a Lean proof.

## Work-package status index

## Integrated work packages for Theorems 1.1 and 1.2 (2026-10-11 audit)

The theorem proofs are being advanced as dependency packages rather than by
patching isolated gaps. The final theorem declarations must keep the paper's
assumptions individually visible: `ψ(0) > 0`, nonempty offspring almost
surely, `ψ(1) = 0`, `ψ'(1) = 0`, finite spine variance, finite cross weight,
the first and fourth positive moments of the leftmost step, and, only for the
zero-start right tail, its positive exponential moment. Existing abstractions
such as `Potential`, `StepLaw`, and the individual `Has…` predicates remain
valid interfaces; no bundled assumption structure is to appear in a final
theorem. A right-oriented theorem uses the corresponding right-side
conditions by formulating the conclusion through `OrderDual`, while keeping
the same offspring law; no reflected-law or symmetry assumption is intended.

| Package | Status after audit | Deliverable and owner |
|---|---|---|
| API0: model and assumption boundary | **Ownership audit mostly clear; final theorem API open** | General/random mechanisms stay in `Selection/`; deterministic first-`N` results stay in `Selection/NSelection/`; generic killed causal populations stay in `Population/Processes/Causal/`. Keep `Potential` and separate assumption predicates. The final adapters must expose the paper's assumptions flatly. Formulate the right-oriented result through `OrderDual` using the same law's right-side conditions; when the corresponding left and right condition families hold, derive both conclusions. No offspring-law reflection symmetry is assumed. |
| T11-R+: positive-start right tail, `0 < a < 1` | **Actual long-corridor second moment and drawdown bound proved; quantitative survival composition open** | The logarithmic tube parameters, one-generation tube estimates, first-moment capacity overflow bound, and capacity-to-first-`N` spatial injection exist. `Spine/Tube/ActualMRCAContribution.lean` identifies each positive-depth contribution with its conditional-prefix integral. `AffineCorridorPairBound.lean` sums the actual ordered distinct-address pairs over all MRCA depths and applies the drawdown estimate; `AffineCorridorSecondMoment.lean` gives the resulting exact second-moment identity. `RightTailKilledCapacity.measure_rightTailPositiveAFirstStageLowCount_le_of_affineCorridorDrawdown` consumes this bound internally, so callers do not assume a second moment. Still open is a quantitative lower bound for the first-stage tilted corridor probability from the paper's finite-variance/Mogulskii assumptions, its conversion by the second-moment argument to a one-root survival power bound, the shifted-root second-stage survival estimate, and the final capacity-failure composition. Do not label the pair estimate as equation (4.15): (4.15) is the right-tail probability target. The surviving-population branch is a prerequisite to the `a = 1` endpoint package. |
| T11-R1: endpoint `a = 1` | **Open adapter** | Choose `b < 1` close to `1`, use initial-root monotonicity, and transfer T11-R+ to the `a = 1` threshold. Depends on T11-R+. |
| T11-R0: zero-start right tail | **Partial; main probabilistic bridge open** | Reuse the same pre-sampled tree, generation-observable completion times `σᵢ`, reserve-lineage freshness, and fixed-horizon endpoint coupling. Still prove the thesis candidate-source comparison, finite-time growth success and spatial bounds (including the failure-conditioned displacement transform), and random remaining-horizon combination with T11-R+. Depends on T11-R+ and the existing `Restart/RootedTrial/` interfaces. |
| T11-L: endpoint sublevel (4.16) | **Open; the obsolete raw-range-rate adapter chain has been removed** | The deleted `EndpointDeviation/PolynomialEndpointSublevel.lean` chain depended on the removed raw range-rate theorem. Its finite-root, countable-root, and `L²` downstream adapters were removed with it. Rebuild this package after the finite-variance tilted-tube lower bound is formalized and connected to the branching estimate. |
| T11-M: endpoint fourth moment and `L²` closure | **Both endpoint fourth-moment sides proved; `L²` assembly open** | `EndpointDeviation/Endpoint/Moments.lean` proves `E[(M⁻)^4] ≤ 2048(1 + log(m)^4)` from the paper assumptions. `EndpointMinimumAddress.lean` and `EndpointMinimumLineage.lean` give a measurable depth-correct minimizing address and compare the next selected minimum to its fresh slot-zero increment; `EndpointDeviation/Endpoint/PositiveMoments.lean` supplies the predictable fresh-step moment law. `EndpointDeviation/Endpoint/PositiveMomentClosure.lean` proves the positive endpoint bound `∫(M⁺)^4 ≤ n^4 E[(Ξ₁)₊^4]`, using only the paper boundary, nonempty-offspring, and fourth-moment conditions. The remaining task is to assemble these bounds with the common countable-root two-sided tail estimates through `L2FromPolynomialTails` (including T11-R0 at `a = 0`). The varying-measure `TailExpectation` result assumes a uniform centered fourth-moment bound and is not a substitute for the paper's logarithmically growing fourth-moment estimate. |
| T11: final trajectory theorem | **Open** | Assemble the preceding packages into the exact flat theorem statement and its `L²` conclusion. The zero-start clause has the paper's extra positive exponential-moment assumption only. State the right-oriented counterpart with the corresponding `OrderDual`/right-side conditions; no offspring-law invariance is assumed. |
| T12-K: speed existence | **Exact-`N` a.s./`L¹` result and smaller-start capacity hit with fresh-field law proved; speed transfer open** | The repository's `Probability.Ergodic.Kingman` implementation supplies the random Kingman theorem; Mathlib's `Analysis.Subadditive` supplies the deterministic Fekete input. `AsymptoticSpeed/KingmanInterface.lean` derives uniform integrability from the one-generation envelope and IID generation coordinates, then proves `L¹` convergence by Vitali for the measurable repaired representative. A flat-`StepLaw` wrapper gives a.s. speed and `L¹` convergence for exactly `N` initial particles under the paper's assumptions. `AsymptoticSpeed/InitialPopulation.lean` proves frequent rank-zero split events in the pre-sampled environment, deterministic saturation from frequent strict growth, and invariance under changing initial positions. `AsymptoticSpeed/InitialPopulation/Hitting.lean` chooses a predictable address from the actual current selected population; its fresh offspring marks are i.i.d. with law `μ`. Supercriticality gives positive split probability, and frequent splits plus nonempty offspring make the actual population hit capacity `N` almost surely. `AsymptoticSpeed/InitialPopulation/FreshField.lean` proves the capacity time is a stopping time, the selected `N` roots form a stopped-measurable vector, and their descendant fields have the product `N`-root law after the finite hit; the a.s. hitting result removes the finite-time restriction. The remaining bridge is the pathwise identification of the post-hit selected population with the exact-`N` trajectory. `RepeatedTrials.lean` remains a generic independent-trial interface, not the proof of this actual-process hit.
| T12-L/U: speed lower/upper bounds | **Open applications** | The lower bound consumes T11-L (and the endpoint expectation estimate); the upper bound consumes T11-R+ and T11-R0 together with the restart/selection comparison. Existing deterministic squeeze and many-to-one components are inputs, not these probability bounds. |
| T12: final speed formula | **Open** | Feed both probabilistic speed bounds and the speed-existence/expectation package into `AsymptoticSpeed/Asymptotics.lean` and state the paper's exact theorem with flat assumptions. |

Dependency order:

```text
existing spine/drawdown/selection interfaces
        ├── T11-L paper-assumption adapter ───────────┐
        ├── T11-R+ corridor survival + capacity ── T11-R1
        │                         └─────────────── T11-R0 restart
        └── endpoint moment/selector chain ────────────┤
                   T11-L + T11-R+/R0 + moments ──> T11-M L² closure
                                                        │
                                                T11 trajectory theorem
                                                        │
existing Kingman core ──> T12-K speed existence ──────┤
                                  T11 + T12-K ──> T12-L/U ──> T12 final formula
```

The package boundaries follow the library ownership map: random-walk corridor
probability estimates remain in `Probability/Process/RandomWalk/`; BRW path
counts and their MRCA decomposition live in `Probability/BranchingRandomWalk/Spine/Path/`;
affine-tube applications and their fixed-depth second-moment bounds live in
`Probability/BranchingRandomWalk/Spine/Tube/`; generic killed populations
remain in `Probability/BranchingRandomWalk/Population/`; and first-`N` endpoint
and speed applications remain in `Probability/BranchingRandomWalk/Selection/NSelection/`.
`Selection/` is not used as a synonym for deterministic first-`N` selection.

This index separates reusable infrastructure from the still-open theorem
applications. “Done” means the stated interface is proved; it does not imply
that a later theorem which consumes it has also been proved.

| Package | Status | Current boundary |
|---|---|---|
| Q0 | **Done** | Variable-length coordinate blocks are the independence base; measurable finite sums derive block-sum independence, and endpoint vectors use `Fin.partialSum`. |
| Q1 | **Done** | `FiniteDimensionalIndependentBlocks.lean` exercises the zero-, one-, and two-block cases, unequal lengths, shifts, and the four guarded declarations. |
| DOC0 | **Done (documentation scope only)** | This checklist and the stable mapping record the source terminal convention, inner/outer probability semantics, Gaussian constant, module ownership, and verification boundaries. “Done” here means the documentation package is maintained; it does not imply that theorem applications listed as open below are proved. |
| RV0 | **Done under the stated attraction and norming hypotheses** | The inverse-Tauberian route proves two-sided tail regular variation and the truncated-moment ratio for `0 < α < 2`. The Gaussian branch derives the infinite-variance truncated-moment asymptotics and quadratic norming; the rounded block inverse uses slow variation and `IsStableNorming`. |
| T0 | **Done under the stated source assumptions** | Hard truncations have finite moments without global moment assumptions; the local bias and excursion bounds are supplied for the three source centering regimes under their respective tail, norming, and centering hypotheses. |
| J0/J1 | **Done** | The deterministic `J₁` compactness/tightness criteria and stable random-walk path-law tightness are proved for the three source centering regimes. |
| T1 | **Done under the stated source assumptions** | Stable tail, norming, and centering hypotheses yield local block-excursion bounds and the multiscale oscillation input used by J1 tightness. |
| F0 | **Done under zero-center scalar attraction and the stated source tightness hypotheses** | Unequal-block finite-dimensional convergence, stable endpoint identification, source-regime J₁ tightness, fixed-time evaluation Borel measurability, and dense-coordinate path-law identification are connected. `FunctionalLimit/Stable/PathFiniteDimensional.lean` keeps the block-center ratios explicit for arbitrary centering and has a zero-center specialization. `FunctionalLimit/Stable/PathLimit/Source.lean` combines that specialization with the three proved tightness regimes and yields stable path-law convergence for `0 < α < 1`, `α = 1`, and `1 < α < 2`. At index one, the sine-centering assumption supplies the tightness estimate; the scalar attraction input is explicitly zero-centered. The generic nonzero-center FCLT still requires a block-center limit. |
| M0 | **Done** | `NormalizedStep/Endpoint.lean` transfers an assumed `J₁` functional limit to the source bounds: open corridor plus open endpoint gives a liminf lower bound, and closed corridor plus closed endpoint gives a limsup upper bound. These are the Mathlib open-set and closed-set Portmanteau implications and require no boundary-nullity. F0 now supplies the stable path-law limit under its stated scalar-attraction and tightness hypotheses. Boundary-nullity is required only by the distinct equality-limit adapter for a fixed event; the small-deviation proof may instead use the separate open lower and closed upper bounds. |
| M1 | **Conditional adapter done** | `Stable/Corridor.lean` derives the stable one-block corridor probability limit from a variable-length `J₁` block-path limit, eventual scale/block positivity, and a null-boundary hypothesis. `FunctionalLimit/Stable/PathLimit/Block.lean` transfers the F0 limit to variable block lengths and spatial scales; `Stable/Corridor.lean` derives the needed rounded-block ratio under stable norming and slow variation. Boundary-nullity remains necessary for equality of probabilities of a fixed corridor event. The open lower and closed upper Portmanteau bounds used separately by small-deviation estimates do not require it. |
| M2 | **Done, including the paper's terminal convention** | Stable-process M₂ rates and the current càdlàg random-walk rate are proved. `Stable/RandomWalkBounds/Source/PartitionLimit.lean` proves the exact variable-horizon rate for the source path ending at `S_(n−1)`; its last block has length `n−1−⌊nt_{m−1}⌋`, and no `o(1)` probability transfer is used. |
| M3 | **Done for both path conventions** | The generic approximation squeeze and stable-process rates give matching inner/outer rates for arbitrary `IsM`. The source-path adapters in `Stable/RandomWalkBounds/Source/PathClassRate.lean`, `Stable/RandomWalkBounds/Source/PathClassRegimes.lean`, and `Stable/RandomWalkBounds/Source/PathClassInnerOuter.lean` extend this to the paper's endpoint convention without inferring measurability from energy approximation. Ordinary probability rates retain an explicit measurability premise. |
| A2 | **Raw-source rate integrated; focused build and axiom audit pass** | `Normal/TruncatedMoment.lean` derives the infinite-variance truncated-moment asymptotics and quadratic norming; normal-domain `J₁` tightness is proved without a finite-second-moment premise. `FromIncrementLaw/NormalDomain.lean` constructs the normalized Gaussian path-law/escape input internally from zero-centered attraction to any nondegenerate Gaussian limit, then proves finite-corridor and relative path-class rates. `FromIncrementLaw/NormalContinuousBoundary.lean` exposes the raw-input terminal probability rate with the universal normalized escape constant `−π²/8`; it needs no `IsBrownianReal` witness or moment premise. The integrated `FromIncrementLawRates.lean` test builds and all 16 named declarations pass the transitive axiom allowlist check. The separate `Gaussian/SourcePathClass.lean` adapter remains conditional on a Brownian witness and is not used by this raw-source route. |
| C0 | **Partial: fixed finite-horizon endpoint/fresh-field law and finite-slot moment recursions verified; causal restart comparison open** | `Restart/FirstSplit.lean` proves the raw first split `τ` is one-generation look-ahead, the observable completion `σ = τ + 1` is a stopping time, and finite first splits have a singleton parent with at least two distinct selected siblings; empty and arbitrary finite offspring families are allowed. `Restart/FirstSplit/BranchingProperty.lean` factors selected sibling subtrees on the finite stopped cell. `Genealogy/Exploration/RootIndexed/StoppingSubtrees/Vector/Factorization.lean` extends stopped subtree-vector factorization to arbitrary root-indexed fields and selector ranges. `Restart/RootedTrial/Reserve/Lineage.lean` applies this to the first two selected reserve siblings at finite `σᵢ`, proving their joint descendant field has the product branching law independently of observable stopped-past events. `Restart/RootedTrial/FiniteSplitCompletion.lean` derives finite split completion from nonempty selected offspring a.s. and positive split probability; `RestartSiblingTrial.lean` contains the concrete `GoodSplit` instantiation with the nonempty and supercritical assumptions passed separately. `Restart/Trial.lean` proves observability and the conditional L¹ failure estimate for a first growth candidate along a pre-sampled reserve lineage. `Restart/RootedTrial/Reserve/Causal.lean` defines generation-enabled, fixed-start cap-stopped candidates on one pre-sampled reserve spine and packages them with the reserve singleton as an adapted, parent-closed source. `Restart/RootedTrial/Coupling.lean` proves stopped-domain measurability and fresh-field factorization for actual rank-installed endpoint roots, the joint law with stopped-measurable endpoint positions, and transfer to the first-`N` population at every fixed finite horizon. `RootedTrial/FiniteSlot/Moments.lean` proves the finite-slot conditional second-moment formula and unconditional one-step first- and second-moment recursions under the derived capacity-two bound; it adds no branching-law moment assumption. The endpoint-specific `selectedReserveSpineRestartEndpointPopulation_law_on_finite` composes these components for the thesis reserve endpoint. This is a fixed-horizon result and gives no random remaining-horizon law. Still open for the theorem instance: identify the causal candidate source with the actual restarted population/frontier, prove freshness of each later reserve candidate against the actual explored-coordinate domain, derive the required finite-time candidate-success and spatial estimates from the theorem hypotheses, and close the restarted-population comparison.

## Measure convolution powers

`MeasureTheory/Measure/Convolution/Power.lean` defines `Measure.convPower`.
Its rotation theorem uses Mathlib's convolution associativity and Dirac unit
laws; it does not assume commutativity. Random-walk callers use this single
recursive definition, with probability and S-finiteness instances.

## Sequence filtrations and IID stopping-time blocks

`Combinatorics/Sequence/Block.lean` defines finite coordinate blocks without
process semantics. `Probability/Sequence/Block.lean` proves their
measurability, and `Probability/Sequence/Filtration.lean` defines the generic
`sequencePrefix` and `sequencePrefixFiltration`, including adaptedness,
coordinate measurability, and equality with the prefix-map comap. The IID
filtration module proves that any coordinate of an independent family after
the prefix is independent of its prefix sigma-algebra. It reuses Mathlib's
`iIndepFun.iIndep` and `indep_iSup_of_disjoint`; the pinned Mathlib revision
does not provide a more specialized prefix-filtration theorem.

`Probability/Sequence/IID/StoppingTime.lean` proves exact factorization on
each finite stopping-time cell for every measurable event of a finite future
block, then sums cells for bounded stopping times and derives the corresponding
upper bound for arbitrary discrete stopping times. These are generic sequence
results and do not assume additive increments or branching. The
`Probability/Process/RandomWalk/Path/Filtration.lean` adapter now contains only
random-walk consequences: positions are adapted to the generic sequence
filtration, and the finite increment prefix is independent of a following
block sum under the canonical IID law.

`Probability/Process/RandomWalk/Path/Block/Law/FirstCrossing.lean` proves
that the first absolute partial-sum exceedance time is a stopping time, that
crossing by a finite horizon agrees with the corresponding finite-prefix
excursion when the threshold is positive, and that this initial excursion
event factors exactly from a fresh finite excursion after the first crossing.
This is an event-level restart identity for IID increments; it does not assert
that a general two-sided path-modulus event is such a product event.

## Mogulskii small-deviation proof

The stable-process and random-walk rate chains are formalized for both the
repository's right-continuous step-path convention (terminal value `S_n`) and
the original paper's convention (terminal value `S_(n−1)`). The source
convention is a separate measurable path transform, and its discrete rate uses
the exact variable-length last block. Intermediate rate adapters accept a
stable-process witness `hX`; the tested `FromIncrementLaw/` public theorems construct
that witness internally from the stated raw domain-of-attraction assumptions.

### Lemmas applying the path-rate theorem: compiled numbering and proof order

The current `main.tex` PDF was compiled to check theorem counters and labels;
the strings in `\label{...}` are keys, not displayed numbers. Lemma 3.1 is in
`contents/part-1-eng.tex`; Lemmas 3.2–3.5 continue in `contents/part-2-eng.tex`.
The order here follows the displayed PDF numbers.

| PDF number | TeX label key | Paper statement and dependency | Lean status |
|---|---|---|---|
| 3.1(i) | `lemma:mogulskii-cal` | For each real width `Δ>0` and integer time horizon `L_Δ` with `L_Δ/Δ²→∞`, the horizontal-tube probability has rate `−π²σ²/2`. | **Formalized for integer widths.** `FromIncrementLaw/HorizontalTube.lean` proves the rate for `L:ℕ→ℕ`, identifying the event with the terminal-left source path convention and squeezing the closed tube between inward and outward strict corridors. The paper proof uses the same interpolation for positive real widths, which are needed for the local widths `Δ(k)` in part 4. The inverse-scale and width-monotonicity results remain Lean infrastructure; the revised paper proof does not require them as separate lemmas. |
| 3.1(ii) | `lemma:mogulskii-cal` | Under the same width-time relation, for fixed `0<u<v<1` and endpoint functions with `v₁(Δ)≤u<v≤v₂(Δ)` eventually, the tube probability with terminal value in `[(v₁(Δ)−a)Δ,(v₂(Δ)−a)Δ]` has rate `−π²σ²/2`. | **Formalized for integer widths.** `centeredFiniteVariance_endpointWindowProbabilityRate` uses the source path ending at `S_(n−1)`, the terminal-jump corridor with energy `H₂=σ²`, and the squeeze between that corridor probability and the tube probability from part (i). Its Lean width parameter is natural-valued; the paper statement also allows positive real widths. |
| 3.2 | `lemma:4.1` | Horizontal-tube upper bound `exp(uΔ^v − dL/Δ²)` for arbitrary `u,v>0`, and the coefficient-one specialization. The proof uses the closed-tube Mogul'skii rate, an equal partition to select one fixed corridor, iteration over full blocks, and a remainder estimate. | **Formalized.** `Mogulskii/RandomWalkBounds/HorizontalTubeUpper.lean` proves the centered-tube bounds `horizontalTubeProbability_le_exp_of_finiteVariance_withRemainder` and `horizontalTubeProbability_le_exp_of_finiteVariance`, and the corresponding translated-interval bounds for IID partial sums. The input rate is the closed horizontal-tube form of Mogul'skii, Theorem 3, Section 4, p. 764. |
| 3.3 | `lemma:2.3` | No-large-drop plus endpoint bound. Its proof uses the 3.2 horizontal-tube estimate for each nonjump block. | **Formalized.** `Drawdown/Upper.lean` proves `measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance`: for a centered law of variance `σ² ∈ (0,∞)`, every `c>0` and `0<d<π²σ²/2` admit one `Δ₀≥1` such that the estimate holds for all `Δ≥Δ₀` and `L≥Δ^(2+c)`. The proof follows Wang Yiyang, *Asymptotic speed of the N-branching random walk with infinite offspring*, Chapter 3, Lemma 3.3, using the rounded running maximum, conditional block estimates, and jump-pattern union. |
| 3.4 | `lemma:4.2` | Small-drift tilted-tube upper bound. The proof invokes 3.3 at the complete-block estimate, iterates blocks by the Markov property, and absorbs the remainder into `Δ^v`. | **Formalized.** `DriftedTube/FiniteVarianceUpper.lean` proves `exists_driftedTubeProbability_le_exp_of_finiteVariance`: the short-horizon case uses probability at most one; the long-horizon case follows the equal-length block decomposition, conditional-expectation iteration, and final-remainder estimate from Wang Yiyang, Chapter 3, Lemma 3.4. |
| 3.5 | `lemma:4.3` | Tilted-tube lower bound with either endpoint window. The proof has a diffusive entrance stage, then a staircase of horizontal sub-tubes; Lemma 3.1(ii) supplies one-block endpoint-window rates, and common narrowed-tube events give the uniform block bounds used in the reverse Markov product. | **Partial.** `DriftedTube/FiniteVarianceLower.lean` proves the integer-width block bound, spatial-bin coverage, central-window geometry, and deterministic real-width transfer. `Brownian/Meander/Corridor.lean`, `Brownian/Bessel/{ThreeDimensional,Support}.lean`, and `Brownian/Meander/{Imhof,Support}.lean` construct the radial three-dimensional path law and Imhof tilt and prove positive corridor mass from Brownian path support. `FunctionalLimit/Conditioned/{Meander,Survival,Transition}.lean` formalize the Appendix A.2 open meander corridor and its Portmanteau consequence from explicit conditioned invariance and support inputs, the survival-conditioned finite path, the exact finite-grid event $D_{n,\Delta}$, and an eventual positive lower bound for $\mathbb P(D_{n,\Delta}\mid C_n)$ from explicit conditioned invariance and support inputs. The exact identity $\mathbb P(D_{n,\Delta})=\mathbb P(D_{n,\Delta}\mid C_n)\mathbb P(C_n)$ is proved from event inclusion. Centered positive-variance increments give positive finite-horizon survival probability, its monotonicity in the horizon, and positive-probability bounded increment windows on both sides of zero. `Analysis/Asymptotics/ShiftedFloor.lean` proves $\Delta_n/\sqrt{\lfloor\Delta_n^2\rfloor-m}\to1$ for positive real widths tending to infinity; the standard conditioned limit at integer times is formally reindexed to these exact diffusive horizons. `Analysis/Asymptotics/RegularVariation/LowerPower.lean` proves Potter's inverse-power lower bound; `FunctionalLimit/Conditioned/{SurvivalPower,TransitionPower}.lean` specialize it to the survival probability at $\lfloor\Delta^2\rfloor-m$ and multiply by the conditional transition probability. `Analysis/Asymptotics/PolynomialExponential.lean` proves the exact polynomial-to-exponential entrance-budget comparison for $L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$. `Fluctuation/{RecordLocalTime,LadderTime,DescendingLocalTime,RenewalFunction}.lean` defines strict record local times, ladder times and heights, and the descending ladder-height renewal function of Chaumont--Doney, Section 2, and Caravenna--Chaumont, definition (1.1). It proves finite-time measurability and the exact survival identity $C_n=\{T^-_1>n\}$. `FunctionalLimit/Donsker/{InteriorCorridor,InteriorFinite,InteriorDiffusive}.lean` proves the Brownian middle-start support and compactness step, its exact finite-grid identification, and a uniform positive lower bound for real widths $\Delta\to\infty$ at $n_\Delta=\lfloor\Delta^2\rfloor$. The final theorem constructs the Gaussian path law from the centered finite-variance increment law. `Entrance/MovingInterior.lean` transfers this bound to the exact moving event $\mathcal A_\Delta(x)$ for middle starting points. `FunctionalLimit/Conditioned/TransitionFactorization.lean` proves the independent fixed-prefix / transition-suffix probability product, including the reflected law. `Entrance/Edge/{LowerGeometry,UpperGeometry,Probability,ThreeRegions}.lean` proves both edge event inclusions, their exact product probability lower bounds, and the final three-interval minimum. `Moments/BoundedWindows.lean` derives the positive-mass positive and reflected increment windows from centered nondegenerate finite variance. `Entrance/Edge/PrefixSelection.lean` chooses fixed lengths with $m_+a_+>c+1$ and $m_-a_->c+1$. It proves the eventual geometric width and horizon inequalities for these fixed prefixes. `Entrance/Edge/PowerAssembly.lean` combines the two transition power bounds with the middle Donsker bound into one uniform $C_\alpha\Delta^{-1-\alpha}$ lower bound for the exact moving entrance event; the transition power bounds still depend on the unproved meander and survival inputs. `Probability/Sequence/IID/ConditionalBlocks.lean` proves the prefix/next-block conditional integral, its sectionwise lower bound, and the reverse Markov product recursion; `RandomWalk/Path/Window/Endpoint.lean` provides the measurable finite-block tube and endpoint event. `DriftedTube/FiniteVarianceLower/Blocks/EventBridge.lean` identifies the translated zero-start event with the next block given its starting position and proves the conditional probability estimate in the natural domain filtration. `DriftedTube/FiniteVarianceLower/Blocks/Product.lean` proves the reverse Markov product for successive blocks of variable lengths, including a longer final block, with an initial entrance-event factor. `DriftedTube/FiniteVarianceLower/Blocks/Geometry.lean` proves that each successful block enters the next central window and combines it with the product. `DriftedTube/FiniteVarianceLower/Blocks/Probability.lean` transfers uniform lower bounds from finitely many narrowed tubes to every starting point in the central window; `DriftedTube/FiniteVarianceLower/Blocks/Assembly.lean` combines this transfer with the Markov product. `DriftedTube/FiniteVarianceLower/Binning/{RealWidthLower,FiniteThreshold,Parameters}.lean` and `DriftedTube/FiniteVarianceLower/Staircase/{Rate/BinRate,Product}.lean` transfer Lemma 3.1(ii) from integer to real widths, take a common threshold over finitely many spatial bins, verify their tube parameters, compare narrowed and global exponents, and feed the resulting bounds into the finite staircase product. `DriftedTube/FiniteVarianceLower/Blocks/Exponent.lean` combines the exponential block costs and entrance budget. `DriftedTube/FiniteVarianceLower/Staircase/{Event,Partition,Inclusion}.lean` prove that the entrance and every horizontal block imply the full tilted-tube endpoint event. `DriftedTube/FiniteVarianceLower/Staircase/FiniteLower.lean` combines these results into the first tilted-tube lower bound under explicit entrance and schedule inequalities, with assumptions restricted to the finite set of actual blocks. `Donsker/InteriorCorridor.lean` also identifies the exact Brownian middle-start event printed in Appendix A.2 and the robust subevent used for scale perturbations. Normalization of the Imhof tilt and its identification with the standard Brownian-meander law, continuous local time and ladder-process convergence, the conditioned meander invariance principle recalled by Caravenna--Chaumont at equation (3.3), the survival asymptotic (Lemma 2.1), the edge entrance estimates, the unconditional entrance bound from the conditioned Brownian-meander and survival theorems, and the final two-sided theorem remain open. |

Thus the lemma dependency chain is 3.1(i) → 3.2 → 3.3 → 3.4, while 3.1(ii) supports the separate lower-bound branch 3.5. The inverse-scale and monotonicity developments remain formalized supporting results, but the revised proof no longer gives them standalone lemma numbers. Do not use a source label as a theorem number, and do not mark a supporting block or drawdown estimate as one of these lemmas.

For the Brownian first-window input to Lemma 3.5, Bolthausen's Lemma 2.3
equation (2.3) is proved in `Brownian/AboveStart/RunningMinimum.lean`, and
equation (2.4) is proved for finite and unrestricted horizons in
`Brownian/AboveStart/InteriorReturn.lean`. That file also proves that
Bolthausen's three-contact event $U$ is null. Both conclusions use the
rational-interval covering of repeated running-minimum values, independent
past and future continuous paths, and the atomless Brownian running minimum.
`Path/AboveStart/RunningMinimum.lean` reduces the endpoint equality in
equation (2.2) to an interior return or a unit-length excursion above the
running minimum. Outside $U$, it also identifies the window start with the
first passage of its height and proves that every strictly lower level is
first reached after the returned endpoint. The remaining input is the zero
probability of a unit-length excursion, which Bolthausen derives from the Lévy decomposition of the
descending Brownian hitting-time process. The pathwise process
$\tau_x=\inf\{t:B(t)\le-x\}$, its monotonicity, and its fixed-level
measurability are in `Path/DescendingHittingTime.lean`. If the path later
reaches a lower value, `Path/AboveStart/RunningMinimum.lean` proves that
every $v>t+1$ already bounds the hitting time of some lower level, so the
right-hand level limit is exactly $t+1$.
`Brownian/Reflection/UnboundedBelow.lean` proves that Brownian paths
eventually descend below every real level, using the reflection principle
and scaling. `Brownian/AboveStart/EndpointReturn.lean` combines that result
with the nullity of $U$ to identify the exact unit hitting-time jump
almost surely on every first-window endpoint-return event. The existing
`Brownian/Reflection/DescendingHittingTimeLaw.lean` states its fixed-level
distribution directly from the reflection principle. The candidate
half-stable Lévy jump-length intensity is defined in
`Distributions/Stable/LevyMeasure/HalfSubordinator.lean`; that file proves
σ-finiteness and zero mass for every singleton, while its identification
with the Brownian hitting-time process remains to be established. The existing
`IsPoissonPointFamily.ae_poissonRandomMeasure_apply_eq_zero` in
`RandomMeasure/Poisson/Support.lean` excludes realized Poisson mass from
zero-intensity mark sets; its fixed-mark corollary proves that an atomless
mark intensity produces no point with a prescribed jump length.
`Brownian/Reflection/FirstPassagePoisson.lean` applies this result to the
half-stable intensity. `Path/Continuous.lean` now makes the future increment
path jointly measurable in its path and start time, and
`Brownian/Independence/FiniteStoppingTime.lean` proves that the future
increment path at a finite-valued stopping time has Brownian path law.
`Brownian/Independence/StoppedPast.lean` strengthens this to independence
from the stopped past. `Brownian/Independence/FirstPassageGrid.lean` applies
the finite-valued result to first-passage observation grids, and
`Brownian/Independence/FirstPassage.lean` passes through expanding grids to
show that the post-passage increment path has Brownian path law and is
independent of the stopped past at each fixed level. The passage of
independence through almost-sure limits is a reusable result in
`MeasureTheory/Convergence/IndependentLimits.lean`.
`Path/FirstPassageRestart.lean` proves the deterministic restart identity
for two finite passages of a continuous path and recovers a finite first
passage from the stopped path. `Path/DescendingHittingTimeRestart.lean`
specializes the restart identity to the descending hitting-time process.
Turning strong Markov and these pathwise identities into stationary
independent increments of the hitting-time process is the next step.
The Brownian hitting-time process has not yet been identified with such a
Poisson jump family. Equation (2.2), Lemma 2.4, and the conditioned
invariance principle remain open.

The concrete finite staircase now has its own verified schedule and geometry:
`DriftedTube/FiniteVarianceLower/Staircase/Setup/Schedule.lean` defines
$q=\lfloor(L-t_1)/\ell\rfloor$ and the final block of length
$\ell+(L-t_1)\bmod\ell$; `DriftedTube/FiniteVarianceLower/Staircase/Setup/Parameters.lean` proves that the
horizontal block is $[r_{t_{j+1}},s_{t_j}]$ with width
$\Delta-c|I_j|/\Delta^2$; `DriftedTube/FiniteVarianceLower/Staircase/Endpoint/Windows.lean` identifies the
paper's $v_1(k),v_2(k)$ with the next central window and the final endpoint
window. `DriftedTube/FiniteVarianceLower/Staircase/Concrete/Lower.lean` applies the finite product theorem to
this exact schedule under explicit numerical and entrance assumptions.
The finite product now selects separate fixed interior endpoint intervals
for ordinary blocks and the final block, as in the two cases following the
uniform-in-$k$ argument of the proof. A single interval would impose an
impossible overlap when the final endpoint fraction is below $1/3$.
`StaircaseFirstWindow.lean` proves that, when the first block has length
$\ell$ and $10c\ell<\Delta^3$, the robust interval
$[r_{t_1}+2\Delta/5,r_{t_1}+3\Delta/5]$ implied for large widths by the three
constructions in Appendix A.2 lies in the central window of the first
horizontal block. The published entrance window
$[r_{t_1}+\Delta/3,r_{t_1}+2\Delta/3]$ is wider than this central window;
the robust entrance probability estimate must therefore be carried through
the Appendix A.2 formalization before it can discharge the first-block
assumption of `DriftedTube/FiniteVarianceLower/Staircase/Concrete/Lower.lean`.
`Entrance/RobustTransition.lean` defines this narrower event with terminal
window $[h_{t_1}+2\Delta/5,h_{t_1}+3\Delta/5]$ and proves that it is
measurable at time $t_1$. `DriftedTube/FiniteVarianceLower/Staircase/EntranceBridge.lean` proves
both its tilted-tube path constraint and its membership in the first
horizontal central window. `DriftedTube/FiniteVarianceLower/Staircase/Concrete/EntranceLower.lean` eliminates
the entrance geometry and measurability assumptions from the finite
staircase theorem; the remaining entrance input is exactly the probability
lower bound for this robust event. The printed $8c\ell<\Delta^3$ is used for the broader
first-window inclusion; $10c\ell<\Delta^3$ is an eventual strengthening
for the robust central-window inclusion in this formalization.
`StaircaseNumeric.lean` proves common width and time-ratio bounds, and
uses the sharp lower width $\Delta-2c\ell/\Delta^2$ for the exponent
comparison. The latter retains the paper's limiting width ratio $1$.
`DriftedTube/FiniteVarianceLower/Staircase/Endpoint/Margins.lean` proves the two separate endpoint-margin
comparisons for ordinary and final blocks; `StaircaseGlobalConditions.lean`
combines them into exactly the six per-block hypotheses of the finite
product. These results formalize the common-threshold part of the paper's
schedule argument without a varying block-index assumption.
`DriftedTube/FiniteVarianceLower/Staircase/Concrete/GlobalLower.lean` applies this reduction to the exact
finite staircase and robust entrance probability, yielding the target
exponential lower bound from the global inequalities.
`StaircaseRateLimit.lean` uses private width-ratio and floor-comparison
helpers to obtain the rounded narrowed-width exponent comparison under
$\ell/\Delta^3\to0$ and the strict margin $d<d''\beta^2$, where
$\beta=1-1/(3m)$.
`StaircaseEventually.lean` keeps its one-use rounded-width threshold,
margin, superquadratic time ratio, and subcubic cost comparisons private
and assembles the common threshold for the staircase proof.
`DriftedTube/FiniteVarianceLower/Staircase/Endpoint/Limit.lean` proves that the ordinary endpoint fraction
tends to $1/(3\beta)$; `StaircaseEventually.lean` takes one common eventual
threshold for all global conditions. `DriftedTube/FiniteVarianceLower/Staircase/Concrete/AsymptoticLower.lean`
then proves the eventual tilted-tube lower bound from the robust entrance
probability budget. The remaining probability-theory input is exactly this
robust entrance budget, downstream of the source meander and survival
theorems.
`DriftedTube/FiniteVarianceLower/Staircase/Concrete/ConditionalLower.lean` composes the Appendix A.2
polynomial-to-exponential entrance argument with that asymptotic product.
Its remaining two reflected transition hypotheses are precisely the
outputs of the conditioned Brownian-meander limit and survival asymptotic
used in Appendix A.2.
The conditional Appendix A.2 deduction is now present:
`Entrance/RobustTransition.lean` transfers the middle Donsker event to the
robust endpoint window, `RobustEdgeGeometry.lean` proves both fixed-prefix
and meander-suffix event inclusions after increasing the width threshold,
`RobustEdgeProbability.lean` proves the corresponding independent-product
lower bounds, `RobustThreeRegions.lean` takes their minimum with the middle
bound, and `RobustPowerAssembly.lean` proves the uniform
$C_\alpha\Delta^{-1-\alpha}$ entrance estimate from the two reflected
nonnegative transition bounds. The source-level conditioned meander
invariance and survival regular variation hypotheses used by those
transition bounds have not yet been discharged.
`Entrance/RobustExponentialBudget.lean` combines that conditional power
bound with the proved polynomial-to-exponential comparison, giving the
entrance probability budget for every horizon
$L\ge\lfloor\Delta^{2+\varepsilon}\rfloor$ along arbitrary real-width
sequences tending to infinity. The source-level probability inputs are
still needed to obtain the unconditional statement of Lemma 3.5.
`Analysis/Asymptotics/SequentialEventually.lean` proves that eventual
validity along every divergent real-width sequence yields a common real
threshold. `Entrance/RobustUniformBudget.lean` applies this lemma to the
robust exponential entrance bound. Its source assumptions quantify the
two reflected transition lower bounds over all divergent real-width
sequences; the width in its conclusion ranges over all sufficiently large
real values rather than just integer widths.
The fluctuation modules now prove $T_k^\pm\le n\iff k\le\ell_n^\pm$,
measurability of both extended ladder times and their finite-height events,
and monotonicity and measurability of the descending ladder renewal function
$V_\nu(x)=\sum_{k\ge0}\mathbb P_\nu(H_k^-\le x)$. Each finite
positive-index ladder time is a strict record; ascending and descending
ladder heights are measurable, nonnegative and nondecreasing, and
$V_\nu(x)=0$ for $x<0$. Tonelli's theorem identifies $V_\nu(x)$ with
the expected number of ladder heights at most $x$, as in
Caravenna--Chaumont, definition (1.1). These are foundational steps toward the cited
renewal and local-time limit theorems; the survival regular variation
and conditioned meander convergence themselves remain to be proved.

| Source component | Lean modules | Verified scope |
|---|---|---|
| Stable-process escape and comparison estimates (Lemmas 1–2) | `Probability/Process/Stable/SmallDeviation/` | Finite negative escape rates, translated corridors, endpoint constraints, and path-law transfer are proved under the stated stable-process assumptions. |
| Stable-process corridor and path-class rates (Theorem 2; Lemmas 2–3) | `Probability/Process/Stable/SmallDeviation/PathClass/StepCorridor/Rate.lean`; generic approximation in `Probability/Process/Path/PathClass/StepCorridor/Probability/Rate/` | Exact `M₂`, finite-union `M₃`, and `M` rates are proved. For arbitrary `IsM` sets the API gives matching inner and outer probability rates; it does not infer measurability from energy approximation. Ordinary probability theorems retain an explicit null-measurability premise. |
| Random-walk finite-partition estimates (Lemma 3) | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/RandomWalkBounds/` | Variable-cell upper estimates, endpoint-core lower estimates, stable block limits, balanced partitions, and the logarithmic energy sum yield exact `M₂` rates for both endpoint conventions. `Stable/RandomWalkBounds/Source/PartitionLimit.lean` proves the exact source-endpoint last-block rate; `Stable/RandomWalkBounds/Source/PathClassRate.lean`, `Stable/RandomWalkBounds/Source/PathClassRegimes.lean`, and `Stable/RandomWalkBounds/Source/PathClassInnerOuter.lean` assemble its `M₃`/`M` and inner/outer consequences. |
| Attraction, norming, and slow diagonal (Lemma 4 input) | `Probability/Distributions/Stable/Attraction/`, `Analysis/Asymptotics/RegularVariation/`, `Probability/Process/RandomWalk/FunctionalLimit/Stable/` | The inverse-Tauberian route covers `0 < α < 2`; the Gaussian normal-domain route covers `α = 2`, including infinite variance. The three source centering regimes have `J₁` tightness and path-law convergence under zero-centered scalar attraction. |
| Gaussian explicit constant and source Theorem 3 | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Gaussian/EscapeConstant.lean`, `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Gaussian/SourcePathClass.lean` | The source Theorem 3 assumes i.i.d. mean-zero, variance-one increments; section 4 computes its constant through the simple symmetric walk. The Lean Gaussian source-rate adapter has the same `−π²/2` width-energy coefficient but currently takes `hB : IsBrownianReal B Q`; the local axiom test verifies the bridge under this input and does not construct a canonical Brownian witness. This does not claim Theorem 3 covers infinite-variance normal attraction. |
| Paper's terminal convention | `Topology/Cadlag/TerminalLeft.lean`, `MeasureTheory/MeasurableSpace/CadlagPath/TerminalLeft.lean`, `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/SourcePath.lean`, `Stable/RandomWalkBounds/Source/PartitionLimit.lean` | The source `D(0,1)` is right-continuous before `1` and left-continuous at `1`; `terminalLeftPathSpace` is that domain inside the repository's larger càdlàg space. The deterministic map, Borel measurability, source path ending at normalized `S_(n−1)`, and exact finite event identities are proved. The exact variable-horizon `M₂` rate and its `M₃`/`M` adapters are established. |
| Relative source target class | `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/RelativeApproximation.lean`, `MeasureTheory/Measure/CadlagPath/PathClass/StepCorridor/ContinuousBoundary.lean`, `Topology/Cadlag/Skorokhod/PathClass/StepCorridor/ContinuousBoundary.lean`, `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Stable/RandomWalkBounds/Source/PathClassRelative.lean`, `BranchingProcessTest/Mogulskii/RelativeTerminalLeft.lean` | The paper's `𝔐` targets are subsets of its terminal-left path space `D₀`. The Lean relative approximation records `D₀ ∩ inner ⊆ G ⊆ D₀ ∩ outer`; the source path law is supported on `D₀`, so this gives the event sandwich. The strict unit corridor test and continuous-boundary relative `M` approximation compile. For the latter, inner and outer energies converge to `continuousBoundaryRealEnergy`, identified with the integral of `continuousBoundaryDensity`. This covers strictly separated continuous boundaries with the source's pinned-start condition; it does not claim every abstract `𝔐` target has such an approximation. The raw-source continuous-boundary adapters are implemented, and their integrated `FromIncrementLawRates.lean` test plus 16-declaration transitive axiom audit pass. |
| Remaining source-assumption and application gaps | `Stable/RandomWalkBounds/Source/Inputs.lean`, `SourceNormalization.lean`, `FunctionalLimit/Stable/PathLawExistence.lean`, `Probability/Process/Stable/PathLaw/{MonotoneGrid,Concatenation,FullProcess}.lean`, `Stable/Discrete/FromIncrementLaw/{PathLaw,StableDomain,NormalDomain,ContinuousBoundary}.lean` | B/C have compiled: tight-subsequence extraction, repeated-grid laws, iid path-block concatenation, and full-time stable-process construction. D's raw-source modules, ordinary-probability adapters, and continuous-boundary specialization build in the focused integration test; its 16 named declarations pass the reviewed transitive axiom allowlist. Intermediate rate APIs may take stable-process/path-law inputs by design; the public increment-law wrappers construct them from raw hypotheses. |

### Source normalization

The source's rate denominator is

```text
n · L*(aₙ) / aₙ^α
```

and is `stableRateNormalization α ν scale n`. The common width-energy coefficient
`rateCoefficient α C = -(C * 2^α)` lives in
`Probability/Process/Path/PathClass/StepCorridor/Probability/Normalization.lean`; the generic
coefficient no longer depends on a stable-process assembly module.

The block length is `⌊c · κν(aₙ)⌋₊` with
`κν(u) = u^α / L*ν(u)`. The slow-variation factor is part of the scale. The
regular-variation and asymptotic-inverse results used for this formula are in
the general `Analysis/Asymptotics/RegularVariation/` layer, while the stable
norming specialization remains in the distribution layer.

### Source-alignment and probability semantics

The source endpoint is implemented by the terminal-left path transform. The
last discrete block is handled with its exact length, so the proof does not
transfer an exponential rate through an `o(1)` probability error. The source
`M₂`, `M₃`, and `M` interfaces are now connected. For arbitrary `IsM` targets,
the theorem provides matching inner and outer probability rates; an ordinary
probability limit is stated only when the target event is measurable (or
null-measurable for the underlying completed probability measure). This
distinction is intentional because the energy approximation in `IsM` alone
does not imply target measurability.

Generic inner measure and measurable-subset inequalities are in
`MeasureTheory/Measure/InnerOuter.lean`; generic analytic/capacity theory is in
`MeasureTheory/Analytic/`. The path-specific projection application remains
in `Probability/Process/Path/PathClass/StepCorridor/Probability/NullMeasurable.lean`.

## Local dependency layout

The Lean probability modules are arranged by role:

- `MeasureTheory/Measure/`: `FiniteOnFamily.lean` holds the single finiteness condition `IsFiniteOnFamily ν 𝒜` together with the compact, left-ray, and right-ray families; `DiracSum.lean` packages optional Dirac sums on top of mathlib's `Measure.sum`/`Measure.count` API and proves that optional Dirac sums are integer-valued with multiplicity; `IntegerValued.lean` defines `Measure.IsIntegerValued` as the requirement that every measurable set have natural or infinite mass, without asserting a countable Dirac representation; `Domination.lean` derives a.e. finiteness on a family from an integrable dominating functional, the abstract form of the paper's `ψ(1) = 0` computation; `AtomFiniteness.lean` gives the deterministic finite-sublevel input to the enumeration.
- `Probability/PointProcess/`: `Basic.lean` holds `PointProcess Ω E 𝒜`, the abstract random measure with integer-valued samples and a separately parameterized finiteness family. Integer-valuedness alone is not a point enumeration theorem. The object is a random measure, so it lives under `Probability/` in the `ProbabilityTheory` namespace, following Mathlib's `Probability/Kernel/`.
- `Probability/BranchingProcess/`: `Offspring/Law.lean` defines a probability law on complete optional unit-marked offspring configurations and its independent address field; `GaltonWatson/Generation.lean` pushes that law to the existing unmarked process object and proves the one-root generation-zero count; `GaltonWatson/BranchingProperty.lean` states the coordinate independence at the process boundary. `Combinatorics/BranchingWalk/Basic/GenerationSize.lean` proves zero-population absorption for any realized walk, including infinite roots and slots. The standard integer-valued population-size transition chain for finite offspring configurations remains open.
- `Combinatorics/BranchingWalk/Step/PointMeasure.lean`: the deterministic Dirac sum `stepPointMeasure` of a branching step, equal to `Measure.iOptionDiracSum`, with its per-slot atoms and evaluation lemmas. `Combinatorics/BranchingWalk/Cloud/SliceMeasure.lean` defines the cloud Dirac sum `Cloud.diracSum C t`, the sum of `Measure.dirac` over the particles alive at `t` with multiplicity, and evaluates it on a countable slice at any threshold as the count of the particles at most there (`Cloud.diracSum_Iic_eq_encard_of_countable`). `Cloud/Order/Slice.lean` states the slice order `SliceDominatesMeasure` on those measures together with the rankwise form `Cloud.RankwiseDominates`, the two being equivalent on a finite slice; `Cloud/Order/Basic.lean` states the order at every time as `Cloud.Dominates`, with its mirror through `OrderDual`.
- `Probability/BranchingRandomWalk/Step/`: `Basic.lean` defines `stepLaw` directly on measurable maps into `ι → Option X`; `Presentation.lean` defines the coordinate sampling structure `StepPresentation Ω ι X`, whose absent-slot displacement is ignored when it assembles to an optional field. `PointMeasure.lean` defines the general `pointMeasureOf` and `branchingLawOf` observations for raw optional fields, while `StepPresentation` supplies convenience adapters. `Field.lean` adds the `TreeNode ι` index; `PointProcess.lean` adapts the observation to the generic point-process interface; `Order.lean` and `MultiRootLaw.lean` transfer structural properties and marginals.
- `Probability/BranchingRandomWalk/Genealogy/`: marked Ulam--Harris trees, the generation domain filtration, positions, first observable splits, and multiple initial roots.
- `Probability/BranchingRandomWalk/Step/`: fixed and generation-measurably selected subtree product laws, including the multi-root versions.
- `Probability/BranchingRandomWalk/Population/`: `Candidates/` for finite ranking and truncation, `Processes/` for selected and retained recursions, and `Growth/` for deterministic size lemmas.
- `Probability/BranchingRandomWalk/Timing/`: generic stopping-time and measurability lemmas, timing counterexamples, and geometric trials.

All modules are reached from the library roots listed in `lakefile.toml`.
General independent-reserve integration estimates live in
`Probability/Independence/Integration/Reserve.lean`; general sequence and
moment estimates are in `Probability/MeasureTheory/Convergence/` and
`Probability/MeasureTheory/Moments/`, including the tail-integral bound in
`Convergence/TailExpectation.lean` and the exponential-moment bound in
`Moments/ExponentialMoment.lean`. The
deterministic speed squeeze is in
`Probability/BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed/Asymptotics.lean`; it is a
final implication from eventual bounds, not a speed-existence theorem. Within
one initial ancestor, a *single* i.i.d. pre-sampled marked tree supplies every
reserve branch. An arbitrary family `κ` of distinct same-generation roots
indexes descendant marked trees in
`Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/JointSubtrees.lean`,
where their joint product law is proved. Random population size, stopped
generations, position offsets, and stopping-line frontiers require the later
dependent interfaces.

For the theorem with $m_N=\lfloor N^\alpha\rfloor$ **initial particles**, `Probability/BranchingRandomWalk/Genealogy/RootIndexed/Law.lean` uses $m_N$ labelled initial roots through the `Fin m_N` instance `finiteRootStepFieldLaw`, each root with its own pre-sampled Ulam--Harris tree; the labelled law, filtration, and positions are that instance, not a separate copy. The initial positions are supplied as `Fin m_N → ℝ`, so all-zero starts and later common shifts are representable. `Genealogy/Exploration/Selected/CellBranching.lean` and `Genealogy/Exploration/Selected/StoppingCellBranching/` prove deterministic-generation branching across these roots, including roots selected using the entire multi-root domain filtration. `Population/Processes/Selected.lean` defines one common selection pool, proves its labelled set adapted, bounds its size by $N$ after the first generation, and proves nonextinction under an explicit pathwise first-child hypothesis. `Probability/BranchingRandomWalk/Step/OrderedSupport.lean` derives orderedness and that first-child hypothesis for the sorted pushforward `StepLaw.sorted`; neither is assumed of the raw law. The earlier single-tree statements concern descendants of one initial ancestor and cannot substitute for this multi-root process.
`Population/Candidates/MultiRoot.lean` makes the finite step explicit. `Population/Candidates/Adapted.lean` proves that an adapted finite parent set produces a measurable candidate set at the next generation, by partitioning over the countable parent-set values. `Combinatorics/BranchingWalk/Step/Monotone.lean` proves local prefix and displacement witnesses for later slots. `Population/Candidates/Ordering.lean and Population/Candidates/Leftmost.lean` proves a deterministic rank rule and its cardinal bound. Its tie key compares parent identity, then the child's slot number, then a full-address fallback; `candidateEarlier_ordered_siblings` proves earlier siblings beat later siblings even at equal displacement. `Combinatorics/BranchingWalk/Step/SlotOrder.lean` now supplies abstract first-$N$ prefixes with exact cardinality and exhaustion. The existing candidate implementation remains the `α = ℕ` specialization and must be generalized to those prefixes. `Population/Candidates/FullRank/ and Population/Candidates/FullSelection.lean` proves exact equality between finite-slot and full selection under ordered marks; the ordered field must now be obtained from `StepLaw.sorted` together with tree-level descendant transport, rather than assumed as the random input. `Genealogy/Exploration/Selected/StoppingCellBranching/DependentLaw.lean` packages every stopped population cardinality into one dependent object. The concrete coupling instance remains open.

`Probability/BranchingRandomWalk/Step/MultiRootLaw.lean` lifts the law of a
random step `Ξ` to all labelled roots and addresses. The construction starts
from `Ξ : Ω → Combinatorics.Branching.Step ℕ ℝ`; it does not reconstruct slots
from an abstract point measure.

`Genealogy/Exploration/RootIndexed/DomainFlow/` uses labelled coordinates
`Fin m × TreeNode` for exploration information. It proves that a reserve
subtree under any initial root is independent of the joint exploration domain
whenever its labelled descendant coordinates have not been inspected. Equal
local addresses under two different initial roots remain distinct coordinates.

The raw mark type does not order optional children.
`Combinatorics/BranchingWalk/Step/Monotone.lean` defines `Step.IsOrdered` as a
property. `Step/Orderable.lean` reindexes an orderable raw step to an ordinary
ordered `Step`; its relabelling is injective and covers every surviving slot.
`Combinatorics/BranchingWalk/Step/Ordering.lean` proves that this reindexing
preserves the complete point measure, including multiplicities.
`Probability/BranchingRandomWalk/Step/Ordering.lean` packages the existence of
a measurable ordered realization as `IsMeasurablyOrderable`, preserves the
branching law, and defines the optional leftmost displacement at the abstract
least slot. The raw and ordered slot types may differ, and sorting is not
specialized to `ℕ`. A concrete raw law must still
construct such a measurable ordered realization;
pointwise `IsOrderable` alone does not imply measurability of a choice.
`Step/OrderingLaw.lean` packages the raw law with deterministic measurable
sorting, and all indexed variables $\Xi_i$ are read only after that map. Even
when sorting acts as the identity on an already ordered sample, orderedness is
not an assumption on the raw branching law.
`Step/FieldOrdering.lean` requires this property at every tree node and proves
that the whole optional field $u\mapsto(\Xi_u)_1$ is jointly measurable. For a
deterministic measurable ordering rule it additionally proves
$(\Xi_u)_1\in\mathcal F_{|u|+1}$, the later-generation version, the dynamically
selected-node version, and measurability of the entire depth-$n$ frontier in
$\mathcal F_{n+1}$. The one-generation offset matches the convention that a
node's reproduction step is revealed when its children appear. The pathwise tree-level sorting obligation is now handled by
`Combinatorics/BranchingWalk/MarkedTree/Ordering.lean`: its recursive address
map follows the local support-covering relabeling at every ancestor, so marks
on the entire descendant subtree travel with the child; it also proves exact
local survival and point-measure preservation. The `RootIndexed` constructor
in `MarkedTree/OfBranchingWalk.lean` applies this transport independently at
each root. What remains is a measurable choice of nodewise relabelings for a
random field, together with measurability of the recursively induced marked
tree map and its use in the concrete random-law/coupling construction. The
earlier ranked-atom and measure-to-step chain remains deleted. Mathlib
measures and Dirac sums are reused for the forward point-measure observation.

An external Lean 4 project, [LeanLevy](https://github.com/slink/LeanLevy/tree/7e73fd9b23ad52956ec2756a815889a783131ce4),
constructs a Poisson random measure by summing Dirac measures at realized
points; see the upstream
[`PoissonRandomMeasure.lean`](https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean),
now maintained here in `Probability/RandomMeasure/Poisson/Basic.lean`.
The MIT-licensed Poisson modules are now vendored and compiled against the
pinned Mathlib. Their point-family assumptions are not the thesis's arbitrary
reproduction law. The generic piece-sum, Poisson-integral measurability, and
finite-window vector API lives under `Probability/RandomMeasure/Poisson/`; the
stable-law identification stays in the stable jump-model layer. Almost-sure
support and starting-value identities for cutoff paths live under
`Probability/Process/Levy/Jump/PoissonConfiguration/Path.lean`.
Mathlib's [`HasPDF`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Density.html)
means absolute continuity of a random variable's law relative to a reference
measure. It is not the definition of a point process and is not assumed for
the present atomic child measure. The Brownian-motion development uses
process and Gaussian-law APIs, not a general point-process representation.
`Probability/BranchingRandomWalk/Step/OrderedSupport.lean` proves that if the one-node mark law gives this ordered subset probability one, then every address in the entire pre-sampled tree has an ordered mark simultaneously almost surely. This uses mathlib's countable almost-everywhere intersection and the proved one-node marginals; it does not itself establish the antecedent from the abstract branching-step point process.

- `Probability/Process/HittingTime/Declarations.lean` owns the generic first-success
  stopping-time declarations; it does not redefine filtration, measurable space
  or stopping time.
- `Probability/BranchingRandomWalk/Timing/TimingCounterexample.lean` gives kernel-checked
  counterexamples to the original look-ahead stopping-time claim and to automatic
  adaptedness of a generation-one state chosen from a generation-two outcome.
  It also proves that an adapted population count need not make the retained
  particle identity adapted. In the thesis
  model itself, $\{\tau_1\le0\}$ has probability $p_0\in(0,1)$ in an allowed
  parameter case, whereas $\mathcal F_0$ is trivial. This does not settle
  whether the final successful completion time $\tau$ is a stopping time.
- `Probability/Process/HittingTime/ObservableCandidates.lean` proves the measurable candidate-declaration interfaces, while `Probability/Process/Adapted/Recursion.lean` proves the causal recursion interface. These do not construct the marked tree, reserve candidates, or coupling.
- `Combinatorics/UlamHarris/Basic.lean` defines `TreeNode`, its `ℕ`-indexed instance `𝕍`, and `Mark`; `Tree/Defs.lean` defines deterministic single-root and root-indexed trees; `Tree/MeasurableSpace.lean` supplies the induced measurable structure. `MarkedTree/Basic.lean` defines realized trees with marks on realized nodes, partial mark views, and the measurable structure induced by tree membership and `Option`-valued marks. `Combinatorics/UlamHarris/Tree/Graph/` projects realized trees to Mathlib graph objects. The address relation is `TreeNode.IsChild` and points from parent to child. The root-indexed family is projected as `RootIndexed.forestGraph`, which is acyclic for any number of initial ancestors and is connected exactly in the one-root case.
- The current branching-step layer is intentionally direct: `Combinatorics.Branching.RootIndexed.BranchingWalk` stores one `StepField` and initial population per root. Its `IsParentClosed` property is derived from the `surviveAlong` prefix theorem, not stored as a structure field. The slot-level condition `Step.IsSiblingClosed` is separate and says that surviving sibling slots form an initial segment. Orderedness is the property `Step.IsOrdered`; there is no `OrderedStep` wrapper. `Step.siblingCardinal` gives the general predecessor cardinal, while `Step.siblingRank` and its `ℕ` theorem apply to finite-predecessor canonical enumerations. Marked-tree correspondence and sibling mark monotonicity remain in `Combinatorics/UlamHarris/MarkedTree/` and use these explicit predicates. A finitely supported step on `ℕ` has an increasing enumeration of its children, built by rank and without
  sorting a list (`Step.hasIncreasingEnumeration_of_isFinitelySupported`), and is orderable by
  `Step.isOrderable_of_hasIncreasingEnumeration`, whose relabelling is that enumeration itself. Orderability
  lifts to a step field and to a root-indexed walk (`StepField.IsOrderable`,
  `RootIndexed.BranchingWalk.IsOrderable`, both found by instance search from the finitely supported ones).
  The generic recursive transport is `MarkedTree.orderingTransport` and
  `StepField.markedTreeOfOrderingMap`;
  `RootIndexed.BranchingWalk.positionedMarkedTreeOfOrderable` applies it at
  every initial root while preserving the position map. These are pathwise
  constructions, not measurable random sorting selectors. Neither orderability
  class is specific to `ℕ`: only the finite-support-to-orderability instance is.
- `Combinatorics/BranchingWalk/Population/` defines the nonrandom set-valued `Population` and layerwise `FinitePopulation` in a fixed branching field. Their depth, successor, root ancestry, surviving-edge, parent, and prefix theorems contain no sample space, filtration, measurability, finiteness assumption on the set-valued version, position, or order. The probability-layer `CausalPopulation` evaluates samplewise to this object and adds only adapted membership events; `CausalFinitePopulation` evaluates samplewise to `FinitePopulation` and supports cardinal observables and capacity events.
- `Combinatorics/BranchingWalk/Selection/` separates candidate rules from whole-walk transforms. `Selection/Basic.lean` defines a `Mechanism` on finite particle-identity sets; `Selection/Contain.lean` defines `SelectContain`; and `Selection/WalkTransform.lean` defines a parent-closed, containment-decreasing `WalkTransform`. `Selection/NSelection/Basic.lean` imposes the exact law `card (select s) = min N (card s)`, so below capacity every candidate is retained and at capacity exactly `N` are retained. `Selection/NSelection/Coupling.lean` proves the abstract one-step threshold-count comparison with leftmost selection without identifying particle identity and position. `Selection/NSelection/BranchingWalk.lean` defines `IsNBranching`, `NBranchingWalk`, and the corresponding capacity-bounded whole-walk transform. Random laws and measurable causal rules live under `Probability/BranchingRandomWalk/Selection/`. `Cloud.DominatesBy φ` and `Cloud.RankwiseDominatesBy φ` compare an abstract position cloud only after applying an ordered observation `φ`; they do not compare raw marks.
- `Combinatorics/BranchingWalk/Step/Measurability.lean` gives the measurable support conditions and the concrete truncation rules. The all-absent mark represents zero children; `Probability/BranchingRandomWalk/Step/Law.lean` supplies the one-field i.i.d. law and `Probability/BranchingRandomWalk/Genealogy/RootIndexed/Law.lean` its arbitrary-root product and finite-root marginals, but no binomial lower-tail estimate has yet been proved for the retained population.
- `Combinatorics/BranchingWalk/Step/FiniteSelection.lean` and `Probability/BranchingRandomWalk/Population/Processes/StepSelection/` replace the former raw-slot retained/truncated implementations. They construct the intrinsic first-$N$ slots only after ordering by a potential, allow empty steps, support measurable barrier filtering and first-child preservation, and prove adaptation and the $N^n$ population bound. No result assumes that raw slots `0` and `1` are already the first two children.
- `Probability/BranchingRandomWalk/Step/Law.lean` reuses mathlib's `Measure.infinitePi`, `infinitePi_map_eval`, and `iIndepFun_infinitePi` for a pre-sampled i.i.d. family at every genealogical address. The random law is parametrized; no moment or ordering hypothesis is silently imposed. `Genealogy/RootIndexed/Law.lean` applies the same construction to the family of initial roots, so the finite initial population is a marginal of one common pre-sampled field.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/Exploration/` and `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/Property.lean` reuse mathlib's `indep_iSup_of_disjoint` and `Measure.map_infinitePi_infinitePi_of_inj`. It proves the actual generation domain is independent of all future raw marks, each fixed descendant subtree has the original i.i.d. law, and two distinct same-depth descendant domains are independent. It does not yet cover the joint random surviving set or positions.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Selected/AbstractSubtree.lean` proves the selected subtree is measurable for a generation-domain-measurable root; if that root has the current depth, a countable measurable partition gives the exact past/subtree event factorization, the original subtree law, and independence from the generation domain. The proof uses no look-ahead choice.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/Property.lean`, `DomainFlow.lean`, and `JointSubtrees.lean` are generic in the child-slot type `α`. They use a prefix-address injection and mathlib's curry theorem for infinite product measures to prove the joint product law for an arbitrary index family `κ` of distinct same-generation roots. No countability assumption on `α` or `κ` is needed for this coordinate-product statement. They also prove the family of subtrees reads only future marks and gives its past/future event factorization; later stopped finite-population interfaces remain specialized to `α = ℕ` and finite vectors.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/StoppingSubtreeVector/` partitions by the countable finite vector of selected addresses. It proves measurability, the event factorization, the joint i.i.d. product law, and independence from the generation domain for a measurable vector of $k$ distinct generation-$n$ roots. It does not yet identify such a vector with the actual selected or killed BRW population.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Selected/StoppingPopulation.lean and Genealogy/Exploration/Selected/StoppingCellBranching/` accepts an arbitrary stopped-domain-measurable finite set of labelled roots, including roots under different initial ancestors. On every prescribed set cell it proves the exact product descendant law by a further countable partition over the finite stopping generation. The theorem includes the empty population and applies directly with $m=\lfloor N^\alpha\rfloor$; it does not assume a child exists.
- `Combinatorics/BranchingWalk/Step/` and `Combinatorics/BranchingWalk/Basic/Displace.lean` expose the abstract position interface induced by a step field: `Step/Basic.lean` gives the presence predicate `survive`, the support, and the zero-defaulted slot value `value'`, `Basic/Displace.lean` the address-carrying mark `displace` (the displacement from a starting address) and its partial version `displace?`; their root instances are written `displace β [] u` and `displace? β [] u`, and no definition is kept that only fixes the starting address. The path realization predicate `surviveAlong` lives in `Combinatorics/BranchingWalk/Basic/SurviveAlong.lean`, whose descendants and ancestors, with the parent and the surviving siblings, are in `Combinatorics/BranchingWalk/Basic/Descendant.lean`; realization of a single child slot is the `survive`/`value'` interface in `Combinatorics/BranchingWalk/Step/Basic.lean`. The abstract position function is total on all addresses, while concrete particle-system theorems must explicitly require realization. There is exactly one position and one realization predicate, defined on an arbitrary label type; a `ℕ`-specialized copy is not kept, and root-indexed displacement is read off the single-root one rather than defined again.
- `Probability/BranchingRandomWalk/Step/Position/Measurability.lean` is the only generation-filtration position file: realized nodes, fixed-address displacements, current-generation displacements, and measurably selected current-generation addresses. It is generic in the mark type, so no real-valued duplicate is needed.
- `Probability/BranchingRandomWalk/Assumptions/`, `Spine/`, `Restart/`, and `Selection/` are compiled directly by the source globs; no umbrella module is needed. `Assumptions/Moments.lean` carries the first-, fourth-, and exponential-moment conditions plus the cross-term weight `∑_{i ≠ j} exp(-(Ξᵢ+Ξⱼ))`; it builds, and `fourthMoment_implies_firstMoment` proves the fourth moment condition implies the first.
- `Probability/BranchingRandomWalk/Spine/FiniteKernel.lean` contains the finite child algebra
  for **both** many-to-one variants. It is not the expectation identity for
  random child and is not marked as the full theorem.
- `Probability/BranchingRandomWalk/Selection/NSelection/AsymptoticSpeed/Asymptotics.lean` contains the final deterministic speed squeeze
  and an elementary first-moment truncation inequality.
- `Probability/MeasureTheory/Convergence/TailExpectation.lean` contains
  the finite-event integral bound and the abstract sequence theorem deriving
  the extended-real bound `liminf E[Xₙ]/log n ≥ target` from eventual
  polynomial lower-tail bounds and `E[exp(−Xₙ)] ≤ n`. The module build, test,
  and axiom audit pass. It does not formalize the BRW estimate (4.16), so it
  does not by itself prove the thesis's `a = 1` endpoint or Theorem 1.3.
- `Probability/BranchingRandomWalk/Spine/FirstPassage.lean` adds a
  one-root, fixed-generation many-to-one bound and a finite-horizon union
  bound; both have a focused test and axiom audit. The uniform-offset
  horizontal-tube block estimate in
  `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Spectral/Range/BlockBound.lean`
  also builds and passes its focused audit. These pieces are inputs, not by
  themselves the BRW estimate (4.16): the
  deterministic running-maximum binning, exact fixed-pattern IID block
  product, finite union over bin patterns, and parameter selection are built
  and audited in `RandomWalk/Path/Drawdown.lean` and
  `Probability/Process/RandomWalk/SmallDeviation/Drawdown/FiniteVarianceUpper.lean`. In particular,
  `measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance`
  proves the uniform no-large-drawdown estimate for centered increments of
  arbitrary positive finite variance. The estimate is direct at that variance;
  `Probability/Process/RandomWalk/SmallDeviation/Drawdown/Scaling.lean`
  records the corresponding event and measure scaling identities.
  The former `SelectedEndpointSublevel.lean` adapter chain depended on the
  removed raw range-rate theorem and has been removed pending a derivation
  from the finite-variance tilted-tube estimate. The T11-L probability
  adapter and its endpoint-moment and `L²` assembly are open.

Shi, *Branching Random Walks*, §1.3, Theorem 1.1 proves the unweighted
many-to-one formula by induction: the one-generation weighted law is followed
by conditioning on the first generation and the branching property. The
weighted variant in the thesis follows by choosing a weighted test function.
This is a paper proof, not reusable Lean code: it assumes the independent BRW
subtrees and the normalized tilted law rather than establishing their
measurability. Shi §1.4, Lemma 1.5 also gives the elementary exponential
minimum bound using Jensen and max $\le$ sum; no new probability construction
is needed for that deduction once the many-to-one identity is formalized.
The reference is at
<https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf>.

## Dependency version audit (2026-10-05)

The project pins upstream mathlib at
`380f2aafb622cb2c1c93dac545b6389083c68c51` and BrownianMotion at
`0d5b6eb928e616d3b1f774ad7d233c167d9f42c9`. Both revisions are recorded in
`lakefile.toml` and `lake-manifest.json`; the Lean toolchain is `v4.35.0-rc3`,
with Elan `4.2.4`. The pins make builds reproducible; dependency refreshes are
performed deliberately rather than as part of routine verification.

## Module migration audit (2026-10-05)

The deterministic path and topology foundations, the random-walk law and
Donsker interfaces, the independence and maximal-inequality layers, the
finite-state spectral interfaces, the shared block-scale arithmetic,
random-walk kernel foundations, killed-kernel comparison and uniform bounds,
measure convolution powers, couplings, stable laws, point-measure/Dirac-sum
interfaces, the Markov/strong-Markov process interfaces, generic sequence
prefix filtrations and IID stopping-time block factorization, and the
stopping-time/timing interfaces are now Lean modules. The
finite corridor-cover, path-oscillation, exceptional-event, finite-kernel,
moment-assumption, deterministic `NSelection`, spine path/endpoint/point-measure,
root-indexed genealogy, selected-population, and split-schedule interfaces are
also moduleized at their generic or application seams. Their imports are public
only where the imported declarations form that layer's API; no umbrella
re-export file was introduced.

The 2026-10-06 full build completed all 4460 Lake jobs. The pinned Mathlib
style linter passed over all 867 production Lean modules. The tracked
verification inventory contains 79 Lean test modules (the Lean test runner
compiles each tracked module) and 28 Python import-boundary unit tests.
Mathlib's own
`lint-style.lean` emits a module-header warning under `requiresModuleSystem`;
that warning is in the pinned dependency script, not a project module. The
visualizer manifest is checked both in the Pages workflow and in the required
Lake build job, so stale declaration names fail the required check. The module-header
contract is parser-checked for the stable escape-rate module and both path-law modules; other legacy
files still use Lean's traditional import header and are not implicitly
claimed to have migrated to the opt-in module system. The random-walk
Mogulskii subtree now consistently uses
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii`, while generic path
classes remain under `Skorokhod.PathClass.StepCorridor` for the classes and `ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability` for their probability estimates.
The singleton-walk optional-increment representation now has a measurable
equivalence, the stable path-law escape proof factors through an exact tube
probability transfer, and `Order.Filter.SlowDiagonal` provides the general
order/filter selector used by fixed-parameter arguments. Its real-valued
estimate is in `Analysis.Asymptotics.SlowDiagonal`; the regular-variation
adapter adds the multiplier-ratio limit, and the stable scale adapter also
enforces `d(n) * scale(n) / normalization(n) → 0`. The first
increment displacement identity now lives in `AdditivePath`; the cleanup also
replaced the obsolete `IsMogulskiiScale` structure projection in the tightness
adapter with the generic `IsSmallDeviationScale.tendsto_atTop` interface.
The generic continuous-process range-event mass is now isolated in
`Probability/Process/Path/Oscillation.lean`, while the unit-interval path
construction is shared from `Probability/Process/Path/UnitInterval.lean` and
the generic càdlàg embedding is shared from
`Probability/Process/Path/Skorokhod.lean`, while
the Brownian start-at-zero specialization lives in
`Probability/Process/Brownian/Range.lean`. Thus the discrete `BlockDonsker`
bound does not import the higher-level spectral-rate or Brownian-specialization
module, and the Donsker rational/Skorokhod adapters import only the Brownian
predicate plus the generic path interfaces. The new
`Range/BlockBound.lean` adapter carries that closed-set estimate to a fixed
diffusive block and keeps the cover parameters fixed before taking the limit;
the finite-cover exponential and complete-spectrum correction are defined once
in `Range/Rate.lean` and reused by the adapter. The explicit nested-limit
parameter choice is isolated in `Range/Parameters.lean`, and its fixed-cover
sharp-upper composition is exposed by `Range/SharpUpper.lean`.
The finite-prefix API uses Mathlib's Fin.partialSum throughout; the
project-local blockPartialSums and finiteIncrementSums definitions were
removed. A generic telescope identity supplements the pinned Mathlib
version, which has no `Fin.partialSum_differences` theorem. Variable-length coordinate-block
independence is the base API, and block-sum independence is derived through
measurable finite sums. The dedicated
`BranchingProcessTest/RandomWalk/FiniteDimensionalIndependentBlocks.lean`
test checks zero-, one-, and two-block cases, unequal block lengths, the
equal-length specialization, and zero/nonzero centering shifts; all four
finite-dimensional and block-independence declarations are included in the
axiom allowlist. The tracked baseline previously passed `lake build`; the
current worktree still requires a full build and the test runner. The runner
now discovers tracked and non-ignored untracked Lean tests, so a new test is
not silently skipped before staging. The remaining Mogulskii and restart items
include mathematical proof obligations as well as pending verification.
Hard-truncated increments and their centered versions now
have all finite moments under finite/probability measures without assumptions
on the original moments; the fourth-power block maximal estimate also has
this weak-assumption version. The second-moment maximal estimate now accepts
an explicit one-step center, and adjacent finite-block excursion events have
an exact IID factorization. Combining these gives a squared local block bound
without imposing a global second moment. For `0 < α < 1`, the source's
uncentered convention now supplies the truncation-bias margin automatically:
a layer-cake identity and Karamata's theorem give the normalized capped
first-moment limit, which yields an explicit eventual small-block bias bound.
For `1 < α < 2`, a Mathlib layer-cake identity and the upper-tail Karamata
theorem give the normalized discarded-first-moment limit; under finite first
absolute moment and mean zero this supplies the bias margin and the local
one-block bound automatically. At `α = 1`, the source condition
`n ∫ sin(x / Bₙ) dν → 0` now gives the required hard-truncation bias bound:
compare the truncated mean with the sine transform, controlling the inside
error by the truncated second moment and the outside error by the tail
probability. The bias estimate now feeds the local one-block probability
bound. A generic IID shift theorem moves excursion probabilities between
increment windows; independence gives a product bound for two adjacent blocks.
The block-excursion API also factors adjacent events with different left and
right lengths and bounds a finite union by the sum of their separate
one-block probability products. The stable block-tail adapter now lifts two
separately controlled, possibly unequal block lengths to the product of their
local bounds, at any deterministic starting position; the finite-union API
also has an `Eventually` wrapper for grids and bounds that vary with `n`. Its equal-length grid
specialization gives the eventual squared estimate and an `O(m δ²)` union
bound over any fixed grid of `m` such pairs. `Path/Skorokhod/Oscillation.lean`
proves deterministic inclusions from failures of the generic double-excursion
and endpoint controls to finite increment-window events.
`FunctionalLimit/Stable/Oscillation.lean` bounds those events by the local
squared estimate and two endpoint block estimates.
`FunctionalLimit/Stable/OscillationPartitions.lean` chooses vanishing mesh and
oscillation scales with summable probability budgets, and includes the finite
prefix. `FunctionalLimit/Stable/Tightness.lean` combines this with the range
bound and generic criterion to prove stable J1 tightness in all three
centering regimes. The next path-space obligation is convergence to the stable
process, not tightness.
Under stable tail
regular variation and stable norming, the normalized truncation estimate gives an eventual
`O(δ)` one-block excursion bound for block lengths at most `δn` once the
appropriate bias bound is supplied. The one-block result accepts arbitrary
strict margins above the tail and truncated-second-moment limits, with an
explicit unit-margin convenience specialization. `Path/Skorokhod/Range.lean`
proves that leaving a symmetric closed interval forces a partial-sum
excursion and transfers this estimate to the normalized step-path law.
`FunctionalLimit/Stable/PathRange.lean` selects truncation radius and
excursion threshold to make whole-horizon range exit smaller than any positive
error, then supplies adapters for `α < 1`, `α = 1`, and `1 < α < 2` source
centering assumptions. This is the compact-range input to the generic
Skorokhod tightness criterion. Stable local double-excursion and endpoint
probability bounds now feed the multiscale oscillation-partition estimate and
the three stable J1 tightness theorems.

`Topology/Cadlag/Skorokhod/Compactness.lean` now proves that the step-path
map for one fixed finite partition is nonexpansive from the finite supremum
metric to `J₁`, and that compact sets of cell values yield compact families
of step paths. The vector includes a separate terminal value: càdlàg paths
may jump at time `1`, so cell oscillation only constrains times below `1`.
`Topology/Cadlag/Skorokhod/Oscillation/Partition/Finite.lean` constructs the
partition object from strictly increasing finite time points, and
`Partition/Existence.lean` constructs one for every càdlàg path from local
left/right oscillation bounds and a finite cover. Tests check the construction
axioms, apply it to a constant path, and check a path with a terminal jump.
Compact families in the `J₁` path space have uniformly bounded ranges, by
identifying the distance to the zero path with the uniform norm, and a
pathwise finite-partition oscillation bound can be made uniform across a
compact family without an additional pathwise existence hypothesis.
`Compactness/Approximation.lean` proves the compact-range sufficient criterion
for total boundedness of a path family. The scalar-valued compactness and
closure characterizations there use uniform absolute-value bounds. The new
`Compactness/Billingsley.lean` theorem upgrades the generic compact-range
criterion to a compact superset in `J₁`: it restricts paths to the compact
range subtype, uses Billingsley's complete metric to form a compact closure,
then maps that compact set back to the ambient state space. This does not
assume completeness or properness of the ambient state space. A corresponding
necessary criterion for arbitrary metric-valued path families is still open.
For each fixed positive random-walk step count,
`Probability/Process/RandomWalk/Path/Skorokhod/Oscillation.lean` constructs a
common uniform-grid partition with positive gap and zero within-cell
oscillation for every increment sequence. This handles fixed finite prefixes
pathwise; its gap shrinks with the step count and therefore does not prove
asymptotic stable tightness by itself. The module
`Probability/Process/RandomWalk/Path/Skorokhod/Tightness.lean` uses Mathlib's
complete product-space measure tightness and the continuity of the fixed-step
path map to prove that every finite set of fixed-step path laws is tight. This
handles finite prefixes. `FunctionalLimit/Stable/OscillationPartitions.lean`
now supplies the multiscale tail estimates, and
`FunctionalLimit/Stable/Tightness.lean` proves stable J1 tightness under the
three source centering regimes. The generic
`MeasureTheory/Measure/CadlagPath/Tightness.lean` now proves an all-index
criterion: high-probability containment in a common compact state-space range,
together with a high-probability event carrying a positive mesh and a positive
oscillation threshold tending to zero at every level, implies Mathlib's
`IsTightMeasureSet`. `Topology/Cadlag/Range.lean` defines the generic
`CadlagPath.rangeIn` event for any càdlàg time domain; the
`Topology/Cadlag/Skorokhod/Range.lean` adapter proves it closed and Borel in
the `J₁` path topology, and `Oscillation/Partition/Measurability.lean`
proves the sequence event Borel.
`MeasureTheory/Measure/Tight/Sequence.lean` proves the generic finite-prefix
principle: if every individual law is tight and, for each error tolerance, a
single compact set controls all sufficiently late laws, then the full range
of laws is tight. The eventual càdlàg criterion in
`MeasureTheory/Measure/CadlagPath/Tightness.lean` uses this result to absorb
the finite exceptional indices without a Polish-space instance on the path
space. Stable compact-range bounds and oscillation-partition estimates are
available for the three source centering regimes above, and their combination
proves stable J1 tightness. `FunctionalLimit/Stable/PathLimit/Source.lean`
also proves convergence of the right-continuous path laws to the stable
process. The weak-limit adapter for the separate terminal-left transform is
part of the source endpoint alignment work.

`Topology/Cadlag/Skorokhod/TimeChange/FinitePartition/` now constructs an
increasing piecewise-affine homeomorphism matching two finite partitions and
proves that its distortion is bounded by any uniform bound on the knot
displacements. The same time change transports a source step path to the
target partition, giving a `J₁` distance bound for step paths with common cell
values. These results supply an explicit estimate for nearby step-function
partitions. The compactness characterization for complete path families is
proved in `Compactness/Approximation.lean`.

`Topology/Cadlag/Oscillation.lean` proves separate local oscillation bounds
from left limits and right continuity, including the value at the right-side
interval's initial endpoint. `Partition/Existence.lean` combines these with
Mathlib's open-cover partition lemma to construct a global finite partition.
The compactness characterization for complete subsets is proved. Stable
random-walk J1 tightness is established by the adapter in
`Probability/Process/RandomWalk/FunctionalLimit/Stable/Tightness.lean`, and
the source-regime path-law limit is proved in
`Probability/Process/RandomWalk/FunctionalLimit/Stable/PathLimit/Source.lean`.

The Mogulskii killed-interval spectrum is also split by dependency: `Spectral/Modes.lean`
contains the Dirichlet modes and eigenvectors, `Spectral/Basis.lean` the
orthogonal coordinates, `Spectral/Expansion.lean` the finite matrix-power
identities, and `Spectral/UpperBound.lean` the geometric row-mass estimate.
The former `Spectral/Spectrum.lean` aggregate module has been removed.

## Additional deductions that must not be hidden

1. A random countable branching-step point process must admit the weighted sum and
   its expectation in the extended nonnegative reals. Normalization and any
   conversion to finite real expectations need their own integrability lemmas.
2. The one-step tilted law needs a constructed probability measure. Across
   generations, the tilted increments must be proved independent and identically
   distributed before the random-walk identity is used.
3. The many-to-one induction needs measurability of path tests and a Tonelli
   or conditional-expectation interchange for the child sums. This is now
   proved for the countable-slot realization. Countability belongs to that
   enumeration because `Measurable.tsum` requires it; it is not a restriction
   on the ambient mark or position space. The abstract point-process statement
   must instead use integration against a measurable random counting measure.
4. The restart schedule must be observable generation by generation, including
   failed trials, truncated descendants, and the generation at which the
   decision is announced. Its increasing trial times alone do not prove this.
   In particular $\tau_k$ looks at generation $\tau_k+1$; the candidate
   stopping time is $\sigma_k=\tau_k+1$. For $k\ge2$, this requires defining
   candidate reserve lineages independently of preceding trial outcomes.
5. The finite first-split instance is now proved by a countable
   generation/root partition: on finite completion, the two pre-sampled
   sibling roots have independent descendant fields conditional on the stopped
   domain flow. The generic recursive reserve/lineage product-law API is also
   formalized, and `Restart/RootedTrial/Reserve/Causal.lean` builds a
   generation-enabled candidate source from one pre-sampled reserve spine.
   `Restart/RootedTrial/Coupling.lean` now proves that on a finite successful
   endpoint the actual target rank roots have a fresh descendant field
   independent of the stopped domain past. It transfers the joint law with
   stopped-measurable endpoint positions to the first-`N` population at every
   fixed finite horizon; the focused `RestartCausalReserveCoupling.lean`
   audit passes for all 23 declarations. This does not identify the candidate
   source with the thesis restart frontier or give a random remaining-horizon
   law. Later source trials still require freshness of each selected unused
   reserve subtree relative to the actual explored-coordinate domain.
   Jagers' optional-line branching theorem is relevant to this step, but its
   hypotheses have not been verified for this construction.
6. Mogul'skiĭ must be stated with the exact centering, variance, scaling,
   tube regularity and endpoint conditions used later. The inverse-scale
   argument in `contents/part-1-eng.tex` also uses
   $\Delta<x(L_\Delta+2)$, which requires monotonicity of $L$ (convergence to
   infinity alone is insufficient); the Lean inverse sandwich makes this
   hypothesis explicit. The former comparison with $L_{x(n)}$ had the wrong
   direction when the integer scale overshoots its target; it has been
   replaced by the minimality bound $L_{x(n)-1}+1<n$, which is also proved in
   Lean. `Entrance/CyclicPath.lean` proves the finite IID cyclic-rotation
   transfer, including the moving-boundary drift identity and factor-`n`
   loss; the all-offset theorem is included in the 24-declaration
   `LinearTubeAxioms.lean` build and axiom audit. `Entrance/NormalDomain.lean`
   derives a uniform `q / floor (Delta²)` entrance lower bound from the raw
   finite centered-second-moment assumption, constructing the Gaussian
   clock-process law internally. This cyclic-rotation estimate is retained
   for other callers, but the direct entrance theorem for Lemma 3.5 must
   follow the Brownian-meander argument in Appendix A.2. The separate
   `Analysis/Asymptotics/PolynomialExponential.lean` proves the polynomial
   error comparison needed after that direct entrance theorem. Neither result
   closes the restarted-population comparison.
7. The selected and restarted walk moment estimates require separate proofs;
   ordinary selected-walk estimates do not automatically transfer to restart.
   Waiting displacements are coupled to non-split events; their joint
   transform, rather than a product of marginal transforms, is required.
9. Aïdékon--Hu Lemma 4.8 applies to a killed process selected by a rule
   adapted to the natural generation filtration. Its separate $a=0$ shortcut
   uses the always-binary child law of that paper and does not extend to
   the present general point process. The current retrospective reserve
   construction is not a verified instance of Lemma 4.8. Starting trials
   sequentially only after failures would consume $K\ell=O((\log N)^2)$
   generations for $K,\ell=O(\log N)$ and loses the stated $O(\log N)$
   restart-time budget. A concurrent causal-backbone construction is a
   possible repair, but its population bound, spatial estimate, and
   measurable coupling must be proved before invoking the lemma.
8. Every use of a limit interchange, monotone convergence, Fatou, or uniform
   integrability in the $L^2$ and proposed $L^1$ closures remains a separate
   proof obligation.
