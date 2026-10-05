# Formalization checklist

The statuses below refer to kernel-checked Lean proofs in this repository.
The LaTeX proof is not counted as a Lean proof.

## Measure convolution powers

`MeasureTheory/Measure/Convolution/Power.lean` defines `Measure.convPower`.
Its rotation theorem uses Mathlib's convolution associativity and Dirac unit
laws; it does not assume commutativity. Random-walk callers use this single
recursive definition, with probability and S-finiteness instances.

## Mogulskii small-deviation proof

The general stable-domain Mogulskii theorem is not proved. The source proof is
being formalized in dependency order, keeping the source notation and event
conventions explicit.

- **Lemma 2(a), relation (21): proved for the stable-process indices in the
  model. The canonical public entry is
  `Probability.Process.Stable.SmallDeviation.ShiftedCorridor`; it exposes both
  the Mathlib CDF hypothesis and the source's strict left-mass hypothesis.
  It uses a fixed finite-time entrance and stable scaling. Its recursive import
  graph does not include feedback entrance, path-law support, or the Poisson
  jump-model modules. Unit-time entrance variants remain in
  `ShiftComparison.AllIndices`.
- The source endpoint event is kept left-open and right-closed:
  `c < f(t) ≤ b`. The smaller open endpoint window used for positivity is
  proved sufficient for (21), without identifying the two events.
- **Lemma 2(b), relation (22): proved for the stable-process model.** The
  public module is
  `Probability.Process.Stable.SmallDeviation.RangeComparison`. It proves the
  left comparison from exact corridor/range event inclusions and the right
  comparison by a finite translated-corridor cover, half-width normalization
  into (21), and a general finite-sum logarithmic estimate. Both directions
  are available under the CDF condition and the source's strict left-half-line
  mass condition. The cover's deterministic core is in
  `Order/Bounds/RangeCover.lean`; the original-process event adapter and
  probability bound are in `Probability/Process/Corridor/Range.lean`. This
  proof uses the original sample space and almost-sure càdlàg paths; it does
  not assume a path-space law or Lemma 1's escape-rate limit.
- **Lemma 2(c), relation (23): proved.**
  `Probability.Process.Stable.SmallDeviation.Blocks.Upper.ArbitraryHorizon`
  proves the stated exponent `⌊c⁻¹⌋₊` for any `0 < c ≤ 1`, first on the
  full range event and then for the complete centered corridor. The complete
  corridor is bridged to the full-range event with its exact width `2 * a`.
- **Lemma 2(c), relation (24): proved.**
  `Probability.Process.Stable.SmallDeviation.BlockBounds` proves the seven
  source endpoint-window lower bound with exponent `⌊c⁻¹⌋₊ + 1`. It uses
  five disjoint endpoint bins for the core recurrence, keeps the terminal
  intervals left-open and right-closed (`Ioc`), and runs the last block past
  time `1` before restricting the resulting corridor. No positivity
  assumption on the minimum block probability is added.
- **Lemma 2(c), relation (25): proved.**
  `Probability.Process.Stable.SmallDeviation.EndpointComparison` proves the
  endpoint-constrained logarithmic comparison for `-1 ≤ c < b ≤ 1`. It uses
  a finite cover of possible prefix endpoints, a separate fixed positive
  entrance time for each cover center, stable scaling on the prefix, and a
  fixed multiplicative cost. The endpoint event preserves the source's
  left-open, right-closed interval `(a * c, a * b]`.
- **Lemma 1 (18)--(20): the process-level escape-rate limits are proved.**
  `Probability.Process.Stable.SmallDeviation.EscapeRate` proves that the
  rational range-tube probability has a finite strictly negative normalized
  logarithmic limit, then proves the same constant for the centered corridor,
  translated corridors, and the source's left-open, right-closed endpoint
  windows. The same-law result shows that this constant is determined by the
  stable increment specification, and explicit normalized logarithmic ratios
  for (19)--(20) converge to one. The unit-interval `CadlagPath` escape-rate
  transfer is proved in `Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw`
  by comparing rational-coordinate laws with a stable Lévy process. The proof
  uses the seven-window lower bound,
  the arbitrary-horizon range upper bound, and the existing (21)--(25)
  comparisons. Escape-rate positivity now uses a common small reference width
  chosen from the probability-level form of (25); the endpoint rate uses a
  fixed positive finite entrance time for each buffer width. Neither escape-
  rate proof imports the unit-time `ShiftComparison.AllIndices` route. The
  probability equality under a shared stable increment law is in the generic
  `Probability.Process.Stable.Corridor.Law` module, independently of the
  escape-rate limit. The path-law transfer assumes a reference stable Lévy
  process with the same increment specification; existence of a full-time
  process extension from an arbitrary unit-interval law is not asserted.
- **Stable characteristic-function normalization: proved.**
  `Probability.Distributions.Stable.CharacteristicFunction` derives
  `‖charFun μ t‖ = exp (-c * |t|^α)` with `c > 0` directly from the affine
  `IsAlphaStable` predicate; the proof includes `α = 1` and does not require a
  Lévy--Khintchine triple. General attraction definitions and finite-sum
  characteristic-function formulas are owned by
  `Probability.Distributions.DomainOfAttraction`; the stable specialization
  proves (6)--(7) with one coefficient `c` shared by every frequency in
  `Probability.Distributions.Stable.Attraction.CharacteristicFunction`.
  Together with the norming-ratio and inverse-Tauberian modules, this proves
  increment-tail regular variation for `0 < α < 2` from the characteristic-
  function defect. Compatible norming rescaling is proved for `0 < α < 2` in
  `Stable/Attraction/Norming/Compatibility.lean`; the `α = 2` normal-attraction
  case and its corresponding compatibility result remain open.
- **Stable norming ratios and frequency regular variation: proved.**
  `NormingRatios/Index.lean`, `NormingRatios/UniformDefect.lean`, and
  `NormingRatios/RegularVariation.lean` prove
  `mₙ/n → λ > 0` implies `B(mₙ)/B(n) → λ^(1/α)` without monotonicity,
  `Bₙ → ∞`, compact-uniform convergence of
  `n (1 - |φν(t/Bₙ)|²)`, and
  `(1 - |φν(su)|²)/(1 - |φν(u)|²) → s^α` as `u ↓ 0` for every `s > 0`.
  The inverse-Tauberian chain for `0 < α < 2` is also complete: the exact
  cosine-kernel identity, nonmonotone Potter control, Mellin-kernel limit,
  symmetrized-tail transfer, and truncated-moment ratio are proved in
  `Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail` and
  `Analysis.Fourier.CosineTauberian`. The `α = 2` normal-attraction branch remains open, as do the scale and
  functional-limit steps needed by the source proof.
- **General stable block-scale inverse for `0 < α < 2`: proved.**
  `Analysis.Asymptotics.RegularVariation.Uniform` gives compact-uniform
  ratios with an explicit eventual-monotonicity hypothesis;
  `Analysis.Asymptotics.RegularVariation.AsymptoticInverse` proves sequential
  inversion, including the quotient `u²/V(u)` when `V` is monotone and
  regularly varying with index below two. The stable adapter in
  `Probability.Distributions.Stable.Attraction.Norming.Inverse` derives the
  variation and monotonicity of the truncated second moment, proves that
  `stableScaleTime` diverges without assuming it is monotone, and establishes
  `B_{⌊c κ(aₙ)⌋₊}/aₙ → c^(1/α)` from `0 < α < 2`, slow variation of `L*`, and
  `IsStableNorming`. This closes the general slowly varying scale bridge; it
  does not prove a path-space stable functional limit or the discrete corridor
  estimates.
- **The general stable-domain theorem remains open.** The source path classes,
  energy, approximation framework, and parts of the discrete estimates are
  present; the discrete random-walk estimates, domain-of-attraction diagonal,
  and final theorem assembly are not established.

The shifted-corridor comparison modules are split by mathematical role:
`ShiftComparison.Core` contains the general logarithmic comparison given an
entrance probability; `SmallDeviation.ShiftedCorridor` is the public
finite-time comparison interface; `ShiftComparison.Support` and
`ShiftComparison.Feedback` contain separate sufficient constructions of
entrance positivity. `Lower.PathSupport` holds path-law support consequences
separately from complete-corridor probability estimates. The range comparison
is independently exposed through `SmallDeviation.RangeComparison`.

| Order | Obligation | Status | Reusable source / next step |
|---|---|---|---|
| 1 | Real limit and two-sided speed squeeze | **Done** | `Probability/BranchingRandomWalk/Analytic/SpeedLimit.lean` |
| 2 | First-moment exceptional-event estimate | **Pointwise, independent integral, finite-sum, fresh-subtree, multi-root reserve-vector, and restart-failure forms done** | `Probability/Independence/Integration.lean` owns the general independence identities; `Probability/BranchingRandomWalk/Restart/Reserve.lean` derives them for fresh selected subtrees, and `Restart/FailureEstimate.lean` composes them with candidate-failure measurability. The concrete coupling's reserve observable and failure-event measurability remain to be instantiated. |
| 3 | Random branching step and selected $N$-BRW | **Raw-law construction, measurable sorting interface, abstract ordered slots, and arbitrary-root product law done; tree transport remains** | `Step/Basic.lean` starts from measurable displacement and presence coordinates, so zero children are allowed. `Step/OrderingLaw.lean` pairs an arbitrary raw law with deterministic measurable sorting and defines every indexed $\Xi_i$ only after sorting. `Combinatorics/BranchingWalk/Step/SlotOrder.lean` uses mathlib's order isomorphism to define exhaustive first-$N$ prefixes for an abstract slot order of type $\omega$. `RootIndexed.stepFieldLaw` is an arbitrary-family product law; `Root = \mathbb N` gives one infinite pre-sampling and injective `Fin N` restrictions recover the finite models. `Step/PointMeasureLaw.lean` and `Step/MultiRootLaw.lean` give the point-measure marginals. The remaining construction must transport each sorted child together with its descendant subtree. |
| 4 | Generation filtration, unconditional candidate bifurcation times $\sigma_k=\tau_k+1$, and exploration information $\mathscr H_j$ | **Pre-sampled reserve recursion and every $\sigma_i$ done; model-specific reserve geometry and $\mathscr H_j$ missing** | `Tree/Filtration.lean` proves random-coordinate and causal-lineage measurability assuming only countability of the selector's actual range; the ambient child-slot type may be uncountable. `Genealogy/Lineage/Lineages.lean` defines every causal reserve lineage on the same pre-sampled tree independently of earlier outcomes, proves each path adapted, and proves every visible split completion $\sigma_i$ and the first successful tested completion are stopping times. `Genealogy/Lineage/MultiRoot.lean` does the same for every labelled initial root. The precise range-localized split theorem is in `Timing/DeclaredSplit.lean`. The split-schedule `time_isStoppingTime`, completion, and first-success theorems now take abstract measurable threshold/test events; `_of_countable` corollaries derive them from finite-set cardinality measurability. Countability is therefore attached to that construction rather than to the stopping-time interfaces. The directly touched reserve-lineage and reserve-factorization dependency spine now uses Lean's module system. `BranchingProcessTest/Branching/RestartLineage.lean` checks the stopping-time and first-moment reserve-failure interfaces against the axiom allowlist and keeps the one-generation look-ahead non-stopping counterexample executable. The thesis coupling must still instantiate its reserve geometry, identify the exploration information, and connect its frontier to the stopped-population law. |
| 5 | First success of an adapted process or measurable declaration, including after a stopping start, is a stopping time | **Done, generic** | `Probability/Process/HittingTime/Declarations.lean`, reusing mathlib's `hittingAfter_isStoppingTime`; model-specific reserve observables remain missing |
| 6 | Prove the final $\tau=\tau_\kappa+\ell$ is a generation stopping time | **Generic declaration theorem done; model instance missing** | `Probability/Process/HittingTime/ObservableCandidates.lean` and `Probability/Process/Adapted/Recursion.lean` prove the measurable candidate declaration and causal recursion interfaces. Split-schedule time, completion, and population-success interfaces take measurable threshold and test events; countability is required only by named sufficient corollaries. The marked-tree model must still identify this time with the thesis’s $\tau$ |
| 7 | Branching property at deterministic times | **Selected-population cell laws, abstract position transport, and a dependent random-size descendant law done** | `Genealogy/Exploration/Selected/CellBranching.lean` proves the cellwise product factorization, including current-position tests. `RootIndexed/SelectedSubtrees/Position.lean` transports positions for arbitrary root, family, child-slot, mark, and additive position types. `Abstract/StoppedPopulation/DependentLaw.lean` packages every cardinality into `Σ k, Fin k → subtree` and proves its countable-mixture law. The theorem-specific translated descendant process remains to be instantiated. |
| 8 | Branching at the final time $\tau$ and at intermediate exploration frontiers | **Single root, fixed vectors, finite stopped populations, and the dependent selected-population law done; coupling instance missing** | `Genealogy/Exploration/Abstract/StoppingSubtree.lean` handles one stopped root and `StoppingSubtreeVector/` handles fixed length. `Abstract/StoppedPopulation/DependentLaw.lean` proves measurability and the dependent random-cardinality mixture, including the empty fibre. `Selected/StoppingCellBranching/DependentLaw.lean` instantiates it for `selectedPopulationAt`. `Genealogy/Exploration/Abstract/Exploration/` handles a random unused reserve selected through $\mathscr H_j$. The concrete restart coupling must still identify its final population and reserve frontier with these interfaces. |
| 9 | Both directions of the many-to-one formula | **Enumeration-free endpoint and complete-path formulas proved** | `Probability/PointProcess/Tilted.lean` constructs the tilted law directly from a law on random measures over an arbitrary measurable space. `Spine/PointMeasureEndpoint.lean` proves both endpoint recursions without a slot type or countability assumption. `Spine/PointMeasureRandomWalk.lean` constructs the corresponding single-root spine `RandomWalk`, proves independent identically distributed increments, both endpoint representations, and the existential formulation. `Spine/Path/PointMeasure.lean` defines enumeration-free weighted and unweighted intensities of complete ancestral histories, proves their parameter-dependent measurability and both path-functional formulas, and identifies the labelled genealogy as their realization. `Path/IncrementSplit.lean` supplies the weighted and unweighted head-tail product decompositions. Countability belongs only to the labelled genealogical realization, not to the abstract many-to-one theorems. |
| 10 | General stable-domain Mogul'skii theorem | **Not proved; generic finite-dimensional block transfer is now formalized, but path tightness and the source theorem remain open** | Stable-process Lemma 2, relations (21)–(25), is proved in `Stable/SmallDeviation/{ShiftedCorridor,RangeComparison,BlockBounds,EndpointComparison}.lean`. Process-level Lemma 1, relations (18)–(20), and its unit-interval `CadlagPath` escape-rate transfer are proved in `Stable/SmallDeviation/EscapeRate.lean` and `EscapeRate/PathLaw.lean`; the path-law transfer compares rational-coordinate laws with a reference stable Lévy process of the same increment specification. `Probability/Process/RandomWalk/FunctionalLimit/FiniteDimensional/IndependentBlocks.lean` proves joint convergence for consecutive blocks of unequal lengths and the cumulative endpoint vector from the existing one-dimensional domain-of-attraction block theorem and independent-block laws; the result is generic and does not assume stability of the limit. This is only the finite-dimensional part: stable path tightness and a Skorokhod-space functional limit remain unproved. The discrete random-walk estimates of Lemma 3, domain-of-attraction diagonal of Lemma 4, and Theorems 1 and 2 remain. `IsStableNorming` uses the source condition `B*(B(n))/n → 1`; the finite-variance Donsker/spectral development is not a proof of the general stable-domain theorem.
| 11 | Horizontal and tilted tube estimates, including the entrance lower bound | **Horizontal event, measurability, width monotonicity, reflection, and abstract entrance concatenation done; local entrance estimate missing** | `Probability/Process/RandomWalk/Path/Corridor/Horizontal.lean` defines the exact first-`n` horizontal-tube event and its extended-real log probability, proves the monotonicity lemma omitted in the thesis without assuming positive probability, and proves that reflecting the one-step law exchanges `a` with `1-a`. The general kernel layer proves the entrance-mass times subsequent-survival lower bound. Quantitative upper/lower estimates depend on order 10; completing the boundary entrance step still needs a suitable positive local entrance estimate. |
| 12 | Killed-BRW pair estimate and Paley–Zygmund step | Missing | Depends on orders 7, 9, 11; this is where the cross-term assumption is used |
| 13 | Couplings of selected, killed, and restarted walks | **General causal killed-population interface, product law, capacity-event reduction, and finite-root first-moment spine reduction done; theorem-specific estimates remain** | `Coupling/Field/Law.lean` proves the fixed left-unique coordinate paste law without countability of roots or slots. `GenerationDecomposition.lean` decomposes a field into its pre-generation past and descendant blocks without defaults. `SelectedCoordinates.lean` proves predictable coordinate selection preserves the product law. `Coupling/Rank/Adaptive.lean` constructs the exact step-only block map, proves global injectivity and freshness, and reduces its function-valued fibres and range to random finite supports. `Selection/NSelection/Law/SelectedPopulation.lean` closes the non-circular strong induction for the concrete first-`N` target. `Population/Processes/Causal.lean` stores one set-valued deterministic `Population` at every sample and expresses random adaptation through mathlib's `Filtration` and `Adapted`. `Causal/Predicate.lean` constructs such a process from any generation-observable retention predicate. `Causal/RelativePosition/Real.lean` supplies the restarted spatial-window specialization and a total real-valued killed process. `Causal/PathWindow.lean` proves that every retained particle has a complete ancestral history in the restarted windows. `Causal/FirstMoment.lean` bounds the killed generation size pathwise by the corresponding path observable and then applies the path many-to-one identity to reduce its first moment to the spine. `Causal/Capacity.lean` bounds finite-horizon capacity failure by these generation-size first moments using only a union bound and Markov's inequality. `Selection/NSelection/Law/CausalPopulation.lean` proves measurability and the complete target product law for every such source, and `RootIndexed.causalPopulationCoupling` bundles the common pre-sampled realization as a genuine `ProbabilityTheory.Coupling` with both marginals verified; `Selection/NSelection/Law/Restarted.lean` pulls the restarted killed source back to the left half of the common field, supplies the canonical measure coupling, and constructs the explicit slice-dominating injection directly from membership in that capacity event. Empty generations and arbitrary finite retained offspring are allowed, with no binary-branching assumption. Countability appears only where cardinal measurability or the concrete enumerable-label first-`N` instance needs it. `Combinatorics/BranchingWalk/Walk/Path/Restart.lean` now owns the deterministic restart schedule and restarted-window predicate, and proves that a constant restarted window splits exactly into zero-started prefix and shifted-tail closed-interval events. `Probability/Process/RandomWalk/Path/Restart/Basic.lean` proves that the two finite coordinate blocks are independent under the canonical IID law and hence that the restarted probability factors; `Probability/Process/RandomWalk/Path/Restart/Corridor.lean` identifies the factors with ordinary horizontal-tube probabilities and gives one piecewise formula valid both before and after the cutoff. `Spine/Path/Window.lean` turns that formula directly into the `HasRestartedWindowFirstMomentBound` consumed by the capacity estimate. `Spine/Path/Window.lean` isolates the remaining analytic input as `HasRestartedWindowFirstMomentBound`, proves translation invariance of restarted-window probabilities, controls the exponential endpoint weight deterministically from the window upper bounds, and derives the required uniform first-moment bound from a zero-start window-probability estimate. `Causal/FirstMoment.lean` then turns this bound into the required finite-root capacity estimate and now exposes a direct theorem whose right-hand side contains only the root count, the exponential endpoint factor, and ordinary horizontal-tube probabilities of the tilted one-step law. The remaining obligation is to prove this predicate quantitatively for the thesis windows. |
| 14 | Theorem 1.1, $L^2$ trajectory limit | Missing | Depends on orders 3–13 |
| 15 | Existence of the selected-walk speed | Missing | Formalize the subadditive process and apply an ergodic theorem |
| 16 | Theorem 1.2, speed under fourth moment | Missing | Depends on the preceding estimates and the analytic closure in order 1 |
| 17 | Theorem 1.3, proposed speed under first moment | **Trial timing, pathwise domination, product law, complete path-window control, and finite-root first-moment spine reduction done; quantitative estimates remain** | The split-schedule development proves the geometric trial law, fresh active/reserve product laws, exact original-address transport, and recursive spatial coupling. `Coupling/Rank/Adaptive.lean` represents rank installation by a globally injective fresh-coordinate map. `Selection/NSelection/Law/SelectedPopulation.lean` performs the non-circular stagewise induction. `Population/Processes/Causal.lean` expresses a killed source through deterministic genealogical populations with mathlib `Adapted`; `Causal/Genealogy.lean` proves abstractly, without countability or positional assumptions, that every retained particle descends from its retained zero-generation root along genuine surviving edges; `Causal/Predicate.lean` constructs the process from arbitrary observable predicates and exposes the retained predicate; `Causal/RelativePosition/Real.lean` constructs the total restarted real-position process and proves every retained positive-generation prefix satisfies its prescribed window; `Causal/PathWindow.lean` lifts this to the complete ancestral history; `Causal/FirstMoment.lean` bounds finite-root killed generations by sums of measurable path observables, invokes path many-to-one rootwise, and combines this with the capacity bound; `Causal/Capacity.lean` controls finite-horizon overload by generation-size first moments, with no second-moment hypothesis; and `Selection/NSelection/Law/CausalPopulation.lean` preserves the target product law for this full interface. The spatial process is connected to rank installation by `RootIndexed.restartedRealPositionCoupling`; `restartedRealPositionCoupledInjectionOnRoots` consumes the capacity event itself and proves pathwise domination there. The restarted event has additionally been split at its cutoff into disjoint-coordinate prefix and shifted-tail path events, and their IID probability has been proved to factor exactly into two ordinary horizontal-tube probabilities. The remaining analytic task on this route is now the corresponding zero-start one-dimensional probability estimate for the thesis windows; `Spine/Path/Window.lean` converts it into `HasRestartedWindowFirstMomentBound` without any additional moment assumption. This still includes the unformalized Mogulskii asymptotic. |

The next proof route starts from the random step `Ξ` and keeps every
construction functorial in its mark type. First complete the abstract
many-to-one induction from the existing one-generation kernel and product-
field independence. Then state and prove the exact small-deviation input,
build the killed and selected couplings, and only then close Theorems 1.1--1.3.
The general unmarked branching-process law now starts directly from
`ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι PUnit`; the
marked-walk adapter `StepPresentation.toGaltonWatsonLaw` obtains that input by
forgetting marks. Finite-type offspring-count transition laws remain a
separate formalization task.

The reserve-lineage recursion in order 4 and completion-time identification in order 6 remain prerequisites for invoking the stopped branching property in order 8 without an additional hypothesis.

The assumptions themselves are formalized separately under
`Probability/BranchingRandomWalk/Assumptions/`. `Structural.lean` contains the
nonempty, supercritical, and permutation-invariant boundary-normalization
predicates; `Moments.lean` defines the leftmost moments through a measurable
ordering rule and the permutation-invariant cross weight directly on the raw law, and
proves that the fourth leftmost moment implies the first moment;
`Bundles.lean` records the current theorem-specific groupings. Centering and
finite variance will be stated on the spine law once that probability measure
has been constructed. The possible weakening of the cross-weight assumption
has not yet been asserted as a theorem.

The deterministic layer the theorems select on is formalized under
`Combinatorics/BranchingWalk/Selection/`. `Basic.lean` defines the general
set-valued `Mechanism` without finiteness or capacity, plus `FiniteMechanism`
as an implementation interface for finite inputs. `NSelection/Basic.lean`
adds the exact capacity law; random and causal mechanisms belong under
`Probability/`. `Card.lean` proves the leftmost rule
has the cardinal bound, and `Mirror.lean` obtains the rightmost rule as its
order dual, so one theory covers both directions. `Walk.lean`, `Cloud.lean`,
and `Frontier.lean` build the deterministic `N`-branching walk, the finite
generation slices of its cloud, and their lower and upper frontier sets and
points, with the order-dual identifications
`(V.mapOrderDual).cloud = V.cloud.mapOrderDual` and
`(V.mapOrderDual).lowerFrontier n = OrderDual.toDual '' V.upperFrontier n`.
`Speed.lean` defines the asymptotic speed `p n / n → c` of a frontier path,
proves it unique, and shows that reversing the order exchanges the two frontier
speeds. A generation can be empty, so frontier points and frontier speeds carry
an explicit non-extinction hypothesis; non-extinction of the random walk is
probabilistic and remains open.

## Local dependency layout

The Lean probability modules are arranged by role:

- `MeasureTheory/Measure/`: `FiniteOnFamily.lean` holds the single finiteness condition `IsFiniteOnFamily ν 𝒜` together with the compact, left-ray, and right-ray families; `DiracSum.lean` packages the Dirac sums `Measure.iDiracSum` and `Measure.iOptionDiracSum` on top of mathlib's `Measure.sum`/`Measure.count` API and proves that optional Dirac sums are integer-valued with multiplicity; `IntegerValued.lean` defines `Measure.IsIntegerValued` as the requirement that every measurable set have natural or infinite mass, without asserting a countable Dirac representation; `Domination.lean` derives a.e. finiteness on a family from an integrable dominating functional, the abstract form of the paper's `ψ(1) = 0` computation; `AtomFiniteness.lean` gives the deterministic finite-sublevel input to the enumeration.
- `Probability/PointProcess/`: `Basic.lean` holds `PointProcess Ω E 𝒜`, the abstract random measure with integer-valued samples and a separately parameterized finiteness family. Integer-valuedness alone is not a point enumeration theorem. The object is a random measure, so it lives under `Probability/` in the `ProbabilityTheory` namespace, following Mathlib's `Probability/Kernel/`.
- `Probability/BranchingProcess/`: `Offspring/Law.lean` defines a probability law on complete optional unit-marked offspring configurations and its independent address field; `GaltonWatson/Generation.lean` pushes that law to the existing unmarked process object and proves the one-root generation-zero count; `GaltonWatson/BranchingProperty.lean` states the coordinate independence at the process boundary. `Combinatorics/BranchingWalk/Basic/GenerationSize.lean` proves zero-population absorption for any realized walk, including infinite roots and slots. The standard integer-valued population-size transition chain for finite offspring configurations remains open.
- `Combinatorics/BranchingWalk/Step/PointMeasure.lean`: the deterministic Dirac sum `stepPointMeasure` of a branching step, equal to `Measure.iOptionDiracSum`, with its per-slot atoms and evaluation lemmas. `Combinatorics/BranchingWalk/Cloud/SliceMeasure.lean` defines the cloud Dirac sum `Cloud.diracSum C t`, the sum of `Measure.dirac` over the particles alive at `t` with multiplicity, and evaluates it on a countable slice at any threshold as the count of the particles at most there (`Cloud.diracSum_Iic_eq_encard_of_countable`). `Cloud/Order/Slice.lean` states the slice order `SliceDominatesMeasure` on those measures together with the rankwise form `Cloud.RankwiseDominates`, the two being equivalent on a finite slice; `Cloud/Order/Basic.lean` states the order at every time as `Cloud.Dominates`, with its mirror through `OrderDual`.
- `Probability/BranchingRandomWalk/Step/`: `Basic.lean` defines `stepLaw` directly on measurable maps into `ι → Option X`; `Presentation.lean` defines the coordinate sampling structure `StepPresentation Ω ι X`, whose absent-slot displacement is ignored when it assembles to an optional field. `PointMeasure.lean` defines the general `pointMeasureOf` and `branchingLawOf` observations for raw optional fields, while `StepPresentation` supplies convenience adapters. `Field.lean` adds the `TreeNode ι` index; `PointProcess.lean` adapts the observation to the generic point-process interface; `Order.lean` and `MultiRootLaw.lean` transfer structural properties and marginals.
- `Probability/BranchingRandomWalk/Genealogy/`: marked Ulam--Harris trees, the generation domain filtration, positions, first observable splits, and multiple initial roots.
- `Probability/BranchingRandomWalk/Step/`: fixed and generation-measurably selected subtree product laws, including the multi-root versions.
- `Probability/BranchingRandomWalk/Population/`: `Candidates/` for finite ranking and truncation, `Processes/` for selected and retained recursions, and `Growth/` for deterministic size lemmas.
- `Probability/BranchingRandomWalk/Timing/`: generic stopping-time and measurability lemmas, timing counterexamples, and geometric trials.

All of these are reached from the library roots listed in `lakefile.toml`; `Probability/BranchingRandomWalk/Spine/`, `Analytic/`, and `Restart/` remain separate because they are proof layers rather than probability-space definitions. `Probability/Independence/Integration.lean` contains general first-moment factorization identities; `Restart/Reserve.lean` connects them to fresh subtrees and multi-root reserve vectors, `Restart/FailureEstimate.lean` handles candidate failure, and `Analytic/SpeedLimit.lean` contains the final two-sided squeeze. Within one initial ancestor, a *single* i.i.d. pre-sampled marked tree supplies every reserve branch. An arbitrary family `κ` of distinct same-generation roots indexes descendant marked trees in `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/JointSubtrees.lean`, where their joint product law is proved. Random population size, stopped generations, position offsets, and stopping-line frontiers require the later dependent interfaces.

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
node's reproduction step is revealed when its children appear. The
remaining tree-level sorting obligation must transport each relabelled child
together with its descendant subtree, rather than reorder only its displacement.
The earlier ranked-atom and measure-to-step chain remains deleted. Mathlib
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
  `RootIndexed.BranchingWalk.IsOrderable`, both found by instance search from the finitely supported ones),
  and `StepField.markedTreeOfOrderable'` reads the ordered marked tree with nothing handed in but finite
  support. Neither class is about `ℕ`: only the instance turning finite support into orderability is.
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
- `Probability/BranchingRandomWalk/Assumptions/`, `Spine/`, and `Analytic/` are compiled directly by the source globs; no umbrella module is needed. `Assumptions/Moments.lean` carries the first-, fourth-, and exponential-moment conditions plus the cross-term weight `∑_{i ≠ j} exp(-(Ξᵢ+Ξⱼ))`; it builds, and `fourthMoment_implies_firstMoment` proves the fourth moment condition implies the first.
- `Probability/BranchingRandomWalk/Spine/FiniteKernel.lean` contains the finite child algebra
  for **both** many-to-one variants. It is not the expectation identity for
  random child and is not marked as the full theorem.
- `Probability/BranchingRandomWalk/Analytic/SpeedLimit.lean` contains the final deterministic speed squeeze
  and an elementary first-moment truncation inequality.

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
interfaces, the Markov/strong-Markov process interfaces, the increment-domain
filtration, and the stopping-time/timing interfaces are now Lean modules. The
finite corridor-cover, path-oscillation, exceptional-event, finite-kernel,
moment-assumption, deterministic `NSelection`, spine path/endpoint/point-measure,
root-indexed genealogy, selected-population, and split-schedule interfaces are
also moduleized at their generic or application seams. Their imports are public
only where the imported declarations form that layer's API; no umbrella
re-export file was introduced.

The 2026-10-05 full build completed all 4383 Lake jobs. The pinned Mathlib
style linter passed over all 792 production Lean modules. The repository
verification suite contains 50 Lean tests and 28 Python tests. Mathlib's own
`lint-style.lean` emits a module-header warning under `requiresModuleSystem`;
that warning is in the pinned dependency script, not a project module. The
visualizer manifest is checked both in the Pages workflow and in the required
Lake build job, so stale declaration names fail the required check. The module-header
contract is parser-checked for the two stable escape-rate modules; other legacy
files still use Lean's traditional import header and are not implicitly
claimed to have migrated to the opt-in module system. The random-walk
Mogulskii subtree now consistently uses
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii`, while generic path
classes remain under `ProbabilityTheory.Process.SmallDeviation.Mogulskii`.
The singleton-walk optional-increment representation now has a measurable
equivalence, the stable path-law escape proof factors through an exact tube
probability transfer, and `Analysis.Asymptotics.SlowDiagonal` provides the
general slowly growing diagonal used by fixed-parameter arguments. The first
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
measurable finite sums. The tracked tree passes `lake build`. The remaining
Mogulskii and restart items are mathematical proof obligations rather than
import failures. Hard-truncated increments and their centered versions now
have all finite moments under finite/probability measures without assumptions
on the original moments; the fourth-power block maximal estimate also has
this weak-assumption version. The second-moment maximal estimate now accepts
an explicit one-step center, and adjacent finite-block excursion events have
an exact IID factorization. Combining these gives a squared local block bound
without imposing a global second moment; source-specific centering and
asymptotic J1-modulus estimates remain open.

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
5. The stopped branching property requires independence of all descendant
   subtrees from the stopped sigma algebra, with countably many possible
   generations and a random surviving particle set.
   The intermediate reboot trials instead require an exploration sigma
   algebra $\mathscr H_j$ and a proof that the selected unused reserve subtree
   is fresh. A direct countable-coordinate partition could replace a general
   stopping-line theorem, but still needs the same no-look-ahead property.
6. Mogul'skiĭ must be stated with the exact centering, variance, scaling,
   tube regularity and endpoint conditions used later. The inverse-scale
   argument in `contents/part-1-eng.tex` also uses
   $\Delta<x(L_\Delta+2)$, which requires monotonicity of $L$ (convergence to
   infinity alone is insufficient); the Lean inverse sandwich makes this
   hypothesis explicit. The former comparison with $L_{x(n)}$ had the wrong
   direction when the integer scale overshoots its target; it has been
   replaced by the minimality bound $L_{x(n)-1}+1<n$, which is also proved in
   Lean. The tilted entrance lower bound additionally needs a local or ballot
   lower estimate.
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
