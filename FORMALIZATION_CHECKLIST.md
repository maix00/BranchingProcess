# Formalization checklist

The statuses below refer to kernel-checked Lean proofs in this repository.
The LaTeX proof is not counted as a Lean proof.

| Order | Obligation | Status | Reusable source / next step |
|---|---|---|---|
| 1 | Real limit and two-sided speed squeeze | **Done** | `Probability/BranchingRandomWalk/Analytic/SpeedLimit.lean` |
| 2 | First-moment exceptional-event estimate | **Pointwise, independent integral, fresh-subtree, and multi-root reserve-vector forms done** | `Analytic/ExceptionalEvent.lean` proves the abstract estimate; `Analytic/ReserveLineage.lean` derives it for measurable observables of a fresh reserve subtree and for a generation-measurably selected vector of distinct reserve subtrees. The concrete coupling's reserve observable and failure-event measurability remain to be instantiated. |
| 3 | Random branching step and selected $N$-BRW | **Done at the construction, measurability, and multi-root-law level** | `Probability/BranchingRandomWalk/Step/Basic.lean` starts from measurable $X$-valued displacement coordinates and separate measurable presence coordinates, so zero children are allowed. `Step/PointMeasureLaw.lean` derives the point-measure law by pushforward, and `Step/MultiRootLaw.lean` transfers it to every address of every labelled root. `Population/Processes/Selected.lean` gives the adapted selected process and size bound; nonextinction additionally requires an at-least-one-child assumption. |
| 4 | Generation filtration, unconditional candidate bifurcation times $\sigma_k=\tau_k+1$, and exploration information $\mathscr H_j$ | **Countable pre-sampled reserve recursion and every $\sigma_i$ done; model-specific reserve geometry and $\mathscr H_j$ missing** | `Genealogy/Lineage/Lineages.lean` defines every causal reserve lineage on the same pre-sampled tree independently of earlier outcomes, proves each path adapted, and proves every visible split completion $\sigma_i$ and the first successful tested completion are stopping times; `Genealogy/Lineage/MultiRoot.lean` does the same for every labelled initial root. The generic split theorem is in `Probability/BranchingRandomWalk/Timing/DeclaredSplit.lean`; the old weighted-slot wrapper is isolated in `Probability/BranchingRandomWalk/Timing/FirstSplit.lean`. The thesis coupling must instantiate the reserve paths and define its exploration information. |
| 5 | First success of an adapted process or measurable declaration, including after a stopping start, is a stopping time | **Done, generic** | `Probability/BranchingRandomWalk/Timing/Stopping.lean`, reusing mathlib's `hittingAfter_isStoppingTime`; model-specific reserve observables remain missing |
| 6 | Prove the final $\tau=\tau_\kappa+\ell$ is a generation stopping time | **Generic declaration theorem done; model instance missing** | `Probability/BranchingRandomWalk/Timing/Measurability.lean` proves that stopping candidate completions and adapted generation tests give a stopping first-success time; the marked-tree model must still verify the hypotheses and identify this time with the thesis’s $\tau$ |
| 7 | Branching property at deterministic times | **Selected-population branching on every finite-set cell and measurable current-position tests done; a single dependent random-size law and translated descendant process missing** | `Genealogy/Exploration/Selected/CellBranching.lean` proves that each event specifying the actual selected set is generation-domain measurable, constructs its duplicate-free enumeration, and gives the joint product factorization on that event, including events testing all current particle positions; `Genealogy/Exploration/Selected/Descendants.lean` supplies the dependent descendant population and its translated positions. `Genealogy/Exploration/Selected/StoppingCellBranching/` is the same statement for a population selected at a stopping time. `Genealogy/RootIndexed/Positions.lean` supplies the abstract multi-root step-field law, independent root coordinates, and the deterministic multi-root marked-tree construction. Next package all cardinalities into one dependent random-size law and define descendants translated by those positions |
| 8 | Branching at the final time $\tau$ and at intermediate exploration frontiers | **Single root, fixed-cardinality vector, every finite-population cell at a finite stopping time, and the selected-population stopping-cell interface done; dependent packaging and coupling instance missing** | `Genealogy/Exploration/Abstract/StoppingSubtree.lean` handles one stopped-measurable root. `Genealogy/Exploration/Abstract/StoppingSubtreeVector/` handles a fixed-length random vector. `Genealogy/Exploration/Selected/StoppingPopulation.lean and Genealogy/Exploration/Selected/StoppingCellBranching/` partitions a stopped finite population by its set value and stopping generation, enumerates each cell without duplicates, and proves the multi-root product subtree law, including the empty cell. It also defines the concrete `selectedPopulationAt`, proves its stopping-cell measurability and depth interface, and instantiates the abstract theorem as `selectedPopulation_stopped_cell_branches`. `Genealogy/Exploration/Abstract/Exploration/` handles a random unused reserve selected through $\mathscr H_j$. It remains to package all cardinalities in one dependent object and instantiate the concrete coupling. |
| 9 | Both directions of the many-to-one formula | **Finite algebra, exponential specialization, measurable monotone truncations, exact supremum limit, normalized slot PMF, nonzero weight, coordinate measurability, almost-everywhere domain validity, almost-everywhere mass-one, reindexed displacement independence, and tilted displacement law done; probabilistic theorem missing** | `Probability/BranchingRandomWalk/Spine/FiniteKernel.lean` proves weighted and unweighted cancellation, specializes the weighted direction to exponential weights, and proves the exponential normalizer is nonzero for every nonempty finite family. `Probability/BranchingRandomWalk/Spine/TruncatedWeights.lean` defines the first-$n$ slot exponential weight, proves measurability, monotonicity, domination, and `⨆ n, truncatedChildWeight n = totalChildWeight`. `Probability/BranchingRandomWalk/Spine/TiltedSlot.lean` reuses mathlib's `PMF.normalize`, proves its mass-one and weighted tsum identities, shows a nonempty child mark has nonzero total weight, proves normalized coordinates are measurable on the whole mark space, proves their total mass is one almost surely, and defines the pushed-forward tilted displacement law. `Probability/BranchingRandomWalk/Step/DisplacementLaw.lean` proves injectively reindexed mark coordinates and displacement observables remain jointly independent. Next: establish the random-law measurability and product law of the actual tilted increment sequence, then induction, following Shi §1.3 |
| 10 | Mogul'skiĭ small-deviation theorem for the finite-variance spine | Missing | No Lean formalization found in the checked mathlib tree or public search; would require a substantial invariance/small-ball development |
| 11 | Horizontal and tilted tube estimates, including the entrance lower bound | Missing | Depends on orders 9–10; the LaTeX entrance estimate also needs a lower local-limit theorem |
| 12 | Killed-BRW pair estimate and Paley–Zygmund step | Missing | Depends on orders 7, 9, 11; this is where the cross-term assumption is used |
| 13 | Couplings of selected, killed, and restarted walks | **Causal truncated populations, random-start adaptation, and finite concurrent-union interface done; concrete parallel restart and comparison missing** | `Population/Processes/Retained/` models the backbone law $\Xi^{(M)\mathrm b}$ and proves nonextinction only under an explicit first-child hypothesis. `Population/Processes/Truncated.lean` models $\Xi^{(M)}$, where both children are truncated and extinction is possible. Both processes are adapted and satisfy $Z_n\le2^n$. `Population/Processes/Parallel/Basic.lean` proves adaptation and cardinal bounds for an adapted finite concurrent union. `Parallel/Started.lean` proves that a candidate process born at an observable stopping generation, empty beforehand and indexed by its local age afterwards, is adapted in global time. The concrete trial activation rule, joint coupled law, and rankwise comparison with the selected process remain to be proved. |
| 14 | Theorem 1.1, $L^2$ trajectory limit | Missing | Depends on orders 3–13 |
| 15 | Existence of the selected-walk speed | Missing | Formalize the subadditive process and apply an ergodic theorem |
| 16 | Theorem 1.2, speed under fourth moment | Missing | Depends on the preceding estimates and the analytic closure in order 1 |
| 17 | Theorem 1.3, proposed speed under first moment | **Abstract fresh-reserve and fixed-generation multi-root reductions done; coupling instance missing** | `Analytic/ExceptionalEvent.lean` proves the exact $L^1$ factorization. `Analytic/ReserveLineage.lean` connects it both to an exploration-measurably selected fresh subtree and to an observable of a generation-measurably selected vector of distinct reserve subtrees for $m$ labelled initial roots. The remaining task is to define the concrete restart observable and prove that its failure event and reserve choice meet one of these interfaces. Mere truncation plus a polynomial event bound is insufficient for an arbitrary integrable tail. |

The next proof route starts from the random step `Ξ` and keeps every construction functorial in its mark type. First complete the abstract many-to-one induction from the existing one-generation kernel and product-field independence. Then state and prove the exact small-deviation input, build the killed and selected couplings, and only then close Theorems 1.1--1.3. The unmarked Galton--Watson arguments use `Ξ.galtonWatsonFieldLaw`, obtained by mapping marks to `PUnit`; they do not introduce a second reproduction model.

The reserve-lineage recursion in order 4 and completion-time identification in order 6 remain prerequisites for invoking the stopped branching property in order 8 without an additional hypothesis.

The assumptions themselves are formalized separately under
`Probability/BranchingRandomWalk/Assumptions/`. `Structural.lean` contains the ordered-support,
nonempty, supercritical, and boundary-normalization predicates;
`Moments.lean` contains the leftmost and cross-weight moment predicates and
proves that the fourth leftmost moment implies the first moment;
`Bundles.lean` records the current theorem-specific groupings. Centering and
finite variance will be stated on the spine law once that probability measure
has been constructed. The possible weakening of the cross-weight assumption
has not yet been asserted as a theorem.

The deterministic layer the theorems select on is formalized under
`Combinatorics/BranchingWalk/Selection/`. `Basic.lean` defines a *selection
mechanism* of capacity `N` as a deterministic map from a finite candidate set
to a sub-collection of at most `N` candidates; a random mechanism is a law on
this type and belongs to `Probability/`. `Card.lean` proves the leftmost rule
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

- `MeasureTheory/Measure/`: `FiniteOnFamily.lean` holds the single finiteness condition `IsFiniteOnFamily ν 𝒜` together with the compact, left-ray, and right-ray families; `DiracSum.lean` packages the Dirac sums `Measure.iDiracSum` and `Measure.iOptionDiracSum` on top of mathlib's `Measure.sum`/`Measure.count` API; `Domination.lean` derives a.e. finiteness on a family from an integrable dominating functional, the abstract form of the paper's `ψ(1) = 0` computation; `AtomFiniteness.lean` gives the deterministic finite-sublevel input to the enumeration.
- `Probability/PointProcess/`: `Basic.lean` holds `PointProcess Ω E 𝒜`, the abstract random counting measure, whose finiteness family is a parameter rather than a hardcoded condition. The object is a random measure, so it lives under `Probability/` in the `ProbabilityTheory` namespace, following Mathlib's `Probability/Kernel/`.
- `Combinatorics/BranchingWalk/Step/PointMeasure.lean`: the deterministic Dirac sum `stepPointMeasure` of a branching step, equal to `Measure.iOptionDiracSum`, with its per-slot atoms and evaluation lemmas. `Combinatorics/BranchingWalk/Cloud/SliceMeasure.lean` defines the cloud Dirac sum `Cloud.diracSum C t`, the sum of `Measure.dirac` over the particles alive at `t` with multiplicity, and evaluates it on a countable slice at any threshold as the count of the particles at most there (`Cloud.diracSum_Iic_eq_encard_of_countable`). `Cloud/Order/Slice.lean` states the slice order `SliceDominatesMeasure` on those measures together with the rankwise form `Cloud.RankwiseDominates`, the two being equivalent on a finite slice; `Cloud/Order/Basic.lean` states the order at every time as `Cloud.Dominates`, with its mirror through `OrderDual`.
- `Probability/BranchingRandomWalk/Step/`: `Basic.lean` defines `StepDisplace Ω X = Ω → X` and an `ι`-indexed random step with measurable displacement and Boolean presence coordinates; `Option X` is introduced only by realization. `Field.lean` adds the `TreeNode ι` index. `Step.indexedLaw` is the enumeration-dependent auxiliary law, while `Step.branchingLaw` is the law of the resulting point measure. `PointMeasure.lean` and `PointMeasureLaw.lean` derive the forward Dirac-sum observation and its law; `PointProcess.lean` adapts it to the generic point-process interface; `Order.lean` and `MultiRootLaw.lean` transfer structural properties and marginals.
- `Probability/BranchingRandomWalk/Genealogy/`: marked Ulam--Harris trees, the generation domain filtration, positions, first observable splits, and multiple initial roots.
- `Probability/BranchingRandomWalk/Step/`: fixed and generation-measurably selected subtree product laws, including the multi-root versions.
- `Probability/BranchingRandomWalk/Population/`: `Candidates/` for finite ranking and truncation, `Processes/` for selected and retained recursions, and `Growth/` for deterministic size lemmas.
- `Probability/BranchingRandomWalk/Timing/`: generic stopping-time and measurability lemmas, timing counterexamples, and geometric trials.

All of these are reached from the library roots listed in `lakefile.toml`; `Probability/BranchingRandomWalk/Spine/` and `Analytic/` remain separate because they are proof layers rather than probability-space definitions. `Analytic/ExceptionalEvent.lean` contains first-moment exceptional-event estimates, `Analytic/ReserveLineage.lean` connects them to fresh reserve subtrees and multi-root reserve vectors, and `Analytic/SpeedLimit.lean` contains the final two-sided squeeze. Within one initial ancestor, a *single* i.i.d. pre-sampled marked tree supplies every reserve branch. A finite vector of same-generation roots indexes descendant marked trees in `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/JointSubtrees.lean`; their joint product law is proved there. The vector length is fixed at the theorem interface. Random population size, stopped generations, position offsets, and stopping-line frontiers are not covered by that theorem.

For the theorem with $m_N=\lfloor N^\alpha\rfloor$ **initial particles**, `Probability/BranchingRandomWalk/Genealogy/RootIndexed/Law.lean` uses $m_N$ labelled initial roots through the `Fin m_N` instance `finiteRootStepFieldLaw`, each root with its own pre-sampled Ulam--Harris tree; the labelled law, filtration, and positions are that instance, not a separate copy. The initial positions are supplied as `Fin m_N → ℝ`, so all-zero starts and later common shifts are representable. `Genealogy/Exploration/Selected/CellBranching.lean` and `Genealogy/Exploration/Selected/StoppingCellBranching/` prove deterministic-generation branching across these roots, including roots selected using the entire multi-root domain filtration. `Population/Processes/Selected.lean` defines one common selection pool, proves its labelled set adapted, bounds its size by $N$ after the first generation, and proves nonextinction under an explicit pathwise first-child hypothesis. `Probability/BranchingRandomWalk/Step/OrderedSupport.lean` derives that hypothesis almost surely from ordered support together with the thesis's at-least-one-child assumption. The earlier single-tree statements concern descendants of one initial ancestor and cannot substitute for this multi-root process.
`Population/Candidates/MultiRoot.lean` makes the finite step explicit. `Population/Candidates/Adapted.lean` proves that an adapted finite parent set produces a measurable candidate set at the next generation, by partitioning over the countable parent-set values. `Combinatorics/BranchingWalk/Step/Monotone.lean` proves local prefix and displacement witnesses for later slots. `Population/Candidates/Ordering.lean and Population/Candidates/Leftmost.lean` proves a deterministic rank rule and its cardinal bound. Its tie key compares parent identity, then the child's slot number, then a full-address fallback; `candidateEarlier_ordered_siblings` proves earlier siblings beat later siblings even at equal displacement. The first version's arbitrary full-address code did not have this property and was corrected. `Population/Candidates/FullRank/ and Population/Candidates/FullSelection.lean` proves exact equality between finite first-$N$-slot selection and full countable-child selection under ordered marks, pointwise at every generation and almost surely under an ordered-support mark law. The ordered step is part of the random input `Ξ`; the remaining gap at this layer is transferring the stated ordered-support hypothesis through the concrete coupled laws. `Genealogy/Exploration/Selected/CellBranching.lean` adds a product descendant-tree law on every cell specifying the actual finite selected set. `Genealogy/Exploration/Selected/StoppingPopulation.lean and Genealogy/Exploration/Selected/StoppingCellBranching/` proves the analogous cellwise statement for any stopped-measurable finite population under the multi-root filtration, supplies `selectedPopulationAt`, its cell measurability and stopped-depth implication, and instantiates the concrete theorem `selectedPopulation_stopped_cell_branches` for the selected process. It also proves the countable population-cell partition and its measure sum. It partitions by the finite population value and the stopping generation, so no stopping-line abstraction is needed for this theorem. A single dependent random-size law and the concrete coupling instance remain open.

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
pointwise `IsOrderable` alone does not imply measurability of a choice. If the
input coordinates are already the paper's ordered $\Xi_i$, `Step/Order.lean`
instead transfers the ordered-support hypothesis directly through their law.
The earlier ranked-atom and measure-to-step chain remains deleted. Mathlib
measures and Dirac sums are reused for the forward point-measure observation.

An external Lean 4 project, [LeanLevy](https://github.com/slink/LeanLevy),
constructs a Poisson random measure by summing Dirac measures at realized
points; see its [`PoissonRandomMeasure.lean`](https://github.com/slink/LeanLevy/blob/main/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean).
This confirms the reusable mathlib construction pattern but its Poisson
point-family assumptions are not the thesis's arbitrary reproduction law.
Mathlib's [`HasPDF`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Density.html)
means absolute continuity of a random variable's law relative to a reference
measure. It is not the definition of a point process and is not assumed for
the present atomic child measure. The Brownian-motion development uses
process and Gaussian-law APIs, not a general point-process representation.
`Probability/BranchingRandomWalk/Step/OrderedSupport.lean` proves that if the one-node mark law gives this ordered subset probability one, then every address in the entire pre-sampled tree has an ordered mark simultaneously almost surely. This uses mathlib's countable almost-everywhere intersection and the proved one-node marginals; it does not itself establish the antecedent from the abstract branching-step point process.

- `Probability/BranchingRandomWalk/Timing/Stopping.lean` contains only the thesis-specific
  adaptation of mathlib's `hittingAfter_isStoppingTime`. It does not redefine
  filtration, measurable space or stopping time.
- `Probability/BranchingRandomWalk/Timing/TimingCounterexample.lean` gives kernel-checked
  counterexamples to the original look-ahead stopping-time claim and to automatic
  adaptedness of a generation-one state chosen from a generation-two outcome.
  It also proves that an adapted population count need not make the retained
  particle identity adapted. In the thesis
  model itself, $\{\tau_1\le0\}$ has probability $p_0\in(0,1)$ in an allowed
  parameter case, whereas $\mathcal F_0$ is trivial. This does not settle
  whether the final successful completion time $\tau$ is a stopping time.
- `Probability/BranchingRandomWalk/Timing/Measurability.lean` proves the measurable candidate declaration and causal recursion interfaces. It does not construct the marked tree, reserve candidates, or coupling.
- `Combinatorics/UlamHarris/Basic.lean` defines the address type `TreeNode`, its `ℕ`-indexed instance `𝕍`, and the mark function `Mark`; `Combinatorics/UlamHarris/Tree/Basic.lean` defines `Tree` (a deterministic tree with root, parent, and ordered-sibling axioms) together with its measurable space, generated by membership of every address in the carrier; `Combinatorics/UlamHarris/MarkedTree/Basic.lean` defines `MarkedTree` (a realized tree with marks on realized nodes), its partial mark views, and its measurable space, induced by the tree together with the `Option`-valued mark reading. `Probability/BranchingRandomWalk/Tree/Filtration.lean` defines the generation filtration on the mark field, including the trivial generation-zero σ-algebra, and proves fixed-node, dynamically selected-node, and causal-lineage measurability. `Combinatorics/BranchingWalk/` defines the step field `BranchingWalk` with its realized tree, displacements, and the derived marked trees `markedTreeOfStep` and `RootIndexed.BranchingWalk.markedTree`. `Probability/BranchingRandomWalk/Timing/DeclaredSplit.lean` contains the model-specific first observable split theorem. `Combinatorics/UlamHarris/Tree/Graph/` projects a tree onto mathlib's graph objects on the realized carrier: the single address-level parent relation `Tree.parentRel`, the digraph, quiver, and simple-graph views, and `childGraph_isTree`, proving that the projected graph is a `SimpleGraph.IsTree`. The root-indexed family is projected as the forest `UlamHarris.RootIndexed.forestGraph`, the disjoint union of the child graphs of the family: it is acyclic however many initial ancestors there are, it is connected and a `SimpleGraph.IsTree` exactly in the one-root case, and `UlamHarris.RootIndexed.uniqueForestGraphIso` identifies that one-root forest with `Tree.childGraph`, so the `Tree` statements are its specialization.
- The current branching-step layer is intentionally direct: `Combinatorics.Branching.RootIndexed.BranchingWalk` stores one `StepField` and initial population per root and requires `IsParentClosed` via `surviveAlong`. The slot-level condition `Step.IsSiblingClosed` is separate and says that surviving sibling slots form an initial segment. Orderedness is the property `Step.IsOrdered`; there is no `OrderedStep` wrapper. `Step.siblingCardinal` gives the general predecessor cardinal, while `Step.siblingRank` and its `ℕ` theorem apply to finite-predecessor canonical enumerations. Marked-tree correspondence and sibling mark monotonicity remain in `Combinatorics/UlamHarris/MarkedTree/` and use these explicit predicates. A finitely supported step on `ℕ` has an increasing enumeration of its children, built by rank and without
  sorting a list (`Step.hasIncreasingEnumeration_of_isFinitelySupported`), and is orderable by
  `Step.isOrderable_of_hasIncreasingEnumeration`, whose relabelling is that enumeration itself. Orderability
  lifts to a step field and to a root-indexed walk (`StepField.IsOrderable`,
  `RootIndexed.BranchingWalk.IsOrderable`, both found by instance search from the finitely supported ones),
  and `StepField.markedTreeOfOrderable'` reads the ordered marked tree with nothing handed in but finite
  support. Neither class is about `ℕ`: only the instance turning finite support into orderability is.
- `Combinatorics/BranchingWalk/Selection/` now hosts the walk-level selection layer. `Selection/Contain.lean` defines `SelectContain`, the containment order on `BranchingWalk` (`ω` keeps a subset of the children of `ω'`, pointwise, with the same displacements) and proves it is a partial order. `Selection/Mechanism.lean` defines `SelectionMechanism`, a map `BranchingWalk α X → BranchingWalk α X` that is `SelectContain`-decreasing. `Selection/NSelection/Basic.lean` defines `IsNBranching`, `NBranchingWalk` (at most `N` children per node), and `NSelection`, a `SelectionMechanism` whose image is `N`-branching. The random counterparts are `Probability/BranchingRandomWalk/Basic.lean` (`BranchingRandomWalk`, a probability law on `BranchingWalk`, with the i.i.d. instance `iid μ`) and `Probability/BranchingRandomWalk/Selection/NSelection/Basic.lean` (`NBranchingRandomWalk`).
- `Combinatorics/BranchingWalk/Step/Measurability.lean` gives the measurable support conditions and the concrete truncation rules. The all-absent mark represents zero children; `Probability/BranchingRandomWalk/Step/DisplacementLaw.lean` supplies the concrete i.i.d. tree law, but no binomial lower-tail estimate has yet been proved for the retained population.
- `Probability/BranchingRandomWalk/Population/Processes/Retained/` instantiates the causal backbone recursion as a finite set of labelled particles. It proves adaptation, $Z_n\le2^n$, and conditional nonextinction under a first-child hypothesis. `Processes/Truncated.lean` separately implements the possibly empty fully truncated law $\Xi^{(M)}$ and proves its adaptation and binary upper bound without claiming nonextinction.
- `Probability/BranchingRandomWalk/Step/DisplacementLaw.lean` reuses mathlib's `Measure.infinitePi`, `infinitePi_map_eval`, and `iIndepFun_infinitePi` for a pre-sampled i.i.d. family at every genealogical address. The random law is parametrized; no moment or ordering hypothesis is silently imposed.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/Exploration/` and `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/Property.lean` reuse mathlib's `indep_iSup_of_disjoint` and `Measure.map_infinitePi_infinitePi_of_inj`. It proves the actual generation domain is independent of all future raw marks, each fixed descendant subtree has the original i.i.d. law, and two distinct same-depth descendant domains are independent. It does not yet cover the joint random surviving set or positions.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Selected/AbstractSubtree.lean` proves the selected subtree is measurable for a generation-domain-measurable root; if that root has the current depth, a countable measurable partition gives the exact past/subtree event factorization, the original subtree law, and independence from the generation domain. The proof uses no look-ahead choice.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/JointSubtrees.lean` uses a prefix-address injection and mathlib's curry theorem for infinite product measures to prove the joint product law for any finite vector of distinct same-generation roots. It also proves the vector of subtrees reads only future marks and gives its past/future event factorization.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Abstract/StoppingSubtreeVector/` partitions by the countable finite vector of selected addresses. It proves measurability, the event factorization, the joint i.i.d. product law, and independence from the generation domain for a measurable vector of $k$ distinct generation-$n$ roots. It does not yet identify such a vector with the actual selected or killed BRW population.
- `Probability/BranchingRandomWalk/Genealogy/Exploration/Selected/StoppingPopulation.lean and Genealogy/Exploration/Selected/StoppingCellBranching/` accepts an arbitrary stopped-domain-measurable finite set of labelled roots, including roots under different initial ancestors. On every prescribed set cell it proves the exact product descendant law by a further countable partition over the finite stopping generation. The theorem includes the empty population and applies directly with $m=\lfloor N^\alpha\rfloor$; it does not assume a child exists.
- `Combinatorics/BranchingWalk/Step/` and `Combinatorics/BranchingWalk/Basic/Displace.lean` expose the abstract position interface induced by a step field: `Step/Basic.lean` gives the presence predicate `survive`, the support, and the zero-defaulted slot value `value'`, `Basic/Displace.lean` the address-carrying mark `displace` (the displacement from a starting address) and its partial version `displace?`; their root instances are written `displace β [] u` and `displace? β [] u`, and no definition is kept that only fixes the starting address. The path realization predicate `surviveAlong` lives in `Combinatorics/BranchingWalk/Basic/SurviveAlong.lean`, whose descendants and ancestors, with the parent and the surviving siblings, are in `Combinatorics/BranchingWalk/Basic/Descendant.lean`; the realized-child predicate of one slot is in `Combinatorics/BranchingWalk/Displace/Node.lean`. The abstract position function is total on all addresses, while concrete particle-system theorems must explicitly require realization. There is exactly one position and one realization predicate, defined on an arbitrary label type; a `ℕ`-specialized copy is not kept, and root-indexed displacement is read off the single-root one rather than defined again.
- `Probability/BranchingRandomWalk/Step/Position/Measurability.lean` is the only generation-filtration position file: realized nodes, fixed-address displacements, current-generation displacements, and measurably selected current-generation addresses. It is generic in the mark type, so no real-valued duplicate is needed.
- `Probability/BranchingRandomWalk/Assumptions/`, `Probability/BranchingRandomWalk/Spine/`, and `Probability/BranchingRandomWalk/Analytic.lean` are reachable from `Probability.BranchingRandomWalk` and therefore part of `lake build`. `Assumptions/Moments.lean` carries the first-, fourth-, and exponential-moment conditions plus the cross-term weight `∑_{i ≠ j} exp(-(Ξᵢ+Ξⱼ))`; it builds, and `fourthMoment_implies_firstMoment` proves the fourth moment condition implies the first.
- `Probability/BranchingRandomWalk/Spine/FiniteKernel.lean` contains the finite child algebra
  for **both** many-to-one variants. It is not the expectation identity for
  random child and is not marked as the full theorem.
- `Probability/BranchingRandomWalk/Analytic.lean` contains the final deterministic speed squeeze
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

## Dependency version audit (2026-09-25)

The previous project configuration used a local path dependency at commit
`de43fbb3c6cbf629cdb6805e24c258f76538689b` (2025-12-01), with Lean
`v4.26.0-rc2`. The project now pins the official upstream mathlib commit
`b3b63681020779dc7e14866c0b2afbd84e0722e4`, which was upstream HEAD
when checked again on 2026-09-25, together with its Lean `v4.35.0-rc2` toolchain.
The local user-fork checkout was not modified. Elan itself was updated to
`4.2.4`. `lake update mathlib` downloaded its cache and `lake build ThesisSpeed`
passes against this pinned revision. A moving upstream branch cannot be
guaranteed to remain current forever; the pinned revision makes the proof
check reproducible.

## Additional deductions that must not be hidden

1. A random countable branching-step point process must admit the weighted sum and
   its expectation in the extended nonnegative reals. Normalization and any
   conversion to finite real expectations need their own integrability lemmas.
2. The one-step tilted law needs a constructed probability measure. Across
   generations, the tilted increments must be proved independent and identically
   distributed before the random-walk identity is used.
3. The many-to-one induction needs measurability of path tests and a Tonelli
   or conditional-expectation interchange for the child sums.
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
   tube regularity and endpoint conditions used later. The tilted entrance
   lower bound additionally needs a local or ballot lower estimate.
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
