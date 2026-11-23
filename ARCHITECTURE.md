# Lean library architecture

`BranchingProcess` formalizes deterministic tree and path objects, measure and
probability interfaces, and theorem-specific branching and random-walk
arguments. Module placement follows the mathematics of a declaration, rather
than the application that first needs it.

## Domain owners

| Domain | Owns | Examples |
| --- | --- | --- |
| `Combinatorics` | Deterministic trees, optional child steps, genealogies, and finite selections | `UlamHarris`, `BranchingWalk`, `TreeNode`, generic capacity-$N$ selectors |
| `Algebra`, `Order`, `Analysis` | Deterministic paths, finite sums, grids, inequalities, scales, and asymptotics | `AdditivePath`, `UniformGrid`, `BlockScale` |
| `MeasureTheory` | Operations and properties of measures, measurable spaces, and integrals that do not require a probability model | convolution powers, Dirac sums, measurable random-selection mechanisms, finite-sum moment bounds, measure limits |
| `Topology` | Path spaces, càdlàg geometry, and Skorokhod criteria | `CadlagPath`, oscillation and compactness criteria |
| `Probability/Process/Path` | Generic discrete and continuous process-path operations that do not require a random-walk law | finite restart schedules, relative-window events, path restriction and first passage |
| `Probability` | Laws, filtrations, independence, random processes, and almost-everywhere statements | IID sequences, random walks, Lévy and stable processes |
| `Probability/BranchingRandomWalk` | Random branching models and their bridges to general process and measure interfaces | offspring fields, spines, selection and coupling |

`Combinatorics/UlamHarris/Relation.lean` owns structural root-preserving
ancestry (same root, prefix address), without a survival hypothesis.
`UlamHarris/Line/Basic.lean` defines lines directly with Mathlib `IsAntichain`,
including their root-fiber and generation characterizations. `Ray.lean` owns
the single infinite-path prefix construction, also used by branching-walk
survival. `Line/Coverage.lean` separates meeting every infinite realized path
from being a line; `Line/Order.lean` owns ancestral precedence and descendant
closure. These definitions impose no finite-branching, local-finiteness, or
probability assumptions. They belong outside `Lemmas/` as reusable tree
objects and results. `BranchingWalk/Population/Line.lean` instantiates them
for actual population generations. Random optional/stopping-line measurability
conditions belong in the probability layer and are not part of `IsLine`.

`Probability/Process/Tree/Line/` owns random-line information conditions,
under `ProbabilityTheory.Tree`, independently of BRW dynamics. `Basic.lean`
uses Mathlib's membership-generated measurable space on sets and reuses
`RootIndexed.IsLine`. `IsOptionalLine` is the stopping criterion: for each
fixed line ℓ, `{L ≼ ℓ}` belongs to its supplied information sigma algebra.
`Ancestral.lean` derives this condition from node-membership measurability
and information containment, rather than defining a parallel stopping-line
class. Its fixed-line criterion only requires that test line to be countable;
the all-lines corollary assumes countable node addresses.

`Information/Coordinates.lean` defines `linePast` by excluding the line and
its descendants, and `ancestralPast` using strict ancestors. Both retain
explicit initial information. A life space is a native measurable value type;
a life coordinate maps the whole sample domain into it, and its information
is `MeasurableSpace.comap` of that map. These are distinct objects.
`Observations.lean` compares inclusive ancestral state observations with
strict-ancestor reproduction information. Measurable projections give an
inclusion; measurable equivalences preserve line information exactly.
`BranchingRandomWalk/Genealogy/RootIndexed/Field/State.lean` proves the actual
state observation is measurable from strict-ancestor Steps, by reusing the
existing `stateAlong` recursion and measurable update `F`. A Step records one
parent's whole indexed offspring branch; a child's mark is one component.
Marks may themselves carry complete life records: their chosen information
content and attachment determine their role, without requiring a separate
life-space type. States are computed from the chosen marks and update. No new state recursion or
life-space wrapper is introduced.

The information distinction follows Biggins and Kyprianou, *Measure change
in multitype branching* (2004), §6, pp. 556–557
(DOI:10.1239/aap/1086957585): their very-simple condition uses ancestral
states, including the current state, while optionality remains the base
condition. Jagers and Nerman, *The asymptotic composition of supercritical,
multi-type branching populations* (1996), §2, p. 41, use measurable carriers
for individual life records. Including a node's birth state does not entail
including its own future reproduction record.

`Line/FirstEntrance.lean` in the combinatorial layer defines first entrance
using native `Minimal` for ancestry; its restriction theorem uses native
`IsLowerSet` for ancestor-closed carriers. `Line/Truncation.lean` defines a
bounded generation cut from this same construction. Actual realized-tree
cuts are restrictions to the realized carrier; a depth bound does not assert
that an address is alive. The probability-layer `FirstEntrance.lean` and
`Truncation.lean` add observability and optionality under explicit ancestral
membership hypotheses. Neither theorem asserts the full simple-line
truncation result of Biggins–Kyprianou (2004), Lemma 14.3.
`PathHitting.lean` identifies finite-path entrance events with native Mathlib
`hittingAfter` events; it introduces no parallel stopping-time object.
`Pasting.lean` owns the ordered optional-line pasting theorem and derives the
deterministic-line case from it. These are reusable constructions, outside
`Lemmas/`; no branching law is needed for these information-theoretic results.
`BranchingRandomWalk/Spine/StoppingLine/FirstEntrance.lean` owns the weighted
first-entry identity for the existing boundary-normalized i.i.d. BRW law.
It sums the existing weighted path many-to-one formula over disjoint entrance
generations and identifies its mass with the deterministic first-entrance
line. This is a model-specific theorem outside the generic tree-information
layer; it does not introduce another branching law or replace the canonical
state-tree branching theorem.
`Line/Information/Localization.lean` owns the optional-line trace rules
`A in F_L => A intersect {ell subset L} in F_ell` and stopped measurability
of the random line. `Line/ConditionalExpectation.lean` transfers deterministic
conditional identities to observed selections of cuts, without requiring the
random line to have countable range or bounded depth.
`Line/Information/Boundary.lean` proves boundary-state observability.
`BranchingProcess/State/Observation/` instantiates these information interfaces
for actual generation states and identifies generation-cut information with
native `piLE`. `State/Descendants/SingleNode.lean` and `Products.lean` prove
ordinary branching at arbitrary deterministic cuts from the canonical tree law.
`State/StrongBranching.lean` is the general optional-line entry: it proves
localized finite-product formulas for lines of arbitrary random cardinality,
then identifies the full descendant-family product kernel with native
`HasCondDistrib` and derives conditional expectations for integrable tests.
`State/Descendants/Observed.lean` derives the original generation and
stopping-generation conclusions from this interface. See
`docs/architecture/OPTIONAL_LINE_BRANCHING_AUDIT.md` for scope and references.
The state-kernel spine construction belongs to
`Probability/BranchingProcess/Spine/`. `Family/Joint.lean` owns the single
joint family/selected-child bias; `Family/Marginals.lean` derives both
marginals and `Family/Conditional.lean` derives conditional child selection.
`Offspring/Mean.lean` owns the mean child kernel, and the independent native
kernel density operation lives in `Probability/Kernel/DoobTransform/Basic.lean`.
`DoobTransform/Composition.lean` owns weight cancellation and native kernel
iteration; `Trajectory.lean` owns the finite-history endpoint density, and
`Restriction.lean` owns the normalized kernel on `{0 < h < ∞}`. The generic
homogeneous history adapter and endpoint marginal belong to
`Kernel/IonescuTulcea/Markov.lean`. Finite-history integration uses Mathlib's
`partialTraj_succ_of_le`, integral composition and product-map formulas
directly. `Process/Markov/Trajectory.lean` owns the homogeneous Markov
realization. Doob and spine clients apply that realization directly after
proving their kernels Markov, with no separate specialization modules or
forwarding declarations. `Spine/StateChain.lean` derives the associated spine
transition and its finite-history density from the general Doob interfaces.
It identifies its transition with the selected-child marginal.
`Spine/Observation.lean` reads a unique distinguished coordinate of any
countable tagged population. Its model-specific readout uses Mathlib's
`measurable_to_countable'` for the selector and
`measurable_from_prod_countable_left` for evaluation. The selector returns the
unique distinguished index, or `none` on exceptional populations.
`Spine/Tree/Observation.lean` reads the actual spine's state sequence from the
existing tree, and `Tree/PathLaw.lean` identifies its complete path law with
the same canonical Doob Markov chain. The proof uses
`State.treeKernel_generations` to recover the original generation process,
and `Kernel.map_eq_trajMeasure` for the observed path law.
The generation-assembly steps specific to this identification belong to
`Tree/Lemmas/Generation.lean`, imported with `import all` by the theorem entry;
the reusable observations and kernel identities remain outside `Lemmas/`.
Single-proof auxiliary steps stay local to their proofs.

The Doob/spine dependency audit is recorded in
`docs/architecture/DOOB_SPINE_MATHLIB_AUDIT.md`. It distinguishes the
Doob-specific cancellation and eligible-region support theorems from generic
kernel operations. Density application, constant-one reduction, s-finiteness,
finite-history integration and Markov realization use existing general
interfaces directly. The s-finite power instance remains because the pinned
Mathlib lacks that closure instance, and replacing it with Markov powers
would strengthen the assumptions on the mean offspring kernel.

The observation abstraction audit checked pinned Mathlib
`26573066084e6e2aa8526ea358bc43b66d96f970` against the
[official measurable-constructions API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html).
`Measurable.find` selects the first satisfied predicate in a natural-number
indexing and assumes a witness at each input. `measurable_liftCover` and
`exists_measurable_piecewise` glue compatible local functions over countably
many measurable pieces. Mathlib's `measurable_to_countable'` and
`measurable_from_prod_countable_left` also cover the former repository
countable-range evaluation interfaces: restrict the selector to its actual
range, equip that countable subtype with the discrete measurable space,
prove selector measurability from its fibers, then evaluate the measurable
product field. This preserves arbitrary ambient index types and requires
coordinate measurability only on the actual range. Every client uses these
native operations directly; no local evaluation wrapper or forwarding alias
is retained. The distinguished-state selector remains model-specific data.

`Spine/Tree/Construction.lean` augments states by the ordinary/distinguished
role and applies the existing `State.treeKernel`; it does not implement
another branching process. Normal states can have zero harmonic weight;
only distinguished states require finite positive weight. A barrier on the
spine therefore leaves ordinary side branches unrestricted.
`State/Support.lean` transfers any jointly measurable almost-sure local
reproduction rule to all nodes of the canonical tree, using one-step laws and
product marginals. It has no dependency on the spine modules.
`Spine/Tree/Ray.lean` applies it to the normal/distinguished rules and derives
a unique realized infinite ray; its carrier is exactly all distinguished nodes.
The deterministic unique-continuation arguments belong to `UlamHarris/Ray.lean`.
`Spine/Tree/FirstGeneration.lean` derives the root-family density directly from
the same canonical tree; it defines no alternative tilted tree law.
`State/Map.lean` transports generation, joint-initial path, and full tree laws
through a measurable state factor intertwining offspring kernels. Injectivity
is not required. Its trajectory step uses the single generic observation proof
in `Kernel/IonescuTulcea/Map.lean`; fixed-history and random-initial observations
are derived cases. `Spine/Tree/Normal.lean` applies this to `Sum.inl` and recovers
the original normal-descendant law after erasing roles; the existing branching
property then gives the conditional product law of normal descendant trees.
These are reusable constructions, outside `Lemmas/`. Countable-uniqueness
measurability helpers used only in the ray proof remain private in that file.
The higher-generation tree-density induction, conditional spine law, and full
path decomposition remain obligations in `FORMALIZATION_CHECKLIST.md`.
Fixed-law and exponential BRW specializations must derive from these general results, without a parallel
joint law. Existing tilted increment laws are not counted as tree-density proofs.

`Information/Stopped.lean` also constructs the native `Filtration` associated
with any preorder-indexed pointwise increasing optional lines. Tower,
conditional-expectation martingale, and Lévy upward results reuse Mathlib
rather than introducing parallel conditional expectation or convergence APIs.
Ancestrally observable stopping lines use the existing optionality implication
and the same filtration construction. The regression example of constant
empty lines retains a trivial limiting
sigma algebra; no assertion that arbitrary lines exhaust ambient information
is introduced.

`Information/Stopped.lean` constructs the sigma algebra at an optional
random line from stopped events, following Mathlib
`IsStoppingTime.measurableSpace`. The upstream audit at Mathlib
`26573066084e6e2aa8526ea358bc43b66d96f970` also checked native set-valued
measurability and `MeasurableSpace.comap`; these supply the base interfaces.
All these reusable objects and results stay outside `Lemmas/`. Coin,
mixed-generation, reversible-coding and information-erasure examples belong
only in `BranchingProcessTest/Branching/RandomLine.lean`.


`Combinatorics/BranchingWalk/Basic/State/Recursion.lean` owns the single
state-update recursion `stateAlong F β s v p`, with update
`F : State → Mark → State`. Its optional observation `stateAlong?` uses the
same recursion and the finite-path survival predicate; `stateTree` is the
root-based observation. Finite-path survival is constructively decidable
without any equality assumptions on the mark or child-index types.
`Position/Displace.lean` defines both `displace` and `displace?` by the
specialization $F(s,e)=s+e$, $s=0$. `DisplacementMap.lean` first maps marks
by $d$ and uses those same definitions. There is no separate additive path
recursor. The entry `Basic/State.lean` proves the additive interpretation
`stateAlong_add` and gives the bundled walk's state operation.
`MarkedTree/State.lean` constructs the realized state-marked tree. These are
reusable constructions outside `Lemmas/`.
`MeasureTheory/BranchingWalk/State.lean` owns coordinate measurability for
arbitrary measurable initial states and mark fields.
`MeasureTheory/BranchingWalk/MarkedTree.lean` proves measurability of the
entire realized state-marked tree representation. Generation and ancestral-information
observability bridges belong in
`Probability/BranchingRandomWalk/Genealogy/RootIndexed/Field/State.lean`.
The existing additive `position_measurable` specializes this update result.
This deterministic interpretation does not impose a probability law or
independence; a state-dependent branching kernel is a separate probabilistic
model, not implied by the update map.
`Probability/BranchingProcess/Offspring/Kernel.lean` owns the state-dependent
indexed offspring kernel and its state-update and point-measure images. It
uses Mathlib `Kernel` and `IsMarkovKernel` and the existing generic offspring
point-measure interface, without depending on random-walk probability modules.

`Probability/BranchingProcess/State/Generation.lean` constructs the actual
state-dependent process by applying the offspring-state kernel independently
to the present parents, then using Mathlib's Ionescu--Tulcea law. The root
initial law is an arbitrary joint distribution, not necessarily a product.
`State/Kernel.lean` constructs the single-root path and whole-tree kernels.
`State/BranchingProperty.lean` is the public entry for complete descendant-tree
independence conditional on the observed generation. It accepts any
state-valued Markov offspring kernel $K$; the original mark-valued kernel
and update enter through $K=Q^F$ in `Offspring/Kernel.lean`.
`State/Descendants/Generation.lean` and `Path.lean` identify its one-generation
and complete-path descendant projections. These are reusable transition and
path-law identities, rather than theorem-specific proof support.
`State/Descendants/Observed.lean` handles history-measurable choices of distinct
nodes and the finite-time event of a possibly infinite stopping generation.
Countable address spaces with measurable singletons suffice for random-address
evaluation; the state space needs neither an order, algebraic structure,
standard-Borel structure, nor moment conditions.

`State/FieldLaw.lean` proves `map_stateTree_offspringFieldLaw`: the realized
state tree on the independent mark field has exactly the canonical `treeKernel`
law with $Q(x)=\mu$. Its proof identifies the initial state and each
past/next joint law and invokes the existing Ionescu--Tulcea uniqueness.
The former independent-mark kernel definition and its public parallel family
interface have been removed, without aliases.
`Genealogy/Exploration/Abstract/State.lean` retains only the concrete raw-field
conditional-law adapters, whose conclusions now use that same canonical kernel.
Their namespace is `ProbabilityTheory.BranchingRandomWalk.Exploration.State`,
with names `condExp_selectedTrees`, `condExp_stoppedTrees`, and
`condExp_stoppedTrees_on_finite`. They condition on the full mark-field past,
not only the state path, so their
input data remain with the concrete model. Their single-file integration helper
is private and uses the field-law identification and native product pushforwards.
The additive and potential-displacement measurability proofs likewise invoke
`stateAlong_measurable`; they do not implement separate induction schemes.

### State-dependent branching: upstream reuse audit (2026-11-20)

The dependency audit checked pinned Mathlib
`26573066084e6e2aa8526ea358bc43b66d96f970`, pinned BrownianMotion
`baaa2468da869e15e1654cbe416e55a5dc9d08b5`, and the official Mathlib kernel
source tree at upstream master `5f78f9ce46fc85fa3cb45561d47b489c4c98cd04`.
The relevant existing APIs and the local additions have separate roles:

| Existing dependency API | Use in this library |
| --- | --- |
| `Measure.infinitePi`, `infinitePi_map_pi`, `infinitePi_map_curry`, `map_infinitePi_infinitePi_of_inj` | Construct and reindex independent coordinate measures; no replacement product-measure object. |
| `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure` | Prove parameter measurability of the product probability kernel from finite cylinders. |
| `Kernel.traj`, `trajMeasure`, `partialTraj`, `partialTraj_compProd_traj` | Construct and disintegrate the full process; no new extension theorem. |
| `Kernel.eq_traj`, `eq_traj'`, projective-limit uniqueness | Existing finite-prefix uniqueness. The local `eq_trajMeasure` derives those prefixes from the initial and one-step joint laws by induction. |
| `Measure.compProd_map` | Change the future coordinate of a joint law. `Composition/Map.lean` supplies the first-coordinate identity and its conditional-kernel observation consequence. |
| `condExp_stopping_time_ae_eq_restrict_eq_of_countable` | Assemble deterministic-time conditional laws on the cells $\{\tau=n\}$; no replacement stopping-time definition. |
| `Kernel.exists_measurable_map_eq_unitInterval` | A possible standard-Borel realization of a kernel, unnecessary here: direct products and Ionescu--Tulcea preserve arbitrary measurable state spaces. |

The local `Probability/Kernel/Composition/InfinitePi.lean` packages the native
product measures as a common-input probability kernel and proves coordinatewise
composition. `Kernel/IonescuTulcea/Independent.lean` identifies independent
products of complete history-dependent process laws. The local conditional
integration statements derive the conditional expectation from an explicit
joint law, without constructing a regular conditional distribution. These
are independently meaningful operations on kernels and processes, outside
`Lemmas/`; the one-use address calculation is a private lemma in its caller.

Official references checked:
[Mathlib Ionescu--Tulcea](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/IonescuTulcea/Traj.html),
[infinite product measures](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/ProductMeasure.html),
and [Giry measurability](https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/GiryMonad.html).
The branching transition follows the parent-conditioned reproduction property
in S. Valère Bitseki Penda and J.-F. Delmas, *Central limit theorem for
bifurcating Markov chains*, Definition 2.1 (binary families),
https://cermics.gitlab.enpc.fr/delmas/Publi/clt-bmc-ptw.pdf. Sibling dependence
is retained inside each joint offspring family; distinct parents reproduce
conditionally independently. Mathlib's extension proof cites O. Kallenberg,
*Foundations of Modern Probability*, third edition (2021), Theorem 8.24,
DOI 10.1007/978-3-030-61871-1.

The selected-path construction used for the asymptotic speed of the frontier is owned by
`Probability/BranchingRandomWalk/Selection/NSelection/Frontier/AsymptoticSpeed/SelectedPath/`.
Its root `selectedPath` follows the second selected child at each split while
the first selected child starts a growth trial. Trial populations, completion,
and coupling are grouped beneath `SelectedPath/GrowthTrial/`,
`SelectedPath/Completion/`, and `SelectedPath/Coupling/`; one-use steps for the
construction are under the sibling `AsymptoticSpeed/Lemmas/`.

The deterministic rule assigning a child slot to the continuation path is in
`Combinatorics.Branching.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath`.
The generic first and second slot operations are methods of `Step.FiniteSelection`.
`Asymptotics.HasAsymptoticSpeed` describes a limit of position sequences, and
`Combinatorics.Branching.Selection.NSelection.Walk.Frontier` applies it to the
least and greatest position paths of a deterministic selected walk.

The first observable split of a selected population is a reusable process fact
owned by the `BranchingRandomWalk.Selection.Stepwise.SplitTime` namespace. Its
files are under `Probability/BranchingRandomWalk/Population/Processes/StepSelection/SplitTime/`.
The fixed-root time shift belongs beside it in `RootIndexed.lean`. The
almost-sure finite completion is in `SplitTime/Finite.lean`, with its proof
helpers in `SplitTime/Lemmas/FiniteCompletion.lean`. The
two-sibling stopped subtree factorization used by the selected-path construction is in
`AsymptoticSpeed/Lemmas/FirstSplit/`. Generic selected-subtree integration is
owned by `Genealogy/Exploration/IndependentSubtreeIntegration.lean`, and the
independent eventwise integral bound is at
`Probability/Independence/Integration/IndependentUpperBound.lean`.

`AsymptoticSpeed/Limit/EndpointExpectation.lean` uses the public stopped
endpoint law to transfer the expectation of a terminal payoff on finite
completion to a fresh descendant field and the stopped endpoint data.

Generic process interfaces stay separate by role: observable candidate
completion and success are in the `ProbabilityTheory.Trial` namespace under `Probability/Process/HittingTime/`, while
i.i.d. geometric reward belongs under `Probability/Sequence/IID/GeometricReward/`.
These cover distinct trial protocols, so no umbrella `Probability/Process/Restart/`
module is introduced. `Probability/Process/Path/Restart/` retains its own
path-rebasing and relative-window meaning. The branching-step split event and
its measurability belong to `Combinatorics/BranchingWalk/Step/Selection/Split.lean`
and `MeasureTheory/BranchingWalk/Step/Selection/Split.lean`; the general
positive-probability bounded-split estimate belongs to
`Probability/BranchingRandomWalk/Step/Selection/BoundedSplit.lean`.

`Probability/Process/Path/Representation/Continuous.lean` owns both the
bundling and measurability interfaces for continuous sample paths and the
generic extraction of a measurable continuous-path-valued version from
coordinate measurability and almost-sure path continuity. Model-specific
constructions, such as Brownian versions, specialize this interface in their
process-law modules.

Generic stopping-time declarations indexed by arbitrary candidate families
belong under `Probability/Process/HittingTime/`; in particular,
`OrderedCandidates.lean` records priority-ordered successes at arbitrary
observable completion times. Recursive schedules of pre-sampled trials,
whose next start is the first observable readiness time after the preceding
start, belong under `Probability/Process/Stopping/CausalSchedule/`. The
fixed-duration completion map for arbitrary scheduled starts belongs under
`Probability/Process/Stopping/TrialSchedule/Completion.lean`. The
branching-walk adapter that reads marks from the current generation frontier
remains under `Probability/BranchingRandomWalk/Timing/Schedule/Frontier.lean`.

`Topology/ContinuousMap/LinearPath.lean` owns the deterministic continuous
map $t\mapsto at$ on the unit interval. `Topology/Cadlag/Skorokhod/Path/Linear.lean`
adapts it to the $J_1$ path space and owns the corresponding distance and
uniform-error estimates. Brownian support results reuse those interfaces and
provide their probabilistic properties at their own layer.

`Topology/MetricSpace/Cutoff.lean` defines the reusable bounded distance to
the complement of an open set, $x\mapsto\min(1,\operatorname{dist}(x,s^c))$.
The Skorokhod corridor weights specialize it to path corridors and terminal
intervals.

`Topology/MetricSpace/Oscillation.lean` owns the generic predicate
`Metric.OscillationBounded f C`, which bounds every pairwise distance in the
range of a function. It connects that pointwise form to Mathlib's extended
range diameter `Metric.ediam`; Skorokhod path tubes and finite random-walk
block events specialize this common interface.

`Topology/Cadlag/Skorokhod/Path/TerminalLeft.lean` owns the terminal-left
modification and the endpoint subspace $D_0$ for càdlàg paths with arbitrary
topological state spaces; mapping into that subspace assumes a T₂ state space.
The Borel-measurability result for real-valued paths remains at
`MeasureTheory/MeasurableSpace/CadlagPath/TerminalLeft.lean`.

`Probability/Process/RandomWalk/Path/Skorokhod/TerminalLeft/Basic.lean` owns
the source terminal-left normalized step path. Its `Partition/Basic.lean` and
`Partition/CellBounds.lean` modules give the clipped knot indices, terminal
cell lengths, corridor-to-cell implication, and selected-cell IID range
probability bound for arbitrary finite `StepBoundary` partitions. Stable-domain
rates remain under `SmallDeviation/Mogulskii/Stable/Discrete/TerminalLeft/`,
while the theorem-specific endpoint-core lower proof remains under
`SmallDeviation/Mogulskii/Lemmas/TerminalLeft/Partition/`.

General finite-history drawdown predicates and their measurability belong to
`Probability/Process/RandomWalk/Path/Event/Drawdown.lean`. Random-walk probability
bounds for those paths belong to `Probability/Process/RandomWalk/SmallDeviation/Drawdown/`.
The cutoff-based discrete restart schedule and the finite-path condition
`x(k) - x(restartAnchor cutoff k) ∈ window k` belong to
`Probability/Process/Path/Restart/`; its measurability and endpoint-bound
consequences are stated at that same general path layer. Random-walk history
identities and IID interval or corridor probabilities that specialize this
event remain under `Probability/Process/RandomWalk/Path/Restart/`.
`FirstMoment.lean` there owns the law-generic exponentially weighted
restarted-window integral and its bound by the endpoint factor times the
ordinary restarted-window probability; its horizontal-tube specialization is
the random-walk interface consumed by estimates for selected branching populations.
Generic conditional-probability integration and successive-block product
bounds belong to `Probability/Process/Filtration/ConditionalBlocks.lean`;
the conditional expectation of a measurable event of an independent pair,
as its second-marginal section probability, belongs to
`Probability/Independence/ConditionalIntegral.lean`. IID prefix/next-block
applications use the independent-block theorem in
`Probability/Sequence/IID/Blocks/StoppingTime.lean` directly. The law transfer
between an infinite IID walk and a finite closed-interval block belongs to
`Probability/Process/RandomWalk/Path/Block/Law/FiniteInterval.lean`, while
translation of a finite interval by its initial position belongs beside the
`FiniteInClosedInterval` definition in `Path/Window/Basic.lean`.
Generic finite block coordinates and their measurability belong to
`Probability/Sequence/Block.lean`; their product-law interface for canonical
IID sequences belongs to `Probability/Sequence/IID/Basic.lean`. These
sequence-level facts are independent of stopping times and random-walk
applications. The measurable map extending a finite block along `Fin.val` by
a fixed default is stated there using Mathlib's generic `Function.extend`.
Uniform one-block estimates for a killed interval kernel and their iteration
to a horizontal-tube bound belong to
`Probability/Process/RandomWalk/SmallDeviation/HorizontalTube/Kernel/BlockIteration.lean`;
the equal-partition and finite-variance rate choices for Wang Yiyang's Lemma
3.2 remain theorem-specific under `HorizontalTube/FiniteVarianceUpper/Lemmas/`.
Within `HorizontalTube/`, endpoint-window definitions and real-width estimates
are grouped under `EndpointWindow/`, Donsker lower bounds under `Diffusive/`,
and killed-kernel estimates under `Kernel/`; the single scaling theorem stays
at the subject root.
BRW ancestral-path decompositions, including ordered generation-pair counts
split by most recent common ancestor, live in `Spine/Path/`; affine-tube
probability estimates and their use in the second-moment argument live in
`Spine/Tube/`. Branching-walk first-passage and many-to-one results also live
under `Probability/BranchingRandomWalk/Spine/`. The deterministic real-mark
order-dual map and its support and exponential-weight identities belong to
`Combinatorics/BranchingWalk/Step/Ordering/OrderDual.lean`; identities for the
corresponding tilted spine laws belong to
`Probability/BranchingRandomWalk/Spine/Tilted/OrderDualLaw.lean`.

The endpoint operator of a real IID increment law and its partial-sum integral
recursions belong to `Probability/Process/RandomWalk/Kernel/Endpoint.lean`;
the unweighted operator is identified there with the action of
`incrementKernel`. Branch-generation operators and their many-to-one
identifications remain under `Spine/ManyToOne/EndpointManyToOne.lean`, and
their realization under the pre-sampled offspring field belongs to
`Spine/ManyToOne/ProductField.lean`.

Selection modules are placed by the data they take as input:

- `Combinatorics/Selection/` owns deterministic candidate-set mechanisms. In
  particular, `NSelection` assigns a finite selected subset to each
  candidate set, with `M.select s ⊆ s` and
  `(M.select s).card = min N s.ncard` when `s` is finite (and cardinality
  `N` when `s` is infinite). This describes a capacity-constrained selection
  rule on an arbitrary type `ι`; it contains no offspring relation, generation,
  or evolving population. The interface is used by generic measurable
  selection (`MeasureTheory/Selection/Random.lean`), stopped ranked selection
  (`Probability/Process/Stopping/Selection/Ranked.lean`), and branching walks.
  Mathlib supplies the underlying filtering and ordering operations
  ([`Finset.filter`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Filter.html),
  [`Finset.sort`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Sort.html));
  the capacity-$N$ interface composes those operations for this project.
- `Combinatorics/Matching/ThresholdCount.lean` owns the generic
  threshold-count matching theorem. If every order-key threshold count of
  `objectsToMatch` is bounded by the corresponding count in
  `availablePartners`, it constructs an injection whose partner order key is
  at most the matched object's order key. The theorem is independent of
  `NSelection`; `Combinatorics/Selection/NSelection/Matching/SelectedPopulation.lean`
  applies it to the population selected by the first-`N` rule. Mathlib provides
  the underlying relation-based finite Hall theorem in
  `Mathlib/Combinatorics/Hall/Basic.lean`.
- `Combinatorics/BranchingWalk/Step/Selection/` owns selectors whose input is
  an offspring step. `Combinatorics/BranchingWalk/Selection/NSelection/Walk/`
  owns the generation recursion
  $P_{n+1}=M\!\left(\bigcup_{x\in P_n}\operatorname{children}(x)\right)$,
  which forms offspring candidates and selects at most $N$ particles. This is the
  deterministic N-branching random walk studied in the literature as a
  branching-selection particle system ([Bérard–Maillard,
  arXiv:1311.1488](https://arxiv.org/abs/1311.1488)).
- `Step.FiniteSelection.binaryOffspringStep` is the deterministic encoding of
  a capacity-two selected offspring family as an initial segment of `Fin 2`;
  its definition and child-count identity belong to
  `Combinatorics/BranchingWalk/Step/Selection/FiniteSlot.lean`. Its
  measurability theorem belongs to
  `MeasureTheory/BranchingWalk/Step/Selection/FiniteSlot.lean`, and the
  pushforward offspring law and supercriticality criterion belong to
  `Probability/BranchingRandomWalk/Step/Selection/BinaryOffspringLaw.lean`.
- `MeasureTheory/Selection/` owns measurable selector realizations and their
  measurability results. Measurability results whose input is a branching step
  belong to `MeasureTheory/BranchingWalk/Step/Selection/`. The generation
  recursion is a deterministic branching-walk object; its random laws,
  selected-population couplings, and stochastic estimates belong to
  `Probability/BranchingRandomWalk/Selection/`. Evaluation of a generic
  ranked selector at a discrete stopping time belongs to
  `Probability/Process/Stopping/Selection/Ranked.lean`; overflow of a causal
  finite selected population belongs to
  `Probability/Process/Stopping/Selection/Overflow.lean`, for arbitrary label
  types.

`NSelection` itself is not a measurable-space construction. Its deterministic
interface remains in `Combinatorics/Selection/`; the modules under
`MeasureTheory/Selection/NSelection/` establish measurability properties of
that interface. In particular, `MeasureTheory/Selection/NSelection/FromSet.lean`
defines `MeasurableFirstNBy`, a measurable realization of the first-$N$
specification; it packages measurability data for the generic selector rather
than defining the selector itself. The generation-by-generation offspring
selection remains under `Combinatorics/BranchingWalk/Selection/NSelection/`.
`MeasureTheory/MeasurableSpace/` is reserved for measurable-space structures
on mathematical objects and their generated σ-algebras. No core selector,
capacity mechanism, or branching walk is defined there. The modules under
`MeasureTheory/Selection/NSelection/` contain measurability results for the
combinatorial selector, not definitions of `NSelection`.

Deterministic bounds on generation sizes from offspring-count recurrences
belong with `Combinatorics/BranchingWalk/Population/`; probability assumptions
or laws are required before such a result belongs under
`Probability/BranchingRandomWalk/Population/`.

The generic candidate-set selector remains in combinatorics because its
signature depends only on candidate sets and cardinality. The displayed
generation recursion acquires BranchingWalk semantics by supplying offspring
sets and iterating the selector; it belongs under `BranchingWalk`. Moving the
generic interface there would make reusable measurable and stopped-selection
results depend on the branching-walk model. The deterministic
root-indexed child-address set for one generation is owned by
`Combinatorics/BranchingWalk/Population/Candidates/Generation.lean`; its
finite negative-exponential-weight lower-finiteness criterion is in
`Combinatorics/BranchingWalk/Population/Candidates/ExponentialWeight.lean`.
The field-observable specialization and its domain-flow measurability theorem are under
`Probability/BranchingRandomWalk/Population/Candidates/RootIndexed/`. Selected
population endpoint and drawdown estimates live under
`Selection/NSelection/EndpointDeviation/`, and random speed arguments live
under `Selection/NSelection/AsymptoticSpeed/`. Root-indexed position
observations are owned by `Genealogy/RootIndexed/Measurability`; random finite
selectors adapted to those observations live under `Selection/Finite/`.
The directory `MeasureTheory/MeasurableSpace/` is for constructions and
properties of measurable-space structures themselves. A theorem about a
selector does not belong there merely because it assumes a `MeasurableSpace`
instance; place it by the selector or process whose measurability it proves.

Within Skorokhod geometry, the isometric map from paths valued in a subtype to
ambient-state paths belongs to `Topology/Cadlag/Skorokhod/Maps/Range.lean`.
The compact-range oscillation criterion belongs to
`Topology/Cadlag/Skorokhod/Compactness/CompactRange.lean`; finite moving-knot
step-path parameters and their compact image belong together in
`Compactness/StepPath.lean`.

These are ownership boundaries, not a requirement to introduce a wrapper at
every boundary. A concrete theorem should depend on the narrowest module that
owns each concept it uses.

## Model seams

- A deterministic branching step is `ι → Option X`. `none` represents an
  absent child, so the model includes zero offspring without a special case.
- `Combinatorics.BranchingWalk` describes deterministic marked walks. The
  random `Probability.BranchingRandomWalk` layer supplies laws and filtrations.
  A random walk is connected to process-level random-walk results through the
  explicit branching-walk bridge; it does not redefine the deterministic
  walk as a probability object.
- `Probability/Process/RandomWalk/Rademacher/FiniteInterval/` owns the finite
  interval walk with fair $\pm1$ increments: its killed transition matrix and
  kernel, sine eigenfunction, and path-survival interpretation. Small-deviation
  modules use this concrete model without owning its construction.
- `LinearAlgebra/Matrix/Substochastic.lean` owns the generic condition
  `(∀ i j, 0 ≤ M i j) ∧ ∀ i, ∑ j, M i j ≤ 1`; the finite-state kernel
  adapter imports this property and owns its real-matrix representation.
- `LinearAlgebra/Matrix/FiniteKernel/Eigenfunction.lean` owns row-mass
  identities and bounds for powers of finite nonnegative matrices from bounded
  right eigenfunctions. Probability modules specialize these algebraic
  estimates and own their transition-law interpretation.
- `Probability/Kernel/Step/` owns noise-realized total and partial steps,
  finite-history path events, and their survival and endpoint recursions.
  `Step/FiniteBranches/` groups the finite weighted transition constructor,
  its history weights, and its canonical-IID comparison. Only the branch-index
  type is finite; the source may be countable and the measurable target is
  arbitrary. The matrix-to-kernel representation that requires a finite state
  space belongs to `Probability/Kernel/FiniteState/Matrix.lean`.
- Brownian range small-width probability bounds belong to
  `Probability/Process/Brownian/SmallDeviation/Range/`; finite-time range and
  corridor survival for the fair Rademacher walk belong to its finite-interval
  model owner. `Probability/Process/RandomWalk/SmallDeviation/Range/` owns
  IID range-to-block comparison, the one-block Donsker bound, finite-corridor
  covers, and the finite-variance block-oscillation rate. Mogulskii-scale
  specializations remain under `SmallDeviation/Mogulskii/Rate/`. Generic
  finite-horizon kernel bridges between source and target subtypes belong to
  `Probability/Kernel/Bridge.lean`; survival mass, returns to measurable
  cores, and their block estimates belong to `Probability/Kernel/Survival/`.
- Ulam--Harris trees describe surviving addresses. A branching walk determines
  its parent-closed genealogy. Sibling closure is additional ordering data and
  is required only when the chosen address order needs it.
- General path and Skorokhod criteria belong below stable-process and
  small-deviation applications. Stable modules specify stable increments and
  use those generic criteria; random-walk Mogulskii modules specialize the
  block and spectral arguments.
- Rational and dyadic grids are deterministic coordinate infrastructure.
  `UniformGrid` accepts arbitrary endpoints; rational and dyadic constructions
  are specializations, not unit-interval-only definitions.

## Reuse and abstraction rule

Before introducing a public object, search Mathlib and the existing library.
Use Mathlib's measure, kernel, filtration, product-law, and path-space objects
directly when they express the needed semantics. Add a local definition only
when it contributes a mathematical interface absent from those objects. Put
that interface in the lowest layer whose assumptions suffice. A named
specialization is appropriate when it records a real model choice or provides
a useful theorem interface; a second copy of a general Mathlib concept is not.

Use across several modules is a prompt to review ownership, not by itself a
reason to promote a declaration to a broader public layer. First search for a
more abstract Mathlib or library interface, then compare its assumptions and
semantics with the actual use sites. For example, finite first-hit selection
uses Mathlib's `MeasureTheory.hittingBtwn` directly. The separate
`Probability.Process.TimeGrid.Ceiling` interface abstracts only the additional
time-threshold operation and its convergence and measurability results over
an arbitrary domain; continuous-path first passage remains a specialization
under `Path/FirstPassage/`. When the local source does not settle whether a
candidate interface is already available, consult the official Mathlib
documentation/source and relevant references, then verify the candidate
against the pinned dependency revision. Record the candidate and the semantic
or hypothesis gap that motivates a local interface; do not promote a theorem
solely to reduce duplicate code or because it has multiple callers.

A public API rename updates every client to the new canonical declaration.
Remove the old declaration instead of retaining a forwarding or deprecated
compatibility alias.

## Proof-module placement

Name Lean files with a concise `UpperCamelCase` topic; let the parent
directory carry the broader subject instead of repeating it in every file
name. Repeated stems such as `Basic`, `Upper`, or `Rate` are acceptable under
different semantic subdirectories when each path gives a clear owner. A
`.lean` file and a sibling directory with the same name are ambiguous and
must be resolved. Keep at most one `Lemmas/` child at each directory level;
when a directory has more than eight direct Lean modules, review whether its
subjects need semantic subdirectories. Mathlib's naming guide specifies the
`UpperCamelCase` file convention; the additional collision and grouping rules
are repository-specific ([Mathlib naming conventions](https://github.com/leanprover-community/leanprover-community.github.io/blob/lean4/templates/contribute/naming.md)).

Use a `Lemmas/` subtree for a substantial one-use derivation or a connected
chain of intermediate results that supports a theorem entry. A short helper
used only by the theorem in the same module should stay there as `private`;
do not create a one-lemma module merely to hide a small proof step. A single
file under `Lemmas/` is appropriate when it contains a substantial, coherent
proof stage; the directory does not need multiple files to be justified. Give
an intermediate result its own file when its proof is substantial, its topic
is coherent enough to navigate independently, or it creates a useful import
boundary. Keep complete reusable theorems, definitions, and construction
interfaces at their semantic owner even when a single theorem currently uses
them.

Declarations under `Lemmas/` are proof support, not public API. In the new
Lean module system, place them in a private section (for example, `section`
without `@[expose] public section`), use ordinary `import` for semantic
dependencies, and use `import all` when another module in the same package
needs an intermediate declaration. Do not use `public import` to re-export a
`Lemmas/` module. If a legacy module cannot share private declarations with
its clients, migrate the relevant dependency chain to the module system
before exposing those helpers as public API. Complete reusable results and
definitions belong at their semantic owner, even if only one current proof
uses them. This follows Lean's package-local private-module mechanism described
in the [Lean reference on source files and modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).

Mathlib also uses `Lemmas` files for coherent collections split from a base
module to reduce dependencies, for example
[`Mathlib.Data.List.Lemmas`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Lemmas.html).
That is a Mathlib example, not a blanket rule that every local proof chain
needs its own file. The private proof-only `Lemmas/` subtree above is this
repository's stricter organization rule.

For probabilistic abstraction, Mathlib provides `iIndepSets` and its finite
product characterization, together with conditional-independence interfaces
such as `iCondIndepSets` ([independence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html),
[conditional independence](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Conditional.html)).
These interfaces express general independence and conditional factorization;
they do not encode this repository's consecutive increment blocks, their
prefix filtrations, or the translation from a horizontal-tube block to its
zero-start event. Keep those reusable sequence and filtration adapters at
`Probability/Sequence/IID/Blocks/` and
`Probability/Process/Filtration/ConditionalBlocks.lean`. A horizontal-tube
module should specialize those interfaces to its event family; a specialization
used only inside one proof belongs under that module's `Lemmas/` subtree.

For the detailed ownership map and examples of reused Mathlib objects, see
[`docs/architecture/MODULE_OWNERSHIP.md`](docs/architecture/MODULE_OWNERSHIP.md).
For the completed structural moves and their remaining proof obligations, see
[`docs/architecture/MIGRATION_PLAN.md`](docs/architecture/MIGRATION_PLAN.md).
For theorem-by-theorem formalization status, see
[`FORMALIZATION_CHECKLIST.md`](FORMALIZATION_CHECKLIST.md).
For the audit of dense module directories and their entry points, see
[`docs/architecture/MODULE_DIRECTORY_AUDIT.md`](docs/architecture/MODULE_DIRECTORY_AUDIT.md).
For the per-module status of the repository-wide structural and semantic audit,
see [`docs/architecture/MODULE_AUDIT_LEDGER.csv`](docs/architecture/MODULE_AUDIT_LEDGER.csv).
For the mathematical distinction between Mogulskii corridors, drawdown,
tilted tubes, and entrance estimates, see
[`Probability/Process/RandomWalk/SmallDeviation/README.md`](Probability/Process/RandomWalk/SmallDeviation/README.md).

There is no repository-wide umbrella import. A named subject entry point may
re-export a coherent list of principal published results for discovery, as
`Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Theorems.lean` does
for the original Mogul'skii theorems. Such an entry point does not replace the
semantic owner modules: proofs and ordinary clients import the narrow module
that defines the required object or proves the required result. The dependency
graph and API are checked by the repository scripts described in
[`CONTRIBUTING.md`](CONTRIBUTING.md).

Do not gather unrelated definitions under a blanket `Definitions/` directory.
Put each definition with the mathematical topic that owns its meaning and
dependencies; keep a subject-level `Theorems.lean` only as a curated discovery
entry. This follows Mathlib's topic-based organization: for example, kernel
composition APIs are split by composition, products, and related operations
under [`Mathlib/Probability/Kernel/Composition`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html),
instead of being grouped in one general definitions module.

## Fixed-address spinal densities and tree observations (2026-11-23)

`BranchingProcess/Spine/Tree/Density/Weight.lean` owns the ancestral
fixed-address densities and their endpoint/root telescoping formula.
`FiniteGeneration.lean` owns the arbitrary-depth fixed-address identity,
finite-generation tree Radon–Nikodym law, and complete-tree identification.
`Conditional.lean` uses native Radon–Nikodym and conditional-expectation APIs
for the spine location given the complete untyped finite tree. The actual
address and ray observations belong in `Tree/Observation.lean`, outside
`Lemmas/`; they reuse `distinguishedState` rather than a second selector.
The source-specific generation assembly and induction stay private to
`Density/Lemmas/`. Their shared tagged-generation support is
`Tree/Lemmas/Generation.lean`, used by both the path-law and density proofs.
There is one canonical tree and one generic observed-state reader throughout.
The tree subject retains seven direct Lean modules; density is a coherent
subdirectory with three public modules and one `Lemmas/` directory.

`Process/Tree/Line/Information/Pasting.lean` owns the exact stopped-information
identity for the existing ordered optional pasting. It requires no branching
model and introduces no second optional-line or information definition.
See [the source and upstream audit](docs/architecture/SPINAL_DENSITY_AUDIT.md).
