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
the random-walk interface consumed by killed branching-population estimates.
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
  `Probability/BranchingRandomWalk/Restart/RootedTrial/FiniteSlot/Offspring.lean`.
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
