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
`MeasureTheory/Measure/Tails/Quadratic.lean` owns vanishing quadratic upper
tails and their finite-second-moment perturbation invariance. The maximal
finite-horizon consequence belongs to `Probability/Sequence/Maximal/`;
it needs only common marginal laws, not independence or a branching model.
`BranchingRandomWalk/Spine/Tilted/FamilyChild.lean` retains the raw family
and distinguished child. `Tilted/Law.lean` derives the original scalar
increment measure and its compensation formula from that joint measure;
`Tilted/Marked.lean` reads a possibly correlated reproductive mark from it.
`BranchingProcess/Spine/LocalBias/ManyToOne.lean` retains arbitrary
observed-generation tree payoffs; `LocalBias/Path.lean` derives the
ancestral-state-path specialization from that interface.
`Assumptions/SpinalWeightTail.lean` owns Mallein's reproductive tail condition
and its equivalence with the total-weight tail. `Tilted/FamilyCutoff.lean`
restricts complete families, whereas the existing `Tilted/Truncation.lean`
truncates ordered child slots. These are different operations.
See `docs/architecture/SPINAL_WEIGHT_TAIL_AUDIT.md` for the completed full-path,
marked-corridor, endpoint and speed chains and the scope of auxiliary examples.
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

## Current interface boundaries

| Interface | Owner and role |
| --- | --- |
| Doob transforms | `Probability/Kernel/DoobTransform/` owns kernel normalization, iteration, restriction to positive states and finite-path density laws. Branching spines call these interfaces. |
| Restart schedules | `Probability/Process/Path/Restart/` owns model-independent schedules and observable path bounds; branching growth trials remain with their target model. |
| Tree lines | `Combinatorics/UlamHarris/Line/` owns deterministic cuts; `Probability/Process/Tree/Line/` owns information and optionality. State-dependent branching supplies descendant-law specializations. |
| Small-deviation entry | `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Theorems.lean` identifies the original numbered results; semantic owner modules contain their proofs and explicit hypotheses. |
| Endpoint and speed estimates | `Probability/BranchingRandomWalk/Selection/NSelection/EndpointDeviation/` and `Frontier/AsymptoticSpeed/` own the selected BRW results, not generic restart theory. |
| Required regressions | `BranchingProcessTest/` tests production interfaces. The central registry owns expected axiom declarations. |
| Reference arguments | `LiteratureProofTest/<CitationKey>/` preserves displaced reference-specific routes and support; production and required regressions cannot import it. Its CI is advisory. |

## Where decisions and rules live

- [Module ownership](docs/architecture/MODULE_OWNERSHIP.md) provides the detailed
  subject inventory; [the theorem index](FORMALIZATION_CHECKLIST.md) records proof status.
- [Module conventions](docs/development/MODULE_CONVENTIONS.md) and
  [abstraction review](docs/development/ABSTRACTION_REVIEW.md) define the normative rules.
- [Verification](docs/development/VERIFICATION.md) defines check selection and evidence.
- [Historical architecture snapshot](docs/architecture/audits/2026-11-27-ARCHITECTURE.md)
  preserves earlier upstream comparisons, chronology and proof-route decisions.
  Existing subject audit documents retain their evidence; they are not alternative
  sources of current ownership or test inventories.

Update current responsibilities when ownership changes. Record historical reasons
in an audit rather than appending another dated narrative to this file.
