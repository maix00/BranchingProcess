# Lean verification of the speed theorem

Run `lake build` in this directory. The project pins Lean and Mathlib through
`lean-toolchain` and `lake-manifest.json`.

There is no project namespace. Declarations live in the namespace of the area
they extend (`Combinatorics.UlamHarris`, `Combinatorics.BranchingWalk`,
`ProbabilityTheory.BranchingRandomWalk`), and the directories mirror mathlib
(`Combinatorics/`, `MeasureTheory/`, `Probability/`). `lakefile.toml` builds the
library through module globs of the three directories, so `BranchingProcess` is only
the build target name and every module is in `lake build`. `ARCHITECTURE.md`
records the full layout.

`Probability/BranchingRandomWalk/Analytic.lean` reexports three focused modules relevant to the new
Theorem 1.3:

1. `Analytic/ExceptionalEvent.lean` proves the pointwise truncation inequality
   and the exact integral factorization available when a fresh reserve
   observable is independent of the exceptional event.
2. `Analytic/ReserveLineage.lean` derives that factorization for measurable
   observables of a fresh exploration-selected subtree and of a selected
   subtree vector in the labelled multi-root model.
3. The exact final limit of the speed from eventual upper and lower bounds at
   every positive error, with coefficient `Real.pi ^ 2 * σ2 / 2`, is in
   `Analytic/SpeedLimit.lean`.

`Probability/BranchingRandomWalk/Timing/Stopping.lean` verifies that the first threshold
crossing of an adapted observable, or the first measurable success declaration,
is a stopping time, using mathlib's hitting-time theorem.
It also proves the generic recursion step: beginning observations after an
already established stopping time preserves the stopping-time property.
`Probability/BranchingRandomWalk/Timing/TimingCounterexample.lean` verifies a finite
counterexample: a time defined from the next generation need not be a stopping
time for the present-generation filtration. It also proves that a retrospectively selected generation-one state can fail adaptedness.
`Probability/BranchingRandomWalk/Timing/Measurability.lean` proves observable declarations for countably many pre-defined candidates and adaptedness of a measurable causal coupling recursion. The thesis-specific constructions still need to satisfy these interfaces.
`Probability/BranchingRandomWalk/Population/Processes/Parallel/Basic.lean`
proves that finitely many concurrently evolved adapted candidate populations
remain adapted after an adapted activation rule takes their union, and bounds
the union size by the sum of the candidate sizes. This is the generic causal
replacement interface for a retrospective restart.
`Combinatorics/UlamHarris/` holds the deterministic address combinatorics:
`TreeNode`, the `𝕍` node set, and the mark function `Mark` in `Basic.lean`;
the `Tree` structure and its measurable space in `Tree/Basic.lean`; the
`MarkedTree` object, its partial mark views, and its measurable space in
`MarkedTree/Basic.lean`; and the declared-split predicate in `Split.lean`. The
generation filtration on the mark field is probabilistic and lives in
`Probability/BranchingRandomWalk/Tree/Filtration.lean`.
`Combinatorics/BranchingWalk/` holds the deterministic branching-step layer: the
slot encoding `Step ι X = ι → Option X` (`Step/Basic.lean`), the
raw and zero-defaulted slot readings (`Step/Basic.lean`), the relation and
ordered-step layers (`Step/Relation.lean`, `Step/Monotone.lean`,
`Step/Rank.lean`, `Step/Orderable.lean`), the step field and the root-indexed
`BranchingWalk` (`Basic/Core.lean`, `Basic/Definitions.lean`),
the measurable slot conditions (`Step/Measurability.lean`), the displacements
(`Basic/Displace.lean`), the survival-along-a-prefix predicates and the
realized marked tree (`Basic/SurviveAlong.lean`, `MarkedTree/OfBranchingWalk.lean`,
`MarkedTree/Equivalence.lean`),
the realized-child predicate (`Displace/Node.lean`), the time-indexed clouds and
trajectories (`Cloud/`, `Trajectory/`), and the domination order on clouds
(`Cloud/Order/Slice.lean`, `Cloud/Order/Basic.lean`). The path recursion is `displace`; the generalized walk interface separates edge
marks from accumulated positions. `RootIndexed.BranchingWalk Root α Mark Position`
stores a `Mark`-valued step field and a `Position`-valued initial state. A map
`d : Mark → Position` is supplied when positions are computed, via
`displaceWith d`. Thus `Mark` need not have an additive structure; only
`Position` is accumulated. The specialization `Mark = Position` and `d = id`
recovers the original displacement recursion. The paper's sum over prefixes is kept as an equivalent
characterization in both indexings and for both marks:
`displace_eq_sum` and
`displace_eq_sum_fin` for the total mark, and
`displace?_eq_some_sum_iff` and
`displace?_eq_some_sum_fin_iff` for the partial mark.
The laws of the step field and the point measure it induces are probabilistic
and live in `Probability/BranchingRandomWalk/Step/`. `Step` still describes
optional child slots and their random edge data; `BranchingWalk` separately
interprets that data as positions through `d`. A potential used for ordering or
log-Laplace weights is an additional measurable real-valued observable, not
the mark type itself. `Probability/BranchingRandomWalk/Genealogy/RootIndexed/`
defines the root-indexed versions (fields, laws, positions, the multi-root step
filtration, and its measurability results); `Probability/BranchingRandomWalk/Genealogy/Lineage/`
holds the pre-sampled reserve lineages. The root-indexed law uses mathlib's
arbitrary-family probability product and does not require `Root` to be finite
or countable. `Root = ℕ` is the canonical one-time infinite pre-sampling used
for the limit in the number of initial particles; every injective
`Fin m → Root` gives its finite marginal. The labelled finite-ancestor law,
filtration, and positions are the `Fin m` instance
(`finiteRootStepFieldLaw`, `multiRootStepFiltration (X := ℝ)`, and
`rootIndexedNodePosition`), so no separate `MultiRoot` copy exists.
Countability is required only when intersecting almost-sure events
simultaneously over every root.
`Genealogy/RootIndexed/FiniteExpectations.lean` shows that a root-dependent
finite sum of measurable observables on this joint space is exactly the sum
of the corresponding single-root expectations. Thus root indexing carries
many copies of a single-root identity without changing that identity.
`Probability/BranchingRandomWalk/Genealogy/Exploration/` collects the abstract, root-indexed, and
selected-population branching-property arguments. Probabilistic growth tails, the selected
population, and the full coupling remain to be modeled.
Deterministic containment and bounded-selection interfaces are polymorphic in
independent `Mark` and `Position` types. Scalar frontiers are obtained by
mapping a position cloud through `potential : Position → ℝ`; the thesis model
is the specialization `Position = ℝ` and `potential = id`.
`Probability/BranchingRandomWalk/Timing/GeometricTrial.lean` verifies the geometric-series
part of the corrected joint transform for reboot waiting displacements.
`Probability/BranchingRandomWalk/Spine/FiniteKernel.lean` verifies the finite one-generation
normalization and both weighted and unweighted size-bias cancellation formulas.
The integrated one-step expectation is formalized in `Spine/TiltedLaw.lean`: it constructs the tilted potential measure, proves probability normalization, and proves both nonnegative one-generation directions. `Spine/EndpointManyToOne.lean` iterates both endpoint identities through every generation. `Spine/IncrementProcess.lean` constructs the independent product process, proves the coordinate laws and independence, and supplies measurable partial-sum positions. `Walk/Basic.lean` defines a single-root `RandomWalk` from a fixed initial position and an increment-process law and realizes it canonically as the `PUnit` child-slot special case of `BranchingRandomWalk`. `Spine/RandomWalk.lean` packages the tilted product process as that object and states both endpoint identities using its position. These interfaces accept separate measurable maps `Mark → Position → ℝ`; the real line remains the scalar potential and spine-increment space. Identifying the recursive branching functional with the actual generation of the pre-sampled tree and extending endpoint tests to path tests remain.
The thesis-specific reboot time has not yet been identified with this generic
hitting time. See [FORMALIZATION_CHECKLIST.md](FORMALIZATION_CHECKLIST.md).

This is **not a formal proof of Theorem 1.3**. The following are still missing:

- the remaining theorem-specific coupling and almost-sure speed arguments;
- the tree/product-process realization of the many-to-one formula and the
  Mogul'skii small-deviation estimates;
- the couplings that yield the two eventual bounds under a first moment;
- an argument replacing the cross-pair second moment, if the cross-term
  assumption is also to be weakened.

Theorem 1.1 retains its stated fourth-moment assumption and its `L²` claim.
Theorem 1.3 currently retains the cross-term assumption. No assumption is
silently promoted to a verified Lean result.
