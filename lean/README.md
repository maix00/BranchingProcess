# Lean verification of the speed theorem

Run `lake build ThesisSpeed` in this directory. The project pins Lean
`v4.35.0-rc2` and Mathlib through `lake-manifest.json`; run `lake update` to
move to the newest compatible revisions.

There is no project namespace. Declarations live in the namespace of the area
they extend (`UlamHarris`, `BranchingStep`, `MeasureTheory`,
`ProbabilityTheory.BranchingRandomWalk`), and the directories mirror mathlib's
(`Combinatorics/`, `MeasureTheory/`, `Probability/`). `lakefile.toml` lists the
aggregate modules as the library roots, so `ThesisSpeed` is only the build
target name. `ARCHITECTURE.md` records the full layout.

`Probability/BranchingRandomWalk/Analytic.lean` currently verifies two analytic facts relevant to the new
Theorem 1.3:

1. A pointwise truncation inequality for controlling an exceptional event with
   a first moment in place of a fourth-moment/Cauchy--Schwarz estimate.
2. The exact final limit of the speed from eventual upper and lower bounds at
   every positive error, with coefficient `Real.pi ^ 2 * σ2 / 2`.

`Probability/BranchingRandomWalk/Timing/Stopping.lean` verifies that the first threshold
crossing of an adapted observable, or the first measurable success declaration,
is a stopping time, using mathlib's hitting-time theorem.
It also proves the generic recursion step: beginning observations after an
already established stopping time preserves the stopping-time property.
`Probability/BranchingRandomWalk/Timing/TimingCounterexample.lean` verifies a finite
counterexample: a time defined from the next generation need not be a stopping
time for the present-generation filtration. It also proves that a retrospectively selected generation-one state can fail adaptedness.
`Probability/BranchingRandomWalk/Timing/Measurability.lean` proves observable declarations for countably many pre-defined candidates and adaptedness of a measurable causal coupling recursion. The thesis-specific constructions still need to satisfy these interfaces.
`Combinatorics/UlamHarris/` holds the deterministic address combinatorics:
`TreeNode`, the `𝕍` vertex set, the `GenealogicalTree` structure, the
`MarkedTree` object and its partial mark views in `Basic.lean`, and the
declared-split predicate in `Split.lean`. The generation filtration on the
mark field is probabilistic and lives in `Probability/BranchingRandomWalk/Tree/Filtration.lean`.
`Combinatorics/BranchingStep/` holds the deterministic branching-step layer: the
slot encoding `Step ι X = ι → Option X` (`Basic.lean`), the
presence-prefix and order conditions (`Prefix.lean`), the increment and support
calculus (`Position/Increment.lean`), the primitive
step field `StepField` (`Field.lean`), the accumulated marks
(`Position/Accumulate.lean`, `Position/Partial.lean`), the realization
predicates and realized tree (`Tree/Realization.lean`, `Tree/Realized.lean`),
and the child-slot vocabulary
(`Slot/Basic.lean`, `Slot/Order.lean`, `Slot/Position.lean`). The path
recursion is the fold `accumulate`, which carries the
current address; the partial mark is the same recursion in `Option`
(`accumulate?`), a computable definition with no
`classical` dependency. The paper's sum over prefixes is kept as an equivalent
characterization in both indexings and for both marks:
`accumulateRoot_eq_sum` and
`accumulateRoot_eq_sum_fin` for the total mark, and
`accumulateRoot?_eq_some_sum_iff` and
`accumulateRoot?_eq_some_sum_fin_iff` for the partial mark.
The laws of the step field and the point measure it induces are probabilistic
and live in `Probability/BranchingRandomWalk/Step/`. `Probability/BranchingRandomWalk/Genealogy/RootIndexed/`
defines the root-indexed versions (fields, laws, positions, the multi-root step
filtration, and its measurability results); `Probability/BranchingRandomWalk/Genealogy/Lineage/`
holds the pre-sampled reserve lineages. The labelled multi-ancestor law,
filtration, and positions are the `Fin m` instance of the root-indexed layer
(`finiteRootStepFieldLaw`, `multiRootStepFiltration (X := ℝ)`, and
`rootIndexedStepPosition`), so no separate `MultiRoot` copy exists.
`Probability/BranchingRandomWalk/Genealogy/Exploration/` collects the abstract, root-indexed, and
selected-population branching-property arguments. Probabilistic growth tails, the selected
population, and the full coupling remain to be modeled.
`Probability/BranchingRandomWalk/Timing/GeometricTrial.lean` verifies the geometric-series
part of the corrected joint transform for reboot waiting displacements.
`Probability/BranchingRandomWalk/Spine/FiniteKernel.lean` verifies the finite one-generation
normalization and both weighted and unweighted size-bias cancellation formulas.
It does not yet include the expectation and independence steps of the full
many-to-one formula.
The thesis-specific reboot time has not yet been identified with this generic
hitting time. See [FORMALIZATION_CHECKLIST.md](FORMALIZATION_CHECKLIST.md).

This is **not a formal proof of Theorem 1.3**. The following are still missing:

- a Lean definition of the branching-step point process, selected branching random
  walk, and almost-sure speed;
- the many-to-one formula and the Mogul'skii small-deviation estimates;
- the couplings that yield the two eventual bounds under a first moment;
- an argument replacing the cross-pair second moment, if the cross-term
  assumption is also to be weakened.

Theorem 1.1 retains its stated fourth-moment assumption and its `L²` claim.
Theorem 1.3 currently retains the cross-term assumption. No assumption is
silently promoted to a verified Lean result.
