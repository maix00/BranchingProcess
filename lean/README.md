# Lean verification of the speed theorem

Run `lake build ThesisSpeed` in this directory. This project uses the local
mathlib checkout at `../../../mathlib4` and Lean `v4.26.0-rc2`.

`ThesisSpeed/Analytic.lean` currently verifies two analytic facts relevant to the new
Theorem 1.3:

1. A pointwise truncation inequality for controlling an exceptional event with
   a first moment in place of a fourth-moment/Cauchy--Schwarz estimate.
2. The exact final limit of the speed from eventual upper and lower bounds at
   every positive error, with coefficient `Real.pi ^ 2 * σ2 / 2`.

`ThesisSpeed/Probability/Stopping.lean` verifies that the first threshold
crossing of an adapted observable, or the first measurable success declaration,
is a stopping time, using mathlib's hitting-time theorem.
It also proves the generic recursion step: beginning observations after an
already established stopping time preserves the stopping-time property.
`ThesisSpeed/Probability/TimingCounterexample.lean` verifies a finite
counterexample: a time defined from the next generation need not be a stopping
time for the present-generation filtration. It also proves that a retrospectively selected generation-one state can fail adaptedness.
`ThesisSpeed/Probability/Measurability.lean` proves observable declarations for countably many pre-defined candidates and adaptedness of a measurable causal coupling recursion. The thesis-specific constructions still need to satisfy these interfaces.
`ThesisSpeed/Probability/Genealogy/Tree.lean` defines the deterministic
`GenealogicalTree` structure, the `MarkedTree` object of a realized tree with
marks on its realized nodes, the mark function `Mark`, the partial-function
and `?` views `MarkedTree.partialMark` and `MarkedTree.mark?` of the realized
marks, and the generation filtration on `Mark`.
`Genealogy/BranchingStepTree.lean` defines the step field
`BranchingStepField` and the objects derived from it: the realized tree
`branchingRealizedTree`, the accumulated marks `branchingStepAccumulatedMark`
and `branchingStepAccumulatedMark?`, and the marked tree
`branchingStepMarkedTree`.
`Genealogy/RootIndexed/Positions.lean` defines the root-indexed versions. The
legacy point-process layer uses `WeightedBranchingStep` only for the
still-migrating weighted-slot construction; the abstract branching interface
uses `BranchingStep ℕ X`. Probabilistic growth tails, the selected population,
and the full coupling remain to be modeled.
`ThesisSpeed/Probability/GeometricTrial.lean` verifies the geometric-series
part of the corrected joint transform for reboot waiting displacements.
`ThesisSpeed/Spine/FiniteKernel.lean` verifies the finite one-generation
normalization and both weighted and unweighted size-bias cancellation formulas.
It does not yet include the expectation and independence steps of the full
many-to-one formula.
The thesis-specific reboot time has not yet been identified with this generic
hitting time. See [FORMALIZATION_CHECKLIST.md](FORMALIZATION_CHECKLIST.md).

This is **not a formal proof of Theorem 1.3**. The following are still missing:

- a Lean definition of the offspring point process, selected branching random
  walk, and almost-sure speed;
- the many-to-one formula and the Mogul'skii small-deviation estimates;
- the couplings that yield the two eventual bounds under a first moment;
- an argument replacing the cross-pair second moment, if the cross-term
  assumption is also to be weakened.

Theorem 1.1 retains its stated fourth-moment assumption and its `L²` claim.
Theorem 1.3 currently retains the cross-term assumption. No assumption is
silently promoted to a verified Lean result.
