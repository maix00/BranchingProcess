# BranchingProcess

`BranchingProcess` is a Lean 4 and Mathlib library for formalizing branching
processes, branching random walks, random walks, and their path-space limits.
It is an active research formalization. Contributions, issue reports, theorem
suggestions, and improvements to the library are welcome.

## Mathematical scope

The library is organized by mathematical domain. The table names the main
interfaces and theorem families; each link goes to the narrow module that
defines or proves it.

| Domain | Core definitions and theorem interfaces | Status |
| --- | --- | --- |
| Ulam--Harris trees and branching walks | [`Step`](Combinatorics/BranchingWalk/Step/Basic.lean), [`surviveAlong`](Combinatorics/BranchingWalk/Basic/SurviveAlong.lean), [`RootIndexed.BranchingWalk`](Combinatorics/BranchingWalk/Basic/Definitions.lean), parent closure and sibling closure | Reusable foundation |
| Random fields and genealogy | Product laws for step fields, generation filtrations, adapted selections, multi-root marginals, fixed and selected descendant laws | Reusable interfaces; theorem-specific instances continue to grow |
| Point processes and spines | [`PointProcess`](Probability/PointProcess/Basic.lean), Dirac point measures, exponential tilting, spine laws, and both directions of the many-to-one formulas | Core formulas formalized |
| Kernels and survival | Markov/sub-Markov kernels, killed and return kernels, corridor survival, block and entrance estimates | Reusable kernel layer |
| Functional limits | Independent-increment finite-dimensional laws, Donsker finite-dimensional and path interfaces, tightness criteria, Brownian and Skorokhod adapters | Interfaces and major inputs formalized |
| Stable processes | [`HasStableClockIncrements`](Probability/Process/Stable/Basic.lean), stable Lévy specializations, finite-dimensional scaling, path-law interfaces, truncated-variance quantities | Stable process infrastructure; final small-deviation theorem remains open |
| Mogulskii small deviations | Diffusive and stable scales, Gaussian block limits, killed-interval spectral modes, return estimates, and rate-function components | Proof assembly is in progress |

The basic deterministic objects are intentionally small:

```lean
abbrev Combinatorics.Branching.Step (ι X : Type*) := ι → Option X

def Combinatorics.Branching.surviveAlong
    (step : TreeNode α → Step α X) : TreeNode α → TreeNode α → Prop

structure Combinatorics.Branching.RootIndexed.BranchingWalk
    (Root α Mark Position : Type*) where
  step : Root → TreeNode α → Step α Mark
  initial : Root → Position
  parentClosed : ∀ r, IsParentClosed (step r)
```

`Option` is part of the model: a step may have no children. Finiteness,
countability, ordering, and measurability are added only by the modules that
need them. The root-indexed construction is the common pre-sampled field for
multiple initial particles; a finite family is obtained by taking a marginal.

## What is complete and what is open

### Formalized interfaces and theorem families

- deterministic trees, marked trees, optional child slots, survival, positions,
  clouds, trajectories, ordering, selection, and domination maps;
- single-root and arbitrary-root product laws, generation filtrations,
  adapted/stopped constructions, branching-property interfaces, and selected
  subtree laws;
- point-measure and point-process observations, normalized potential laws,
  spine changes of measure, and the two orientations of endpoint and ancestral
  path many-to-one formulas;
- killed and return kernels, kernel iteration, corridor identities, and finite
  block estimates;
- central-limit and Donsker inputs, path tightness criteria, Brownian bridges,
  stable process interfaces, and the finite-state spectral estimates used by
  the Mogulskii route.

### Current research targets

- the final varying-boundary finite-variance Mogulskii asymptotic, including
  the quantitative entrance estimate and the last blocking step;
- the general stable Mogulskii theorem and its Skorokhod path-law bridge;
- the remaining quantitative estimates for the selected-walk speed theorems,
  including the first-moment and cross-term hypotheses needed by the thesis;
- the final assembly of the thesis statements (including the proposed
  first-moment version) from the verified interfaces above.

The detailed dependency graph and proof boundary are kept in
[`ARCHITECTURE.md`](ARCHITECTURE.md) and
[`FORMALIZATION_CHECKLIST.md`](FORMALIZATION_CHECKLIST.md). A theorem marked
as an interface there is not silently treated as a completed asymptotic
theorem.

## Contributing

Please read [`CONTRIBUTING.md`](CONTRIBUTING.md) before opening a pull request.
Good contributions include a missing measurability lemma, a reusable
probability or topology interface, a corrected theorem statement, a smaller
dependency boundary, and documentation that makes an existing result easier
to use.

Use GitHub issues for questions, counterexamples, proof gaps, and proposed
improvements. Pull requests should import the narrowest module available,
reuse Mathlib definitions when possible, include the smallest meaningful
verification target, and update the proof-boundary documentation when a
theorem changes status.

For questions that do not fit an issue, contact
**wang_yi_yang@foxmail.com**.

## Build and use

The repository pins Lean, Mathlib, and BrownianMotion in
[`lean-toolchain`](lean-toolchain), [`lakefile.toml`](lakefile.toml), and
[`lake-manifest.json`](lake-manifest.json). A clean checkout can be built with:

```sh
lake update
lake exe cache get
lake build
```

Import the narrowest module that provides the needed definition or theorem.
There is deliberately no umbrella import. For example:

```lean
import Probability.BranchingRandomWalk.Walk.Basic
import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.CLT
import Probability.PointProcess.Basic
```

The standalone library is released from the `lean/` subtree of the thesis
checkout. See [`RELEASE.md`](RELEASE.md) for the reproducible release check.

## License

The original source and documentation in this repository are released under
the [Apache License 2.0](LICENSE). Mathlib, BrownianMotion, and other external
dependencies retain their own licenses.
