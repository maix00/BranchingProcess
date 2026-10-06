# Lean library architecture

`BranchingProcess` formalizes deterministic tree and path objects, measure and
probability interfaces, and theorem-specific branching and random-walk
arguments. Module placement follows the mathematics of a declaration, rather
than the application that first needs it.

## Domain owners

| Domain | Owns | Examples |
| --- | --- | --- |
| `Combinatorics` | Deterministic trees, optional child steps, genealogies, and finite selections | `UlamHarris`, `BranchingWalk`, `TreeNode` |
| `Algebra`, `Order`, `Analysis` | Deterministic paths, finite sums, grids, inequalities, scales, and asymptotics | `AdditivePath`, `UniformGrid`, `BlockScale` |
| `MeasureTheory` | Operations and properties of measures and integrals that do not require a probability model | convolution powers, Dirac sums, measure limits |
| `Topology` | Path spaces, càdlàg geometry, and Skorokhod criteria | `CadlagPath`, oscillation and compactness criteria |
| `Probability` | Laws, filtrations, independence, random processes, and almost-everywhere statements | IID sequences, random walks, Lévy and stable processes |
| `Probability/BranchingRandomWalk` | Random branching models and their bridges to general process and measure interfaces | offspring fields, spines, selection and coupling |

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

For the detailed ownership map and examples of reused Mathlib objects, see
[`docs/architecture/MODULE_OWNERSHIP.md`](docs/architecture/MODULE_OWNERSHIP.md).
For the completed structural moves and their remaining proof obligations, see
[`docs/architecture/MIGRATION_PLAN.md`](docs/architecture/MIGRATION_PLAN.md).
For theorem-by-theorem formalization status, see
[`FORMALIZATION_CHECKLIST.md`](FORMALIZATION_CHECKLIST.md).

There is no umbrella import. Import the module that owns the required
definition or theorem. The dependency graph and API are checked by the
repository scripts described in [`CONTRIBUTING.md`](CONTRIBUTING.md).
