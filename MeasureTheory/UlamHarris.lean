import MeasureTheory.UlamHarris.Basic
import MeasureTheory.UlamHarris.Tree.Basic
import MeasureTheory.UlamHarris.Tree.Truncation
import MeasureTheory.UlamHarris.Tree.Height
import MeasureTheory.UlamHarris.Tree.Topology
import MeasureTheory.UlamHarris.Tree.Borel
import MeasureTheory.UlamHarris.Tree.Metric
import MeasureTheory.UlamHarris.Tree.FiniteLabels
import MeasureTheory.UlamHarris.Tree.Graph
import MeasureTheory.UlamHarris.Tree.LocallyFinite.Basic
import MeasureTheory.UlamHarris.Tree.LocallyFinite.Space
import MeasureTheory.UlamHarris.Tree.Finite.Basic
import MeasureTheory.UlamHarris.Tree.Finite.Space
import MeasureTheory.UlamHarris.MarkedTree.Basic
import MeasureTheory.UlamHarris.MarkedTree.Measurability
import MeasureTheory.UlamHarris.RootIndexedTree.Basic
import MeasureTheory.UlamHarris.RootIndexedTree.Measurability
import MeasureTheory.UlamHarris.RootIndexedTree.Topology
import MeasureTheory.UlamHarris.RootIndexedTree.Metric
import MeasureTheory.UlamHarris.RootIndexedTree.Borel
import MeasureTheory.UlamHarris.RootIndexedTree.Singleton
import MeasureTheory.UlamHarris.RootIndexedMarkedTree.Basic
import MeasureTheory.UlamHarris.RootIndexedMarkedTree.Measurability
import MeasureTheory.UlamHarris.RootIndexedMarkedTree.Singleton
import MeasureTheory.UlamHarris.Split

/-!
# The Ulam--Harris address space

Deterministic combinatorics of the rooted tree of addresses and the
declared-split predicate, together with the truncation, the agreement height,
the pointwise and truncation topologies, the tree metric, and the comparison of
the resulting Borel and cylinder σ-algebras. It also contains the spaces of
locally finite and finite trees, with their subspace topologies, subspace
σ-algebras, and restricted tree metrics. Nothing here mentions a filtration, a
probability measure, or a stopping time; the generation filtration itself lives
in
`Probability/BranchingRandomWalk/Tree/Filtration.lean`.

The root-indexed layer collects one such tree for each initial ancestor,
together with its product measurable structure, its product and uniform
topologies, the sup tree metric, and the corresponding Borel comparisons.
The root-indexed marked layer keeps the same separation of roots and records
marks on the realized nodes of each one; it carries the product measurable
structure, but no topology is imposed on marked trees.
-/
