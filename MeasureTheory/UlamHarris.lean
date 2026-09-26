import Combinatorics.UlamHarris.Basic
import Combinatorics.UlamHarris.Tree.Basic
import Combinatorics.UlamHarris.Tree.Truncation
import Combinatorics.UlamHarris.Tree.Height
import Combinatorics.UlamHarris.Tree.Topology
import Combinatorics.UlamHarris.Tree.Borel
import Combinatorics.UlamHarris.Tree.Metric
import Combinatorics.UlamHarris.Tree.FiniteLabels
import Combinatorics.UlamHarris.Tree.Graph.IsTree
import Combinatorics.UlamHarris.Tree.LocallyFinite.Basic
import Combinatorics.UlamHarris.Tree.LocallyFinite.Space
import Combinatorics.UlamHarris.Tree.Finite.Basic
import Combinatorics.UlamHarris.Tree.Finite.Space
import Combinatorics.UlamHarris.MarkedTree.Basic
import Combinatorics.UlamHarris.MarkedTree.SiblingOrder
import Combinatorics.UlamHarris.MarkedTree.Forget
import Combinatorics.UlamHarris.MarkedTree.Measurability
import Combinatorics.UlamHarris.RootIndexedTree.Basic
import Combinatorics.UlamHarris.RootIndexedTree.Measurability
import Combinatorics.UlamHarris.RootIndexedTree.Topology
import Combinatorics.UlamHarris.RootIndexedTree.Metric
import Combinatorics.UlamHarris.RootIndexedTree.Borel
import Combinatorics.UlamHarris.RootIndexedTree.Singleton
import Combinatorics.UlamHarris.RootIndexedTree.Graph.IsTree
import Combinatorics.UlamHarris.RootIndexedTree.Graph.Singleton
import Combinatorics.UlamHarris.RootIndexedMarkedTree.Basic
import Combinatorics.UlamHarris.RootIndexedMarkedTree.Forget
import Combinatorics.UlamHarris.RootIndexedMarkedTree.Measurability
import Combinatorics.UlamHarris.RootIndexedMarkedTree.Singleton
import Combinatorics.UlamHarris.Split

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
