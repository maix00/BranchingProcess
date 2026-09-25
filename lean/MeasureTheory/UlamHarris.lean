import MeasureTheory.UlamHarris.Basic
import MeasureTheory.UlamHarris.Tree.Basic
import MeasureTheory.UlamHarris.Tree.Truncation
import MeasureTheory.UlamHarris.Tree.Topology
import MeasureTheory.UlamHarris.MarkedTree.Basic
import MeasureTheory.UlamHarris.Split

/-!
# The Ulam--Harris address space

Deterministic combinatorics of the rooted tree of addresses and the
declared-split predicate, together with the truncation, pointwise topology,
truncation topology, and Borel structure on trees. Nothing here mentions a
filtration, a probability measure, or a stopping time; the generation
filtration itself lives in
`Probability/BranchingRandomWalk/Tree/Filtration.lean`.
-/
