import MeasureTheory.BranchingWalk.Step.Basic
import MeasureTheory.BranchingWalk.Relation.Basic
import MeasureTheory.BranchingWalk.Relation.Field
import MeasureTheory.BranchingWalk.Step.Measurability
import MeasureTheory.BranchingWalk.Step.PointMeasure
import MeasureTheory.BranchingWalk.Ordered
import MeasureTheory.BranchingWalk.Basic
import MeasureTheory.BranchingWalk.Displace.Basic
import MeasureTheory.BranchingWalk.Displace.Partial
import MeasureTheory.BranchingWalk.Displace.Initial
import MeasureTheory.BranchingWalk.Displace.Node
import MeasureTheory.BranchingWalk.Tree.Realization
import MeasureTheory.BranchingWalk.Tree.Realized
import MeasureTheory.BranchingWalk.Tree.Correspondence.Basic
import MeasureTheory.BranchingWalk.Tree.Correspondence.Equiv
import MeasureTheory.BranchingWalk.Tree.Correspondence.RootIndexed
import MeasureTheory.BranchingWalk.Cloud.Basic
import MeasureTheory.BranchingWalk.Cloud.SliceMeasure
import MeasureTheory.BranchingWalk.Cloud.Measurability
import MeasureTheory.BranchingWalk.Cloud.Order.Slice
import MeasureTheory.BranchingWalk.Cloud.Order.Basic
import MeasureTheory.BranchingWalk.Cloud.Order.DiracSum
import MeasureTheory.BranchingWalk.Cloud.Frontier.Basic
import MeasureTheory.BranchingWalk.Trajectory.Basic
import MeasureTheory.BranchingWalk.Trajectory.Step
import MeasureTheory.BranchingWalk.Trajectory.Measurability
import MeasureTheory.BranchingWalk.Selection.Basic
import MeasureTheory.BranchingWalk.Selection.Card
import MeasureTheory.BranchingWalk.Selection.Mirror
import MeasureTheory.BranchingWalk.Selection.Walk
import MeasureTheory.BranchingWalk.Selection.Contain
import MeasureTheory.BranchingWalk.Selection.Mechanism
import MeasureTheory.BranchingWalk.Selection.NSelection.Basic
import MeasureTheory.BranchingWalk.Selection.Cloud
import MeasureTheory.BranchingWalk.Selection.Frontier
import MeasureTheory.BranchingWalk.Selection.Speed

/-!# Deterministic branching-step combinatorics

The slot encoding `Step ι X = ι → Option X`, its measurable structure, the
presence predicate and support, the raw and zero-defaulted slot readings, the
relation and ordered-step layers, the child vocabulary, the step fields over
addresses, the displacements along a path, realized nodes, the realized and
marked trees, the real-line slot vocabulary, and the deterministic selection
mechanisms with the `N`-branching walks, clouds, frontiers, and frontier speeds
they generate. These layers carry at most a measurable structure; they mention
no probability measure, filtration, or stopping time.
-/
