import MeasureTheory.BranchingWalk.Basic
import MeasureTheory.BranchingWalk.Field
import MeasureTheory.BranchingWalk.Prefix
import MeasureTheory.BranchingWalk.Position.Displace
import MeasureTheory.BranchingWalk.Position.Increment
import MeasureTheory.BranchingWalk.Position.Partial
import MeasureTheory.BranchingWalk.Tree.Realization
import MeasureTheory.BranchingWalk.Tree.Realized
import MeasureTheory.BranchingWalk.Slot.Basic
import MeasureTheory.BranchingWalk.Slot.Order
import MeasureTheory.BranchingWalk.Slot.Position

/-!# Deterministic branching-step combinatorics

The slot encoding `Step ι X = ι → Option X`, its measurable structure, the
presence predicate and support, the order conditions on present slots, the
step fields over addresses, the displacements along a path, realized
nodes, the realized and marked trees, and the real-line slot vocabulary. These
layers carry at most a measurable structure; they mention no probability
measure, filtration, or stopping time.
-/
