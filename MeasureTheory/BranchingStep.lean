import MeasureTheory.BranchingStep.Basic
import MeasureTheory.BranchingStep.Field
import MeasureTheory.BranchingStep.Prefix
import MeasureTheory.BranchingStep.Position.Accumulate
import MeasureTheory.BranchingStep.Position.Increment
import MeasureTheory.BranchingStep.Position.Partial
import MeasureTheory.BranchingStep.Tree.Realization
import MeasureTheory.BranchingStep.Tree.Realized
import MeasureTheory.BranchingStep.Slot.Basic
import MeasureTheory.BranchingStep.Slot.Order
import MeasureTheory.BranchingStep.Slot.Position

/-!# Deterministic branching-step combinatorics

The slot encoding `Step ι X = ι → Option X`, its measurable structure, the
presence predicate and support, the order conditions on present slots, the
step fields over addresses, the accumulated marks along a path, realized
nodes, the realized and marked trees, and the real-line slot vocabulary. These
layers carry at most a measurable structure; they mention no probability
measure, filtration, or stopping time.
-/
