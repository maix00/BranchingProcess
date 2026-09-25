import Combinatorics.BranchingStep.Basic
import Combinatorics.BranchingStep.Field
import Combinatorics.BranchingStep.Prefix
import Combinatorics.BranchingStep.Position.Accumulate
import Combinatorics.BranchingStep.Position.Increment
import Combinatorics.BranchingStep.Position.Partial
import Combinatorics.BranchingStep.Tree.Realization
import Combinatorics.BranchingStep.Tree.Realized
import Combinatorics.BranchingStep.Slot.Basic
import Combinatorics.BranchingStep.Slot.Order
import Combinatorics.BranchingStep.Slot.Position

/-!# Deterministic branching-step combinatorics

The slot encoding `Step ι X = ι → Option X`, its measurable structure, the
presence predicate and support, the order conditions on present slots, the
step fields over addresses, the accumulated marks along a path, realized
nodes, the realized and marked trees, and the real-line slot vocabulary. These
layers carry at most a measurable structure; they mention no probability
measure, filtration, or stopping time.
-/
