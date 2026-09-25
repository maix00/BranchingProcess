import Combinatorics.BranchingStep.AccumulatedMark
import Combinatorics.BranchingStep.Basic
import Combinatorics.BranchingStep.Field
import Combinatorics.BranchingStep.Increment
import Combinatorics.BranchingStep.PartialMark
import Combinatorics.BranchingStep.Position.Basic
import Combinatorics.BranchingStep.Prefix
import Combinatorics.BranchingStep.Realization
import Combinatorics.BranchingStep.RealizedTree
import Combinatorics.BranchingStep.Slot.Basic
import Combinatorics.BranchingStep.Slot.Order
import Combinatorics.BranchingStep.Slot.Position

/-!
# Deterministic branching-step combinatorics

The slot encoding `BranchingStep ι X = ι → Option X`, its measurable
structure, the order conditions on present slots, the increment and support
calculus, the step fields over addresses, the accumulated marks along a path,
realized nodes, and the real-line slot vocabulary. These layers carry at most
a measurable structure; they mention no probability measure, filtration, or
stopping time.
-/
