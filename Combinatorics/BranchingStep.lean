import Combinatorics.BranchingStep.AccumulatedMark
import Combinatorics.BranchingStep.Field
import Combinatorics.BranchingStep.PartialMark
import Combinatorics.BranchingStep.Position.Basic
import Combinatorics.BranchingStep.Realization
import Combinatorics.BranchingStep.RealizedTree
import Combinatorics.BranchingStep.Slot.Basic
import Combinatorics.BranchingStep.Slot.Order
import Combinatorics.BranchingStep.Slot.Position
import Combinatorics.BranchingStep.Basic

/-!
# Deterministic branching-step combinatorics

The slot encoding `BranchingStep ι X = ι → Option X`, its fields, the
accumulated marks along a path, realized nodes, and the ordered-slot
vocabulary. These layers carry at most a measurable structure; they mention
no probability measure, filtration, or stopping time.
-/
