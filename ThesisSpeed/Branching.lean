import ThesisSpeed.Branching.AccumulatedMark
import ThesisSpeed.Branching.Field
import ThesisSpeed.Branching.PartialMark
import ThesisSpeed.Branching.Position.Basic
import ThesisSpeed.Branching.Realization
import ThesisSpeed.Branching.RealizedTree
import ThesisSpeed.Branching.Slot.Basic
import ThesisSpeed.Branching.Slot.Order
import ThesisSpeed.Branching.Slot.Position
import ThesisSpeed.Branching.Step

/-!
# Deterministic branching-step combinatorics

The slot encoding `BranchingStep ι X = ι → Option X`, its fields, the
accumulated marks along a path, realized nodes, and the ordered-slot
vocabulary. These layers carry at most a measurable structure; they mention
no probability measure, filtration, or stopping time.
-/
