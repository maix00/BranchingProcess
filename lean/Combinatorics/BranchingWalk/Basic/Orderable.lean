import Combinatorics.BranchingWalk.Basic.Definitions
import Combinatorics.BranchingWalk.Step.Orderable

/-!
# The orderable form of a step field and of a walk

`Step.IsOrderable` is the step-level notion, and a finitely supported step on `ℕ` has it by
`Step.isOrderable_of_isFinitelySupported`. The classes here lift it: a step field on `ℕ` is orderable when
all of its steps are, and a root-indexed walk when all of its step fields are. Finiteness of the support is
an assumption about the steps and has no source in the slot type, so the field and the walk carry their own
classes, and the step-level property is then found by instance search.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

variable {Root X : Type*} [LinearOrder X]

/-- A finitely supported step on `ℕ` is orderable, by instance search. -/
instance (priority := 100) {ξ : Step ℕ X} [h : ξ.IsFinitelySupported] : ξ.IsOrderable :=
  Step.isOrderable_of_isFinitelySupported h

/-- A step field on `ℕ` is finitely supported when all of its steps are. -/
class StepField.IsFinitelySupported (β : StepField ℕ X) : Prop where
  pointwise : ∀ u, Step.IsFinitelySupported (β u)

/-- A step field on `ℕ` is orderable when all of its steps are. -/
class StepField.IsOrderable (β : StepField ℕ X) : Prop where
  pointwise : ∀ u, Step.IsOrderable (β u)

/-- A finitely supported step field is orderable, by instance search on its steps. -/
instance (priority := 100) {β : StepField ℕ X} [h : β.IsFinitelySupported] : β.IsOrderable :=
  ⟨fun u => by
    haveI := h.pointwise u
    exact inferInstance⟩

/-- A root-indexed walk is finitely supported when all of its step fields are. -/
class RootIndexed.BranchingWalk.IsFinitelySupported
    (β : RootIndexed.BranchingWalk Root ℕ X) : Prop where
  pointwise : ∀ r, StepField.IsFinitelySupported (β.step r)

/-- A root-indexed walk is orderable when all of its step fields are. -/
class RootIndexed.BranchingWalk.IsOrderable (β : RootIndexed.BranchingWalk Root ℕ X) : Prop where
  pointwise : ∀ r, StepField.IsOrderable (β.step r)

/-- A finitely supported walk is orderable, by instance search on its step fields. -/
instance (priority := 100) {β : RootIndexed.BranchingWalk Root ℕ X}
    [h : β.IsFinitelySupported] : β.IsOrderable :=
  ⟨fun r => by
    haveI := h.pointwise r
    exact inferInstance⟩

end Branching

end Combinatorics
