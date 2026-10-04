/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Definitions
public import Combinatorics.BranchingWalk.Step.Orderable

/-!
# The orderable form of a step field and of a walk

`Step.IsOrderable` is the step-level notion, and a finitely supported step on `ℕ` has it by
`Step.isOrderable_of_isFinitelySupported`. The classes here lift it: a step field is orderable when all of
its steps are, and a root-indexed walk when all of its step fields are.

Neither notion is about `ℕ`: a field or a walk is orderable whenever its steps are, on any slot type, so the
classes below are polymorphic and only raise the step-level property to the whole field or walk. Finiteness
of the support is an assumption about the steps and has no source in the slot type, so a field and a walk
carry their own classes for it as well. What is specific to `ℕ` is the instance that turns finite support
into orderability, because the relabelling proving it labels the children of a step by the ranks
`0, …, k - 1`, and the surviving slots of that relabelling are the slots below `k`.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

/-- A step field is finitely supported when all of its steps are. -/
class StepField.IsFinitelySupported {α X : Type*} (β : StepField α X) : Prop where
  pointwise : ∀ u, Step.IsFinitelySupported (β u)

/-- A root-indexed walk is finitely supported when all of its step fields are. -/
class RootIndexed.BranchingWalk.IsFinitelySupported
    {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) : Prop where
  pointwise : ∀ r, StepField.IsFinitelySupported (β.step r)

/-- A step field is orderable when all of its steps are. -/
class StepField.IsOrderable {α X : Type*} [LT α] [Preorder X] (β : StepField α X) : Prop where
  pointwise : ∀ u, Step.IsOrderable (β u)

/-- A root-indexed walk is orderable when all of its step fields are. -/
class RootIndexed.BranchingWalk.IsOrderable
    {Root α Mark Position : Type*} [LT α] [Preorder Mark]
    (β : RootIndexed.BranchingWalk Root α Mark Position) : Prop where
  pointwise : ∀ r, StepField.IsOrderable (β.step r)

section Nat

variable {Root Mark Position : Type*} [LinearOrder Mark]

/-- A finitely supported step on `ℕ` is orderable, by instance search. -/
instance (priority := 100) {ξ : Step ℕ Mark} [h : ξ.IsFinitelySupported] : ξ.IsOrderable :=
  Step.isOrderable_of_isFinitelySupported h

/-- A finitely supported step field on `ℕ` is orderable, by instance search on its steps. -/
instance (priority := 100) {β : StepField ℕ Mark} [h : β.IsFinitelySupported] : β.IsOrderable :=
  ⟨fun u => Step.isOrderable_of_isFinitelySupported (h.pointwise u)⟩

/-- A finitely supported root-indexed walk on `ℕ` is orderable, by instance search on its step fields. -/
instance (priority := 100)
    {β : RootIndexed.BranchingWalk Root ℕ Mark Position}
    [h : β.IsFinitelySupported] :
    β.IsOrderable :=
  ⟨fun r => ⟨fun u => Step.isOrderable_of_isFinitelySupported ((h.pointwise r).pointwise u)⟩⟩

end Nat

end Branching

end Combinatorics

end
