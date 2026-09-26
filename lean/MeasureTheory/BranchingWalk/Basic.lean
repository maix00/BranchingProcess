import MeasureTheory.UlamHarris.Basic
import MeasureTheory.BranchingWalk.Step.Basic
import MeasureTheory.BranchingWalk.Ordered

/-!
# Branching walks

`StepField α X = TreeNode α → Step α X` is the raw field of branching steps,
one at every address. `RootIndexedBranchingWalk Root α X` bundles one step
field and one initial population for every initial ancestor, so the walk also
carries where it starts. `BranchingWalk α X` is the single-ancestor case
`RootIndexedBranchingWalk PUnit α X`.
-/

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris

/-- The raw branching step field: one branching step at every address. -/
abbrev StepField (α X : Type*) := TreeNode α → Step α X

/-- A branching walk for every initial ancestor: one step field and one initial
position per root. -/
@[ext]
structure RootIndexedBranchingWalk (Root α X : Type*) where
  /-- The step field of every initial ancestor. -/
  step : Root → StepField α X
  /-- The initial population of every initial ancestor. -/
  initial : Root → Set X

/-- A branching walk: the single-ancestor case of `RootIndexedBranchingWalk`. -/
abbrev BranchingWalk (α X : Type*) := RootIndexedBranchingWalk PUnit.{1} α X

/-- The present marks of every step increase along the slot order. -/
abbrev IsOrdered {α X : Type*} [LT α] [LE X] (β : StepField α X) : Prop :=
  ∀ u, markOrdered (β u)

/-- The measurable space of a root-indexed branching walk is the product of the
step-field and initial-position coordinates. -/
instance {Root α X : Type*} [MeasurableSpace X] :
    MeasurableSpace (RootIndexedBranchingWalk Root α X) :=
  MeasurableSpace.comap (fun β : RootIndexedBranchingWalk Root α X =>
    (β.step, β.initial)) inferInstance

end BranchingWalk

end MeasureTheory
