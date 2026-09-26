import Combinatorics.UlamHarris.Basic
import Combinatorics.BranchingWalk.Basic.Core
import Combinatorics.BranchingWalk.Basic.SurviveAlong
import Combinatorics.BranchingWalk.Step.Monotone

/-!
# Branching walks

`StepField α X = TreeNode α → Step α X` is the raw field of branching steps,
one at every address. `RootIndexed.BranchingWalk Root α X` bundles one step
field and one initial population for every initial ancestor, so the walk also
carries where it starts. `BranchingWalk α X` is the single-ancestor case
`RootIndexed.BranchingWalk PUnit α X`.
-/

namespace Combinatorics

namespace Branching

open Combinatorics.UlamHarris

/-- The raw branching step field: one branching step at every address. -/
abbrev IsParentClosed {α X : Type*} (β : StepField α X) : Prop :=
  ∀ u v, surviveAlong β [] (u ++ v) → surviveAlong β [] u

theorem isParentClosed_of_surviveAlong_prefix
    {α X : Type*} (β : StepField α X) : IsParentClosed β := by
  intro u v h
  exact surviveAlong_prefix β u v h

/-- A branching walk for every initial ancestor: one step field and one initial
position per root. -/
@[ext]
structure RootIndexed.BranchingWalk (Root α X : Type*) where
  /-- The step field of every initial ancestor. -/
  step : Root → StepField α X
  /-- The initial population of every initial ancestor. -/
  initial : Root → Set X
  parentClosed : ∀ r, IsParentClosed (step r)

/-- A branching walk: the single-ancestor case of `RootIndexed.BranchingWalk`. -/
abbrev BranchingWalk (α X : Type*) := RootIndexed.BranchingWalk PUnit.{1} α X

/-- A branching walk with one starting position for each initial ancestor: the
data that generates an indexed particle cloud. The initial population of a
`RootIndexed.BranchingWalk` is a set of positions per root, which does not single
out the position of one particle; a cloud keeps one particle per root, as the
probability layer does with its initial-position map `Root → X` next to a step
field. -/
structure RootIndexed.PositionedWalk (Root α X : Type*) where
  /-- The step field of every initial ancestor. -/
  step : Root → StepField α X
  /-- The starting position of the particle of every initial ancestor. -/
  start : Root → X

/-- The measurable space of a root-indexed branching walk is the product of the
step-field and initial-position coordinates. -/
instance {Root α X : Type*} [MeasurableSpace X] :
    MeasurableSpace (RootIndexed.BranchingWalk Root α X) :=
  MeasurableSpace.comap (fun β : RootIndexed.BranchingWalk Root α X =>
    (β.step, β.initial)) inferInstance

end Branching

end Combinatorics
