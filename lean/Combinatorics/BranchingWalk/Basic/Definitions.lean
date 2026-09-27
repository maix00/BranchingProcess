import Combinatorics.UlamHarris.Basic
import Combinatorics.BranchingWalk.Basic.Core
import Combinatorics.BranchingWalk.Basic.SurviveAlong
import Combinatorics.BranchingWalk.Step.Monotone

/-!
# Branching walks

`StepField α X = TreeNode α → Step α X` is the raw field of branching steps,
one at every address. `RootIndexed.BranchingWalk Root α Mark Position`
bundles one mark-valued step field and one position-valued initial population
for every initial ancestor. `BranchingWalk α Mark Position` is its
single-ancestor case.
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

namespace RootIndexed

/-- A branching walk for every initial ancestor: one step field and one initial
position per root. -/
@[ext]
structure BranchingWalk (Root α Mark Position : Type*) where
  /-- The step field of every initial ancestor. -/
  step : Root → StepField α Mark
  /-- The initial position of the particle of every initial ancestor. -/
  initial : Root → Position
  parentClosed : ∀ r, IsParentClosed (step r)

namespace BranchingWalk

/-- Bundle a raw root-indexed step field and its initial positions as a
branching walk. Parent closure follows from path realization itself. -/
def ofStepField {Root α Mark Position : Type*}
    (initial : Root → Position) (step : Root → StepField α Mark) :
    RootIndexed.BranchingWalk Root α Mark Position where
  step := step
  initial := initial
  parentClosed r := isParentClosed_of_surviveAlong_prefix (step r)

@[simp] theorem ofStepField_step {Root α Mark Position : Type*}
    (initial : Root → Position) (step : Root → StepField α Mark) :
    (ofStepField initial step :
      RootIndexed.BranchingWalk Root α Mark Position).step = step :=
  rfl

@[simp] theorem ofStepField_initial {Root α Mark Position : Type*}
    (initial : Root → Position) (step : Root → StepField α Mark) :
    (ofStepField initial step :
      RootIndexed.BranchingWalk Root α Mark Position).initial = initial :=
  rfl

end BranchingWalk

end RootIndexed

/-- A branching walk: the single-ancestor case of `RootIndexed.BranchingWalk`. -/
abbrev BranchingWalk (α Mark Position : Type*) :=
  RootIndexed.BranchingWalk PUnit.{1} α Mark Position

/-- The measurable space of a root-indexed branching walk is the product of the
step-field and initial-position coordinates. -/
instance {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position] :
    MeasurableSpace (RootIndexed.BranchingWalk Root α Mark Position) :=
  MeasurableSpace.comap
    (fun β : RootIndexed.BranchingWalk Root α Mark Position =>
      (β.step, β.initial)) inferInstance

end Branching

end Combinatorics
