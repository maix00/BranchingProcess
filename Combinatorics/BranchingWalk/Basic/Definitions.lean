/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.StepField
public import Combinatorics.BranchingWalk.Basic.Survival.SurviveAlong

/-!
# Branching walks

`StepField α X = TreeNode α → Step α X` is the raw field of branching steps,
one at every address. `RootIndexed.BranchingWalk Root α Mark Position`
bundles one mark-valued step field and one position-valued initial population
for every initial ancestor. `BranchingWalk α Mark Position` is its
single-ancestor case.

The public declarations are:

- `IsParentClosed`: $\forall u,v$, survival at $u++v$ implies survival at
  $u$.
- `isParentClosed_of_surviveAlong_prefix`: every step field satisfies this
  prefix-closure property.
- `RootIndexed.BranchingWalk`: the data
  $\mathrm{step}:Root\to\mathrm{StepField}(\alpha,Mark)$ and
  $\mathrm{initial}:Root\to Position$.
- `RootIndexed.BranchingWalk.parentClosed`: each root's realized walk is
  parent-closed.
- `RootIndexed.BranchingWalk.ofStepField`,
  `RootIndexed.BranchingWalk.ofStepField_step`, and
  `RootIndexed.BranchingWalk.ofStepField_initial`: construct the structure
  from its two coordinate maps and recover those maps by projection.
- `BranchingWalk`: the single-ancestor specialization with root type
  $\mathrm{PUnit}$.
- The `MeasurableSpace (RootIndexed.BranchingWalk Root α Mark Position)`
  instance is the comap of the product sigma algebra along
  $\beta\mapsto(\beta.\mathrm{step},\beta.\mathrm{initial})$.
-/

@[expose] public section

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

namespace BranchingWalk

/-- Every realized branching walk is parent-closed by the prefix property of
`surviveAlong`; this is derived from the step field rather than stored. -/
theorem parentClosed {Root α Mark Position : Type*}
    (β : RootIndexed.BranchingWalk Root α Mark Position) :
    ∀ r, IsParentClosed (β.step r) :=
  fun r => isParentClosed_of_surviveAlong_prefix (β.step r)

/-- Bundle a raw root-indexed step field and its initial positions as a
branching walk. Parent closure follows from path realization itself. -/
def ofStepField {Root α Mark Position : Type*}
    (initial : Root → Position) (step : Root → StepField α Mark) :
  RootIndexed.BranchingWalk Root α Mark Position where
  step := step
  initial := initial

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

end
