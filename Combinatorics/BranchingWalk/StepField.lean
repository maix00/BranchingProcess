/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.BranchingWalk.Step.Map
public import Combinatorics.UlamHarris.Basic

/-!
# Fields of branching steps

## Public declarations

For $\beta:\operatorname{TreeNode}(\alpha)\to\operatorname{Step}(\alpha,X)$:

* `Combinatorics.Branching.StepField α X` is the function type
  $\operatorname{TreeNode}(\alpha)\to\operatorname{Step}(\alpha,X)$.
* `Combinatorics.Branching.StepField.map` maps every mark by $f:X\to Y$.
  `Combinatorics.Branching.StepField.map_apply` gives
  $(\beta.\operatorname{map}(f))(u)=(\beta(u)).\operatorname{map}(f)$.
* `Combinatorics.Branching.StepField.map_id` and
  `Combinatorics.Branching.StepField.map_map` give
  $\beta.\operatorname{map}(\mathrm{id})=\beta$ and
  $(\beta.\operatorname{map}(f)).\operatorname{map}(g)
    =\beta.\operatorname{map}(g\circ f)$.
  `Combinatorics.Branching.StepField.map_measurable` states that
  $\operatorname{StepField.map}(f)$ is measurable when $f$ is measurable.
* `Combinatorics.Branching.StepField.forgetMarks` replaces each mark with
  $\mathrm{PUnit.unit}$ and preserves its optional child slots:
  $(\operatorname{forgetMarks}(\beta))(u)
    =(\beta(u)).\operatorname{map}(\lambda\_,\mathrm{PUnit.unit})$.

A step field assigns one complete optional child-slot configuration to every
potential address. This module contains its type and pointwise mark maps, below
the definitions of realized branching walks.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- A field of branching steps, one optional offspring configuration at every
Ulam--Harris address. -/
abbrev StepField (α X : Type*) := TreeNode α → Step α X

/-- Map the mark of every step in a deterministic field. -/
def StepField.map {α X Y : Type*} (f : X → Y)
    (β : StepField α X) : StepField α Y :=
  fun u => (β u).map f

@[simp] theorem StepField.map_apply {α X Y : Type*} (f : X → Y)
    (β : StepField α X) (u : TreeNode α) :
    β.map f u = (β u).map f := rfl

@[simp] theorem StepField.map_id {α X : Type*} (β : StepField α X) :
    β.map id = β := by
  funext u
  exact Step.map_id (β u)

@[simp] theorem StepField.map_map {α X Y Z : Type*}
    (g : Y → Z) (f : X → Y) (β : StepField α X) :
    (β.map f).map g = β.map (g ∘ f) := by
  funext u
  exact Step.map_map g f (β u)

/-- Mapping marks coordinatewise is measurable when the mark map is
measurable. -/
theorem StepField.map_measurable {α X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {f : X → Y} (hf : Measurable f) :
    Measurable (StepField.map (α := α) f) := by
  rw [measurable_pi_iff]
  intro u
  exact (Step.map_measurable hf).comp (measurable_pi_apply u)

/-- Forget every child mark while retaining exactly the child slots. -/
def StepField.forgetMarks {α X : Type*} (β : StepField α X) :
    StepField α PUnit.{1} :=
  β.map (fun _ => PUnit.unit.{1})

end Combinatorics.Branching

end
