/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Law
public import Probability.BranchingRandomWalk.Step.Position.Measurability

/-!
# Measurability of branching-walk coordinates and survival

These results apply to arbitrary child-slot types. Singleton-slot random walks
use them as a special case.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

theorem measurable_step
    {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position] :
    Measurable (fun walk : BranchingWalk α Mark Position =>
      walk.step PUnit.unit) := by
  have hpair : Measurable
      (fun walk : BranchingWalk α Mark Position =>
        (walk.step, walk.initial)) :=
    Measurable.of_comap_le le_rfl
  exact (measurable_pi_apply PUnit.unit).comp (measurable_fst.comp hpair)

theorem measurableSet_survivesAlong
    {α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (u : TreeNode α) :
    MeasurableSet {walk : BranchingWalk α Mark Position |
      surviveAlong (walk.step PUnit.unit) [] u} := by
  have hs : MeasurableSet {step : StepField α Mark |
      surviveAlong step [] u} :=
    (generationFiltration (M := Step α Mark)).le u.length _
      (surviveAlong_root_measurableSet (X := Mark) u)
  exact hs.preimage measurable_step

end ProbabilityTheory.BranchingRandomWalk

end
