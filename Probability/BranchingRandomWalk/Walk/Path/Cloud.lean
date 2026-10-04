/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Position
public import Probability.BranchingRandomWalk.Walk.Kernel.Basic

/-!
# Random-walk paths in branching clouds

This file closes the probability-level square between the four views of a
single-lineage walk:

* the increment path;
* displacement along the unique tree address;
* position in the associated generation cloud;
* the iterated increment kernel.

The equalities are stated for an abstract additive position space.  Killing
is handled separately by `RandomWalk.process`; the cloud formula below reads
the position attached to the unique address of an everywhere-present
increment realization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching
open Combinatorics.Branching.Walk

variable {E : Type*} [AddCommMonoid E]

/-- The generation-cloud position of an increment realization is its initial
position plus the corresponding partial sum.  In particular, its displacement
term is the same `displaceWith` used by every branching walk. -/
theorem discreteTimeCloud_position_ofIncrements
    (initial : E) (increment : ℕ → E) (n : ℕ) :
    (Cloud.discreteTimeCloud_ofBranchingWalk id
        (Walk.ofIncrements initial increment)).position
        PUnit.unit (Walk.lineNode n) =
      positionProcess initial n increment := by
  exact Walk.discreteTimeCloud_position_lineNode_eq_positionProcess
    id initial increment n

/-- Equivalently, the displacement part of the cloud position is the partial
sum before the initial position is added. -/
theorem discreteTimeCloud_displacement_ofIncrements
    (initial : E) (increment : ℕ → E) (n : ℕ) :
    displaceWith id
        ((Walk.ofIncrements initial increment).step PUnit.unit) []
        (Walk.lineNode n) = partialSum n increment := by
  exact Walk.displaceWith_lineNode_eq_partialSum id increment n

/-- Reading a fixed generation-cloud coordinate from an increment path is a
measurable random variable. -/
theorem measurable_discreteTimeCloud_position_ofIncrements
    [MeasurableSpace E] [MeasurableAdd₂ E] (initial : E) (n : ℕ) :
    Measurable (fun increment : ℕ → E =>
      (Cloud.discreteTimeCloud_ofBranchingWalk id
          (Walk.ofIncrements initial increment)).position
          PUnit.unit (Walk.lineNode n)) := by
  rw [show (fun increment : ℕ → E =>
      (Cloud.discreteTimeCloud_ofBranchingWalk id
          (Walk.ofIncrements initial increment)).position
          PUnit.unit (Walk.lineNode n)) =
      fun increment => initial + partialSum n increment by
    funext increment
    exact discreteTimeCloud_position_ofIncrements initial increment n]
  exact measurable_const.add (partialSum_measurable n)

/-- Under IID increments, the law of a generation-cloud position is the
`n`-step law of the increment kernel.  Thus the cloud/displacement description
and the Chapman--Kolmogorov description are literally the same random walk. -/
theorem iidSequenceLaw_map_discreteTimeCloud_position
    [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (initial : E) (n : ℕ) :
    (iidSequenceLaw ν).map (fun increment : ℕ → E =>
      (Cloud.discreteTimeCloud_ofBranchingWalk id
          (Walk.ofIncrements initial increment)).position
          PUnit.unit (Walk.lineNode n)) =
      (incrementKernel ν ^ n) initial := by
  rw [show (fun increment : ℕ → E =>
      (Cloud.discreteTimeCloud_ofBranchingWalk id
          (Walk.ofIncrements initial increment)).position
          PUnit.unit (Walk.lineNode n)) =
      fun increment => initial + partialSum n increment by
    funext increment
    exact discreteTimeCloud_position_ofIncrements initial increment n]
  exact iidSequenceLaw_map_initial_add_partialSum ν n initial

/-- Under IID increments, every coordinate of the standard time-indexed
position process has the same iterated-kernel law as the corresponding cloud
coordinate. -/
theorem iidSequenceLaw_map_positionProcess
    [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableSingletonClass E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (initial : E) (n : ℕ) :
    (iidSequenceLaw ν).map (positionProcess initial n) =
      (incrementKernel ν ^ n) initial := by
  exact iidSequenceLaw_map_initial_add_partialSum ν n initial

end ProbabilityTheory.RandomWalk
