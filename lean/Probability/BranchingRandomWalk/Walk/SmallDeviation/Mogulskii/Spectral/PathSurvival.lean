/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.PathSurvival
public import Probability.BranchingRandomWalk.Walk.Path.Window
public import Probability.BranchingRandomWalk.Walk.Rademacher

/-!
# The Rademacher path bridge

This file identifies the process-level interval event with the same event
viewed through the singleton-slot branching-walk realization.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Matrix

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open Combinatorics.Branching.Walk

/-- The interval-kernel mass is the same event under the singleton-slot
branching-walk law and under the ordinary Rademacher increment law. -/
theorem intervalRademacherKernel_pow_apply_univ_eq_branchingWalkProcess
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (intervalRademacherKernel interiorCount ^ n) start Set.univ =
      (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.rademacher
        (intervalSite start)).law
        {walk | _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.ProcessInClosedInterval
          id 1 interiorCount n walk} := by
  rw [_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.rademacher_law,
    Measure.map_apply
      (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.measurable_ofIncrements
        (intervalSite start))
      (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.measurableSet_processInClosedInterval
        id measurable_id 1 interiorCount n)]
  change _ = independentIncrementLaw rademacherMeasure
    {increment | _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.ProcessInClosedInterval
      id 1 interiorCount n (ofIncrements (intervalSite start) increment)}
  rw [show {increment | _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.ProcessInClosedInterval
      id 1 interiorCount n (ofIncrements (intervalSite start) increment)} =
      {increment | InClosedInterval 1 interiorCount n (intervalSite start) increment} by
    ext increment
    exact _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.processInClosedInterval_ofIncrements_iff
      1 interiorCount n (intervalSite start) increment]
  exact intervalRademacherKernel_pow_apply_univ_eq_randomWalkInterval
    interiorCount n start

end ProbabilityTheory.BranchingRandomWalk.RandomWalk.SmallDeviation.Mogulskii

end
