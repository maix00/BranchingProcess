/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Path
public import Probability.BranchingRandomWalk.Walk.Path.Window
public import Probability.BranchingRandomWalk.Walk.Rademacher

/-!
# Finite-interval survival for the Rademacher branching walk

## Public declarations

For `interiorCount n : ℕ` and an initial site `start : Fin interiorCount`,
`ProbabilityTheory.BranchingRandomWalk.RandomWalk.intervalRademacherKernel_pow_apply_univ_eq_processInClosedInterval`
identifies the $n$-step killed-kernel mass with the path probability of the
branching-walk realization:

$$
(K^n)(\mathrm{start},\mathrm{univ})
=\mathbb P_{\mathrm{rademacher}(\mathrm{intervalSite}(\mathrm{start}))}
  \left\{w:\forall k\le n,\ \mathrm{process}(\mathrm{id},k,w)
  \in\{\mathrm{some}(x):1\le x\le\mathrm{interiorCount}\}\right\}.
$$

Here $K$ is `intervalRademacherKernel`. The theorem identifies its iterated
survival mass with the same finite-time window event under the
singleton-slot branching-walk law. The generic composition and iterate laws
for kernels are supplied by Mathlib; this module provides the project-specific
identification with the branching-walk path event.
-/

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval
open Combinatorics.Branching.Walk

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- The interval-kernel mass is the same event under the singleton-slot
branching-walk law and under the ordinary Rademacher increment law. -/
theorem intervalRademacherKernel_pow_apply_univ_eq_processInClosedInterval
    (interiorCount n : ℕ) (start : Fin interiorCount) :
    (intervalRademacherKernel interiorCount ^ n) start Set.univ =
      (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.rademacher
        (intervalSite start)).law
        {walk | _root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.ProcessInClosedInterval
          id 1 interiorCount n walk} := by
  rw [_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.rademacher_law,
    MeasureTheory.Measure.map_apply
      (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.measurable_ofIncrements
        (intervalSite start))
      (_root_.ProbabilityTheory.BranchingRandomWalk.RandomWalk.measurableSet_processInClosedInterval
        id measurable_id 1 interiorCount n)]
  change _ = iidSequenceLaw rademacherMeasure
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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk

end
