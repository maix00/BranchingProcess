/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher
public import Probability.BranchingRandomWalk.Walk.Basic

/-!
# The Rademacher walk as a singleton-slot branching walk

This module connects the process-level Rademacher increment law to the
singleton-slot branching-walk law.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching
open Combinatorics.Branching.Walk
open ProbabilityTheory.RandomWalk

/-- The everywhere-present random walk with IID Rademacher increments. -/
noncomputable def rademacher (initial : ℝ) : RandomWalk ℝ ℝ :=
  ofIncrementLaw initial (independentIncrementLaw rademacherMeasure)

@[simp]
theorem rademacher_law (initial : ℝ) :
    (rademacher initial).law =
      (independentIncrementLaw rademacherMeasure).map
        (Walk.ofIncrements initial) := rfl

/-- The Rademacher random walk is realized by an increment path. -/
theorem rademacher_isIncrementPathRealization (initial : ℝ) :
    IsIncrementPathRealization (rademacher initial) :=
  isIncrementPathRealization_ofIncrementLaw initial
    (independentIncrementLaw rademacherMeasure)

/-- Hence the canonical Rademacher random walk survives forever. -/
theorem rademacher_survivesForever (initial : ℝ) :
    SurvivesForever (rademacher initial) :=
  survivesForever_ofIncrementLaw initial
    (independentIncrementLaw rademacherMeasure)

/-- Along an increment realization, the process position is the project's
usual partial sum added to the initial position. -/
theorem process_ofIncrements_eq_partialSum
    (initial : ℝ) (increment : ℕ → ℝ) (n : ℕ) :
    process id n (Walk.ofIncrements initial increment) =
      some (initial + partialSum n increment) := by
  simp [positionProcess]


end ProbabilityTheory.BranchingRandomWalk.RandomWalk

end
