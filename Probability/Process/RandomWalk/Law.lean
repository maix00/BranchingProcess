/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID

/-!
# Independent increment laws

The countable product of a one-step law is the canonical increment-path law
of a random walk. This construction is independent of branching and tilting.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Canonical independent increment-path law with common marginal `ν`. -/
noncomputable def independentIncrementLaw {E : Type*} [MeasurableSpace E]
    (ν : Measure E) : Measure (ℕ → E) :=
  iidSequenceLaw ν

noncomputable instance independentIncrementLaw.instIsProbabilityMeasure
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentIncrementLaw ν) := by
  unfold independentIncrementLaw
  exact iidSequenceLaw.instIsProbabilityMeasure ν

theorem independentIncrementLaw_coordinate {E : Type*} [MeasurableSpace E]
    (ν : Measure E)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (independentIncrementLaw ν).map (fun increment : ℕ → E => increment n) = ν := by
  unfold independentIncrementLaw
  exact iidSequenceLaw_map_apply ν n

theorem independentIncrementLaw_independent {E : Type*} [MeasurableSpace E]
    (ν : Measure E)
    [IsProbabilityMeasure ν] :
    iIndepFun (fun n (increment : ℕ → E) => increment n)
      (independentIncrementLaw ν) := by
  unfold independentIncrementLaw
  exact iidSequenceLaw_independent ν

/-- The increment process seen after any deterministic time has the original
i.i.d. increment law. -/
theorem independentIncrementLaw_map_natAdd {E : Type*} [MeasurableSpace E]
    (ν : Measure E)
    [IsProbabilityMeasure ν] (offset : ℕ) :
    (independentIncrementLaw ν).map
        (fun increment n => increment (offset + n)) =
      independentIncrementLaw ν := by
  exact ProbabilityTheory.iidSequenceLaw_map_natAdd ν offset

end ProbabilityTheory.RandomWalk
