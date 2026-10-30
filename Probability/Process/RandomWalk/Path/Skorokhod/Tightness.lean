/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Tight
public import MeasureTheory.Measure.Tight.FiniteFamily
public import Probability.Process.RandomWalk.Path.Skorokhod.Core
public import Probability.Process.RandomWalk.Path.Skorokhod.Basic

/-!
# Tightness of fixed random-walk path laws

For each fixed step count, the normalized path law is a continuous image of
the countable product law of the increments. Mathlib's tightness theorem for
finite measures on Polish spaces therefore gives tightness of each individual
path law and of every finite family of such laws.

## Public declarations

* `isTightMeasureSet_singleton_normalizedStepPathLaw` states
  `IsTightMeasureSet {normalizedStepPathLaw ν scale n}`.
* `isTightMeasureSet_normalizedStepPathLaw_image_of_finite` states that for
  finite `I`, `IsTightMeasureSet (normalizedStepPathLaw ν scale '' I)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

/-- Every fixed-step normalized random-walk path law is tight. -/
theorem isTightMeasureSet_singleton_normalizedStepPathLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (scale : ℕ → ℝ) (n : ℕ) :
    IsTightMeasureSet {normalizedStepPathLaw ν scale n} := by
  let hsource : IsTightMeasureSet {iidSequenceLaw ν} :=
    isTightMeasureSet_singleton
  have hmap := hsource.map (continuous_normalizedStepCadlagPathIcc scale n)
  simpa [normalizedStepPathLaw, iidSequenceLaw] using hmap

/-- Every finite set of fixed-step normalized random-walk path laws is tight.
This supplies the finite-index part of an asymptotic path-tightness argument. -/
theorem isTightMeasureSet_normalizedStepPathLaw_image_of_finite
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (scale : ℕ → ℝ)
    {I : Set ℕ} (hI : I.Finite) :
    IsTightMeasureSet (normalizedStepPathLaw ν scale '' I) := by
  exact isTightMeasureSet_image_of_finite (normalizedStepPathLaw ν scale)
    hI (fun n => isTightMeasureSet_singleton_normalizedStepPathLaw ν scale n)

end ProbabilityTheory.RandomWalk

end
