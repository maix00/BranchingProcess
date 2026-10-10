/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.ProcessExistence
public import Probability.Process.Stable.PathLaw.FullProcess
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic

/-!
# Stable escape rates from tight random-walk sources

This is the small-deviation adapter from the general stable process existence
theorem to the process escape-rate interface.
-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A tight source path-law subsequence yields a full-time stable Lévy process
and its unit-interval escape-rate witness. -/
theorem exists_generatedStableProcess_escapeRate_of_tightSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hStable : IsStrictlyAlphaStable α μ)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    ∃ P : ProbabilityMeasure (CadlagPath unitInterval ℝ),
      ∃ hP : IsStableClockProcessLaw α μ UnitInterval.clock (P : Measure _),
        ∃ C, HasStableProcessEscapeRate α μ
          ((iidUnitPathBlockProcess_isStableLevyProcess hP).unitIntervalPathLaw :
            Measure (CadlagPath unitInterval ℝ)) C := by
  obtain ⟨P, hP, _sub, _hsub, _hconv⟩ :=
    exists_stableClockProcessLaw_of_tightSource hDOA hStable htight
  let hX := iidUnitPathBlockProcess_isStableLevyProcess hP
  obtain ⟨C, hEscape⟩ :=
    hX.isStableClockProcessLaw_unitIntervalPathLaw
      |>.hasStableProcessEscapeRate_of_isStableLevyProcess hX hcdf
  exact ⟨P, hP, C, hEscape⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
