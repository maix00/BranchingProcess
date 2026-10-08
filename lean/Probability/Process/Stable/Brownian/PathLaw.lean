/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Skorokhod
public import Probability.Process.Stable.Brownian
public import Probability.Process.Stable.PathLaw
public import Topology.Cadlag.Skorokhod.Integral

/-!
# Brownian path laws as stable clock-process laws

The finite-horizon law of an everywhere-continuous Brownian version has the
stable clock-increment specification needed by the random-walk functional
limit theorem. The construction uses Mathlib's Brownian finite-dimensional
laws and the repository's generic path-map transfer lemma.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Skorokhod law of a pointwise-continuous pre-Brownian process is the
standard exponent-two stable clock-process law on `[0,1]`. The explicit
pointwise continuity and coordinate measurability hypotheses select a genuine
measurable path-valued realization; Mathlib's `IsBrownianReal` records
continuity only almost surely. -/
theorem IsPreBrownianReal.isStableClockProcessLaw_cadlagunitIntervalPathLaw
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    IsStableClockProcessLaw 2 (gaussianReal 0 (1 : ℝ≥0)) unitIntervalClock
      (cadlagunitIntervalPathLaw P B hcontinuous hmeasurable) := by
  let path : Ω → CadlagPath unitInterval ℝ :=
    cadlagunitIntervalPath B hcontinuous
  let pathLaw : Measure (CadlagPath unitInterval ℝ) :=
    cadlagunitIntervalPathLaw P B hcontinuous hmeasurable
  have htime : Monotone unitIntervalToNNReal := fun _ _ hst => hst
  have htimeBot : unitIntervalToNNReal ⊥ = 0 := by
    apply NNReal.coe_injective
    rfl
  have hinterval := hB.hasStableClockIncrements.comp_time
    unitIntervalToNNReal htime htimeBot
  have hclockEq :
      (fun t : unitInterval =>
        ((unitIntervalToNNReal t : ℝ≥0) : ℝ)) = unitIntervalClock := by
    funext t
    rfl
  have hinterval' : HasStableClockIncrements 2
      (gaussianReal 0 (1 : ℝ≥0)) unitIntervalClock
      (fun t ω => B (unitIntervalToNNReal t) ω) P := by
    simpa only [hclockEq] using hinterval
  have hpath : HasLaw path pathLaw P := by
    exact hasLaw_cadlagunitIntervalPath P B hcontinuous hmeasurable
  have hstable := hinterval'.law_of_pathMap hpath
    (fun t => Skorokhod.measurable_apply t)
    (fun t ω => by simp [path, cadlagunitIntervalPath_apply])
  simpa [pathLaw] using hstable

end ProbabilityTheory

end
