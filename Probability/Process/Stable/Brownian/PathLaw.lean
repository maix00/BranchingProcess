/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Skorokhod
public import Probability.Process.Stable.Brownian
public import Probability.Process.Stable.PathLaw
public import Probability.Process.Path.Cadlag.MeasurableMap
public import Probability.Process.Stable.PathLaw.UnitInterval
public import Topology.Cadlag.Skorokhod.Integral

/-!
# Brownian path laws as stable clock-process laws

Brownian motion on a finite horizon has the stable clock-increment
specification needed by the random-walk functional limit theorem. An
everywhere-continuous selected version uses the direct continuous-path map;
Mathlib's almost-surely continuous Brownian process uses the generic
rational-coordinate realization for càdlàg processes.
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
    IsStableClockProcessLaw 2 (gaussianReal 0 (1 : ℝ≥0)) UnitInterval.clock
      (cadlagunitIntervalPathLaw P B hcontinuous hmeasurable) := by
  let path : Ω → CadlagPath unitInterval ℝ :=
    cadlagunitIntervalPath B hcontinuous
  let pathLaw : Measure (CadlagPath unitInterval ℝ) :=
    cadlagunitIntervalPathLaw P B hcontinuous hmeasurable
  have htime : Monotone UnitInterval.toNNReal := fun _ _ hst => hst
  have htimeBot : UnitInterval.toNNReal ⊥ = 0 := by
    apply NNReal.coe_injective
    rfl
  have hinterval := hB.hasStableClockIncrements.comp_time
    UnitInterval.toNNReal htime htimeBot
  have hclockEq :
      (fun t : unitInterval =>
        ((UnitInterval.toNNReal t : ℝ≥0) : ℝ)) = UnitInterval.clock := by
    funext t
    rfl
  have hinterval' : HasStableClockIncrements 2
      (gaussianReal 0 (1 : ℝ≥0)) UnitInterval.clock
      (fun t ω => B (UnitInterval.toNNReal t) ω) P := by
    simpa only [hclockEq] using hinterval
  have hpath : HasLaw path pathLaw P := by
    exact hasLaw_cadlagunitIntervalPath P B hcontinuous hmeasurable
  have hpathEval : ∀ t,
      (fun ω => path ω t) =ᵐ[P]
        (fun ω => B (UnitInterval.toNNReal t) ω) := by
    intro t
    exact Filter.Eventually.of_forall fun ω => by
      simp [path, cadlagunitIntervalPath_apply]
  have hstable := hinterval'.law_of_pathMap_ae hpath
    (fun t => Skorokhod.measurable_apply t) hpathEval
  simpa [pathLaw] using hstable

/-- Mathlib's Brownian process, which is continuous only almost surely,
induces the exponent-two stable clock-process law on Skorokhod path space.
The path-valued random variable is obtained from its rational coordinates;
the measurable embedding theorem makes the construction valid after
completion on the exceptional non-càdlàg set. -/
theorem IsBrownianReal.isStableClockProcessLaw_cadlagunitIntervalProcessPathLaw
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    IsStableClockProcessLaw 2 (gaussianReal 0 (1 : ℝ≥0)) UnitInterval.clock
      (Process.Path.Cadlag.pathLaw P
        (fun t ω => B (UnitInterval.toNNReal t) ω)
          (fun t => hB.toIsPreBrownianReal.aemeasurable
            (UnitInterval.toNNReal t))) := by
  exact hB.isStableLevyProcess.isStableClockProcessLaw_unitIntervalPathLaw

end ProbabilityTheory

end
