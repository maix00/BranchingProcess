/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Cadlag.MeasurableMap
public import Probability.Process.Stable.FiniteDimensional
public import Probability.Process.Stable.Levy
public import Probability.Process.Stable.PathLaw

/-!
# Unit-interval path law of a stable Lévy process

An actual stable Lévy process on nonnegative time induces its canonical
càdlàg path law on `[0,1]`. This adapter constructs that law from the process
itself, so applications need not separately provide a compatible finite-
horizon path-law witness.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The canonical unit-interval path law induced by an actual stable Lévy
process, using its almost-everywhere measurable coordinates. -/
noncomputable def IsStableLevyProcess.unitIntervalPathLaw
    {α : ℝ} {μ : Measure ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsStableLevyProcess α μ X Q) :
    ProbabilityMeasure (CadlagPath unitInterval ℝ) :=
  ⟨Process.Path.Cadlag.pathLaw Q
      (fun t ω => X (unitIntervalToNNReal t) ω)
      (fun t => hX.increments.aemeasurable_eval (unitIntervalToNNReal t)),
    inferInstance⟩

/-- The restriction of a stable Lévy process to `[0,1]`, represented in
Skorokhod space by the canonical rational-coordinate path map, has the
corresponding stable clock-process law. -/
theorem IsStableLevyProcess.isStableClockProcessLaw_unitIntervalPathLaw
    {α : ℝ} {μ : Measure ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsStableLevyProcess α μ X Q) :
    IsStableClockProcessLaw α μ unitIntervalClock hX.unitIntervalPathLaw := by
  let pathProcess : unitInterval → Ω → ℝ :=
    fun t ω => X (unitIntervalToNNReal t) ω
  let coordinates : ∀ t, AEMeasurable (pathProcess t) Q := by
    intro t
    exact hX.increments.aemeasurable_eval (unitIntervalToNNReal t)
  let pathLaw : Measure (CadlagPath unitInterval ℝ) := hX.unitIntervalPathLaw
  have htime : Monotone unitIntervalToNNReal := fun _ _ h => h
  have htimeBot : unitIntervalToNNReal ⊥ = 0 := by
    apply NNReal.coe_injective
    rfl
  have hincrements := hX.increments.comp_time
    unitIntervalToNNReal htime htimeBot
  have hclockEq :
      (fun t : unitInterval =>
        ((unitIntervalToNNReal t : ℝ≥0) : ℝ)) = unitIntervalClock := by
    funext t
    rfl
  have hincrements' : HasStableClockIncrements α μ unitIntervalClock
      pathProcess Q := by
    simpa only [pathProcess, hclockEq] using hincrements
  have hcadlag : ∀ᵐ ω ∂Q,
      IsCadlag (fun t : unitInterval => pathProcess t ω) := by
    filter_upwards [hX.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous htime continuous_unitIntervalToNNReal
  have hpath := Process.Path.Cadlag.hasLaw_pathMap pathProcess coordinates
  have hpathEval : ∀ t,
      (fun ω => Process.Path.Cadlag.pathMap pathProcess ω t) =ᵐ[Q]
        pathProcess t := by
    intro t
    exact Process.Path.Cadlag.pathMap_ae_eval_eq pathProcess hcadlag t
  have hstable := hincrements'.law_of_pathMap_ae hpath
    (fun t => Skorokhod.measurable_apply t) hpathEval
  simpa [pathLaw, IsStableLevyProcess.unitIntervalPathLaw, pathProcess] using hstable

end ProbabilityTheory

end
