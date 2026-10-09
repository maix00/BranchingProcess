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
public import Topology.Cadlag.Skorokhod.Scaling

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
      (fun t ω => X (UnitInterval.toNNReal t) ω)
      (fun t => hX.increments.aemeasurable_eval (UnitInterval.toNNReal t)),
    inferInstance⟩

/-- The restriction of a stable Lévy process to `[0,1]`, represented in
Skorokhod space by the canonical rational-coordinate path map, has the
corresponding stable clock-process law. -/
theorem IsStableLevyProcess.isStableClockProcessLaw_unitIntervalPathLaw
    {α : ℝ} {μ : Measure ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    {X : ℝ≥0 → Ω → ℝ} (hX : IsStableLevyProcess α μ X Q) :
    IsStableClockProcessLaw α μ UnitInterval.clock hX.unitIntervalPathLaw := by
  let pathProcess : unitInterval → Ω → ℝ :=
    fun t ω => X (UnitInterval.toNNReal t) ω
  let coordinates : ∀ t, AEMeasurable (pathProcess t) Q := by
    intro t
    exact hX.increments.aemeasurable_eval (UnitInterval.toNNReal t)
  let pathLaw : Measure (CadlagPath unitInterval ℝ) := hX.unitIntervalPathLaw
  have htime : Monotone UnitInterval.toNNReal := fun _ _ h => h
  have htimeBot : UnitInterval.toNNReal ⊥ = 0 := by
    apply NNReal.coe_injective
    rfl
  have hincrements := hX.increments.comp_time
    UnitInterval.toNNReal htime htimeBot
  have hclockEq :
      (fun t : unitInterval =>
        ((UnitInterval.toNNReal t : ℝ≥0) : ℝ)) = UnitInterval.clock := by
    funext t
    rfl
  have hincrements' : HasStableClockIncrements α μ UnitInterval.clock
      pathProcess Q := by
    simpa only [pathProcess, hclockEq] using hincrements
  have hcadlag : ∀ᵐ ω ∂Q,
      IsCadlag (fun t : unitInterval => pathProcess t ω) := by
    filter_upwards [hX.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous htime UnitInterval.continuous_toNNReal
  have hpath := Process.Path.Cadlag.hasLaw_pathMap pathProcess coordinates
  have hpathEval : ∀ t,
      (fun ω => Process.Path.Cadlag.pathMap pathProcess ω t) =ᵐ[Q]
        pathProcess t := by
    intro t
    exact Process.Path.Cadlag.pathMap_ae_eval_eq pathProcess hcadlag t
  have hstable := hincrements'.law_of_pathMap_ae hpath
    (fun t => Skorokhod.measurable_apply t) hpathEval
  simpa [pathLaw, IsStableLevyProcess.unitIntervalPathLaw, pathProcess] using hstable

set_option linter.style.haveILetI false in
/-- Spatially scaling a stable unit-interval path law pushes its increment
law forward by the same factor. -/
theorem IsStableClockProcessLaw.spatialScale
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (h : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (q : ℝ) (hq : 0 < q) :
    IsStableClockProcessLaw α (μ.map fun x => q * x) UnitInterval.clock
      (P.map (Skorokhod.scalePath q)) := by
  change HasStableClockIncrements α μ UnitInterval.clock cadlagPathProcess P at h
  let X : unitInterval → CadlagPath unitInterval ℝ → ℝ := fun t f => q * f t
  let Q : Measure (CadlagPath unitInterval ℝ) :=
    P.map (Skorokhod.scalePath q)
  have hcontScale : Continuous (fun f : CadlagPath unitInterval ℝ =>
      Skorokhod.scalePath q f) := by
    have hp : Continuous (fun f : CadlagPath unitInterval ℝ => (q, f)) := by
      fun_prop
    exact Skorokhod.continuous_scalePath.comp hp
  letI : IsProbabilityMeasure Q :=
    (Measure.isProbabilityMeasure_map_iff hcontScale.aemeasurable).2 inferInstance
  have hscaled : HasStableClockIncrements α (μ.map fun x => q * x)
      UnitInterval.clock X P := by
    simpa [X, cadlagPathProcess] using h.map_spaceScale_measure q hq
  have hpathMapEq (f : CadlagPath unitInterval ℝ) :
      Process.Path.Cadlag.pathMap X f = Skorokhod.scalePath q f := by
    let p : CadlagPath unitInterval ℝ :=
      ⟨fun t => q * f t, f.isCadlag_toFun.const_smul q⟩
    have hcoords :
        (fun r : RationalCoordinate.UnitInterval =>
          X (RationalCoordinate.toUnitInterval r) f) =
        MeasureTheory.CadlagPath.denseEvaluation
          RationalCoordinate.toUnitInterval p := by
      funext r
      rfl
    have hmap : Process.Path.Cadlag.pathMap X f = p := by
      change Function.extend
        (MeasureTheory.CadlagPath.denseEvaluation
          RationalCoordinate.toUnitInterval)
        id (fun _ => Skorokhod.ofContinuousMap
          (ContinuousMap.const unitInterval 0))
        (fun r : RationalCoordinate.UnitInterval =>
          X (RationalCoordinate.toUnitInterval r) f) = p
      rw [hcoords]
      exact Process.Path.Cadlag.rationalEvaluationEmbedding.injective.extend_apply
        _ _ _
    rw [hmap]
    rfl
  have hpath : HasLaw (Process.Path.Cadlag.pathMap X) Q P := by
    have hmap : HasLaw (Skorokhod.scalePath q) Q P :=
      hasLaw_map hcontScale.aemeasurable
    exact hmap.congr (ae_of_all _ fun f => hpathMapEq f)
  have hcadlag : ∀ᵐ f ∂P, IsCadlag (fun t => X t f) := by
    filter_upwards with f
    exact f.isCadlag_toFun.const_smul q
  have heval : ∀ t,
      Measurable (fun f : CadlagPath unitInterval ℝ => f t) := by
    intro t
    exact Skorokhod.measurable_apply t
  have hpathEval : ∀ t,
      (fun f => Process.Path.Cadlag.pathMap X f t) =ᵐ[P] X t := by
    intro t
    exact Process.Path.Cadlag.pathMap_ae_eval_eq X hcadlag t
  have hresult := hscaled.law_of_pathMap_ae hpath heval hpathEval
  simpa [Q] using hresult

end ProbabilityTheory

end
