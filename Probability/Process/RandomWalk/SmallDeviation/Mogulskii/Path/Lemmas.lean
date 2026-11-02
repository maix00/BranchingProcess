/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic
import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnionNullMeasurable
import Probability.Sequence.IID.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Internal path-law transfer lemma for Mogul'skii rates

This module contains the non-reusable transfer step used by
`Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Path.Realization`.

## Internal proof declarations

- `measure_sourceFiniteCorridorUnionEvent_eq_of_iid` transfers the probability
  of a finite corridor union from an arbitrary i.i.d. realization to the
  canonical sequence law, using the induced path law and
  null-measurability of the corridor event.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

lemma measure_sourceFiniteCorridorUnionEvent_eq_of_iid
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {coordinate : ℕ → Ω → ℝ}
    (hindep : iIndepFun coordinate P)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    (hlaw : ∀ k, HasLaw (coordinate k) ν P)
    (scale : ℕ → ℝ) (n : ℕ) {α : ℝ} (C : FiniteCorridorUnion α) :
    P {ω | terminalLeftNormalizedStepCadlagPathIcc scale n
        (fun k => coordinate k ω) ∈ C.toSet} =
      iidSequenceLaw ν {increment |
        terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈ C.toSet} := by
  let pathMap : (ℕ → ℝ) → CadlagPath unitInterval ℝ :=
    terminalLeftNormalizedStepCadlagPathIcc scale n
  let pathLaw : Measure (CadlagPath unitInterval ℝ) :=
    (iidSequenceLaw ν).map pathMap
  let realizedPath : Ω → CadlagPath unitInterval ℝ := fun ω =>
    pathMap (fun k => coordinate k ω)
  have hrealizedLaw : HasLaw realizedPath pathLaw P := by
    simpa [realizedPath, pathLaw, pathMap] using
      hasLaw_terminalLeftNormalizedStepCadlagPathIcc_of_iid
        hindep hmeasurable hlaw scale n
  have hpathEvent : NullMeasurableSet C.toSet pathLaw := by
    dsimp [pathLaw]
    exact FiniteCorridorUnion.nullMeasurableSet_toSet C _
  have hrealizedPathEvent : NullMeasurableSet C.toSet (P.map realizedPath) := by
    rw [hrealizedLaw.map_eq]
    exact hpathEvent
  calc
    P {ω | realizedPath ω ∈ C.toSet} = P.map realizedPath C.toSet :=
      (Measure.map_apply₀ hrealizedLaw.aemeasurable hrealizedPathEvent).symm
    _ = pathLaw C.toSet := by rw [hrealizedLaw.map_eq]
    _ = iidSequenceLaw ν {increment | pathMap increment ∈ C.toSet} := by
      dsimp [pathLaw]
      exact Measure.map_apply₀
        (measurable_terminalLeftNormalizedStepCadlagPathIcc scale n).aemeasurable
        (by simpa [pathLaw, pathMap] using hpathEvent)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
