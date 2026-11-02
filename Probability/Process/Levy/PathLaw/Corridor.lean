/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.PathLaw.UnitInterval
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Corridor probabilities under Lévy path laws

## Public declarations

- `ProbabilityTheory.IsLevyProcess.unitIntervalPathLaw_measure_corridorStartingAtZero`:
  if $X_0=0$ almost surely, the path-law probability that
  $t\mapsto X_{Tt}$ starts at zero and stays uniformly inside $(l,u)$ equals
  the process probability that $X_{Tt}-X_0$ stays uniformly inside $(l,u)$:
  \[
    \operatorname{Law}(t\mapsto X_{Tt})
      (\operatorname{corridorStartingAtZero}(l,u))
      =\mathbb P\{\exists\eta>0,\ \forall t\in[0,1],\ l+\eta
        \le X_{Tt}-X_0\le u-\eta\}.
  \]

This identity uses the canonical rational-coordinate realization of an
almost-surely càdlàg process and the complete-segment corridor event. It
requires no stable-law assumptions.
- `ProbabilityTheory.IsLevyProcess.unitIntervalPathLaw_measure_corridorReturnEvent`:
  when $X_0=0$ almost surely, the path-law mass of the zero-start corridor
  with terminal value in $(c,d)$ satisfies
  \[
    \mathcal L((X_{Tt})_{t\in[0,1]})
      \bigl(\{f:f(0)=0,\ \exists\eta>0,\ \forall t\in[0,1],\
        l+\eta\le f(t)\le u-\eta,\ f(1)\in(c,d)\}\bigr)
    =\mathbb P\bigl\{\exists\eta>0,\ \forall t\in[0,1],\
        l+\eta\le X_{Tt}-X_0\le u-\eta,\ X_T-X_0\in(c,d)\bigr\}.
  \]
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.IsLevyProcess

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℝ≥0 → Ω → ℝ}

/-- The unit-interval path-law probability of a centered open corridor is the
probability of the corresponding complete-segment corridor for the original
process. -/
theorem unitIntervalPathLaw_measure_corridorStartingAtZero
    (h : IsLevyProcess X P) (horizon : ℝ≥0) (lower upper : ℝ) :
    (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ))
        (Skorokhod.corridorStartingAtZero lower upper) =
      P (fullSegmentCorridorEvent X 0 horizon lower upper) := by
  let process : unitInterval → Ω → ℝ := fun t ω =>
    X (horizon * unitInterval.toNNReal t) ω
  have hprocessCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : unitInterval => process t ω) := by
    let timeChange : unitInterval → ℝ≥0 :=
      fun t => horizon * unitInterval.toNNReal t
    have htimeMonotone : Monotone timeChange := by
      intro s t hst
      exact mul_le_mul_of_nonneg_left hst horizon.2
    have htimeContinuous : Continuous timeChange := by
      exact continuous_const.mul unitInterval.toNNReal_continuous
    filter_upwards [h.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous htimeMonotone htimeContinuous
  have hpathLaw : HasLaw (Process.Path.Cadlag.pathMap process)
      (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)) P := by
    simpa [unitIntervalPathLaw, process, Process.Path.Cadlag.pathLaw] using
      (Process.Path.Cadlag.hasLaw_pathMap process
        (fun t => h.aemeasurable_eval _))
  have hpreimage :
      {ω | Process.Path.Cadlag.pathMap process ω ∈
        Skorokhod.corridorStartingAtZero lower upper} =ᵐ[P]
        fullSegmentCorridorEvent X 0 horizon lower upper := by
    filter_upwards [h.ae_start_eq_zero, hprocessCadlag] with ω hzero hω
    rw [Process.Path.Cadlag.pathMap_eq_of_cadlag process ω hω]
    have hbot : unitInterval.toNNReal ⊥ = 0 := by
      apply Subtype.ext
      simp [unitInterval.toNNReal]
    simp [process, Skorokhod.corridorStartingAtZero,
      Skorokhod.rangeInOpenInterval, fullSegmentCorridorEvent,
      segmentIncrement, hzero, hbot]
  have hcorridorMeasurable :=
    Skorokhod.measurableSet_corridorStartingAtZero lower upper
  calc
    (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ))
        (Skorokhod.corridorStartingAtZero lower upper) =
      P {ω | Process.Path.Cadlag.pathMap process ω ∈
        Skorokhod.corridorStartingAtZero lower upper} :=
      (hpathLaw.measure_eq hcorridorMeasurable).symm
    _ = P (fullSegmentCorridorEvent X 0 horizon lower upper) :=
      measure_congr hpreimage

/-- The unit-interval path-law probability of a zero-start corridor with an
open terminal window is the probability of the corresponding complete-segment
corridor return event for the original process. -/
theorem unitIntervalPathLaw_measure_corridorReturnEvent
    (h : IsLevyProcess X P) (horizon : ℝ≥0)
    (lower upper coreLower coreUpper : ℝ) :
    (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ))
        (Skorokhod.corridorStartingAtZero lower upper ∩
          {f : CadlagPath unitInterval ℝ | f ⊤ ∈ Set.Ioo coreLower coreUpper}) =
      P (fullSegmentCorridorReturnEvent X 0 horizon lower upper
        coreLower coreUpper) := by
  let process : unitInterval → Ω → ℝ := fun t ω =>
    X (horizon * unitInterval.toNNReal t) ω
  have hprocessCadlag : ∀ᵐ ω ∂P,
      IsCadlag (fun t : unitInterval => process t ω) := by
    let timeChange : unitInterval → ℝ≥0 :=
      fun t => horizon * unitInterval.toNNReal t
    have htimeMonotone : Monotone timeChange := by
      intro s t hst
      exact mul_le_mul_of_nonneg_left hst horizon.2
    have htimeContinuous : Continuous timeChange := by
      exact continuous_const.mul unitInterval.toNNReal_continuous
    filter_upwards [h.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous htimeMonotone htimeContinuous
  have hpathLaw : HasLaw (Process.Path.Cadlag.pathMap process)
      (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)) P := by
    simpa [unitIntervalPathLaw, process, Process.Path.Cadlag.pathLaw] using
      (Process.Path.Cadlag.hasLaw_pathMap process
        (fun t => h.aemeasurable_eval _))
  let pathEvent : Set (CadlagPath unitInterval ℝ) :=
    Skorokhod.corridorStartingAtZero lower upper ∩
      {f : CadlagPath unitInterval ℝ | f ⊤ ∈ Set.Ioo coreLower coreUpper}
  have hpathEventMeasurable : MeasurableSet pathEvent := by
    apply (Skorokhod.measurableSet_corridorStartingAtZero lower upper).inter
    exact (Skorokhod.measurable_apply ⊤) measurableSet_Ioo
  have hpreimage :
      {ω | Process.Path.Cadlag.pathMap process ω ∈ pathEvent} =ᵐ[P]
        fullSegmentCorridorReturnEvent X 0 horizon lower upper
          coreLower coreUpper := by
    filter_upwards [h.ae_start_eq_zero, hprocessCadlag] with ω hzero hω
    rw [Process.Path.Cadlag.pathMap_eq_of_cadlag process ω hω]
    have hbot : unitInterval.toNNReal ⊥ = 0 := by
      apply Subtype.ext
      simp [unitInterval.toNNReal]
    simp [pathEvent, process, Skorokhod.corridorStartingAtZero,
      Skorokhod.rangeInOpenInterval, fullSegmentCorridorReturnEvent,
      segmentCorridorEndpointEvent, fullSegmentCorridorEvent,
      segmentIncrement, hzero, hbot]
  calc
    (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ))
        pathEvent =
      P {ω | Process.Path.Cadlag.pathMap process ω ∈ pathEvent} :=
      (hpathLaw.measure_eq hpathEventMeasurable).symm
    _ = P (fullSegmentCorridorReturnEvent X 0 horizon lower upper
          coreLower coreUpper) := measure_congr hpreimage

end ProbabilityTheory.IsLevyProcess

end
