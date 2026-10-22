/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.Bridge.Lemmas.TerminalLeftAsymptotics
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.Bridge.Lemmas.EndpointCorridorDecay
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.Bridge.Lemmas.EntrancePositivity
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate

/-! # Terminal-left logarithmic comparison

The public theorem exists_source_equation34_log_ratio_lower_of_stableDomain_slowVariation
gives the equation-(34) logarithmic comparison under the stable-domain
hypotheses of A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765;
English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081, Theorem 3, Section 4. It yields the endpoint-corridor
decay from slow variation and the two-scale condition, without imposing
a finite-limit assumption on L*.

The public theorem states that for every δ > 0, eventually
1 − δ ≤ log P_ν(Bₙ) / log P_ν(Eₙ), where Bₙ is the source base-corridor
event and Eₙ is the source endpoint-corridor event.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The equation-(34) logarithmic comparison under the stable-domain
hypotheses of Mogul'skii, *Small Deviations in a Space of Trajectories*,
Theorem 3, Section 4, with no extra finite-limit assumption on `L*`. The bridge
comparison and base-corridor positivity are the existing terminal-left-specific
inputs; this theorem supplies the missing endpoint probability decay from
slow variation and the two-scale condition. -/
theorem exists_source_equation34_log_ratio_lower_of_stableDomain_slowVariation
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω']
    {X : ℝ≥0 → Ω' → ℝ} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hnorm : IsStableNorming α ν normalization)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₂ : α < 2)
    (ε c b : ℝ) (hε : 0 < ε) (hc : -1 < c)
    (hcb : c < b) (hb : b < 1)
    (bridgeLength : ℕ → ℕ)
    (hscaleAll : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hbridgePos : ∀ᶠ n in atTop, 0 < bridgeLength n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale bridgeLength)
      atTop id (fun _ => iidSequenceLaw ν) P)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset SourceBridgeCenter, ∃ lowerBound : ℝ,
      F.Nonempty ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        1 - δ ≤ Real.log ((iidSequenceLaw ν
          (sourceBaseCorridorEvent (scale n) n)).toReal) /
          Real.log ((iidSequenceLaw ν
          (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal) := by
  have hα : 0 < α := hP.strictlyStable.1
  have hlow : α < 1 → ∀ radius y : ℝ, 0 < radius → -1 < y → y < 1 →
      ∀ x : SourceBridgeCenter,
        0 < Q (fullSegmentCorridorReturnEvent X 0 1
          (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)) := by
    intro _ radius y hradius hylo hyhi x
    exact sourceBridgeEntrance_pos_of_cdfAtZero_allIndices hX hcdf
      radius x.1 y hradius x.2 ⟨hylo, hyhi⟩
  obtain ⟨F, lowerBound, hF, hlowerBound, hcomparison⟩ :=
    exists_source_equation34_finite_bridge_comparison_of_cdf
      hX hP hcdf ε c b hε hc hcb hb scale bridgeLength hscaleAll
      hbridgeLe hbridgePos hlow hlimit
  have hbase : ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n) :=
    eventually_sourceBaseCorridorEvent_pos_of_stableDomain
      hDOA hP hX hcdf htight hnorm hα hα₂ hscale.scale_tendsto_atTop
  have htargetZero : Tendsto (fun n => (iidSequenceLaw ν
      (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal)
      atTop (𝓝 0) :=
    tendsto_sourceEndpointCorridor_toReal_zero_of_strictStableDomain_slowVariation
      ν μ hα hP.strictlyStable hα₂ hnorm hDOA hscale ε c b hε
  have hratio := eventually_one_sub_le_log_ratio_of_source_equation34
    F hF lowerBound hlowerBound ε c b scale hcomparison hbase htargetZero δ hδ
  exact ⟨F, lowerBound, hF, hlowerBound, hratio⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
