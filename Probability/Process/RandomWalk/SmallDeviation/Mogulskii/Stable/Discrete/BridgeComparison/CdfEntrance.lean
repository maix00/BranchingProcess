/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.BridgeComparison.SourceAsymptotics
import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.AllIndices

/-! # CDF entrance adapter for source equation (34)

The bridge comparison modules use Lean's `module` import discipline. The
all-index stable entrance theorem still belongs to the legacy import layer,
because its finite-variation Poisson construction depends on legacy imports.
This adapter joins those APIs and discharges the `α < 1` entrance input from
the original CDF sign condition. -/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The source bridge event at any interior center has positive stable-law
mass under the source CDF sign condition. This specializes the all-index
entrance theorem to the shifted corridor used by the finite bridge cells. -/
theorem sourceBridgeEntrance_pos_of_cdfAtZero_allIndices
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (radius x y : ℝ) (hradius : 0 < radius)
    (hx : -1 < x ∧ x < 1) (hy : -1 < y ∧ y < 1) :
    0 < Q (fullSegmentCorridorReturnEvent X 0 1
      (-1 - x) (1 - x) (y - x - radius) (y - x + radius)) := by
  convert hX.measure_fullEntrance_pos_of_cdfAtZero_allIndices hcdf
    (-y) (-x) radius
    (by constructor <;> linarith [hy.1, hy.2])
    (by constructor <;> linarith [hx.1, hx.2]) hradius using 1; ring_nf

/-- The source equation (34) lower bound with no auxiliary entrance
hypothesis: every bridge mass is obtained from the source CDF condition by
the centered, index-one, or finite-variation Poisson stable entrance result. -/
theorem exists_source_equation34_log_ratio_lower_of_stableDomain_of_cdfAtZero
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
    {ell : ℝ} (hell : 0 < ell)
    (hslowLimit : Tendsto (stableSlowVariation α ν) atTop (𝓝 ell))
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
  have hlow : α < 1 → ∀ radius y : ℝ, 0 < radius → -1 < y → y < 1 →
      ∀ x : SourceBridgeCenter,
        0 < Q (fullSegmentCorridorReturnEvent X 0 1
          (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)) := by
    intro _ radius y hradius hylo hyhi x
    exact sourceBridgeEntrance_pos_of_cdfAtZero_allIndices hX hcdf
      radius x.1 y hradius x.2 ⟨hylo, hyhi⟩
  exact exists_source_equation34_log_ratio_lower_of_stableDomain
    hX hP hcdf htight hnorm hDOA hscale hα₂ hell hslowLimit
    ε c b hε hc hcb hb bridgeLength hscaleAll hbridgeLe hbridgePos hlow
    hlimit δ hδ

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
