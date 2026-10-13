/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.EndpointBridge
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableLower.CellBridge

/-!
# Stable lower bounds for endpoint bridges

This file specializes the stable endpoint-core estimate to the bridge from
the central third of `[-D, 0]` to the terminal interval of a wider corridor.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A wider stable corridor has an eventual quantitative lower bound for the
robust bridge from the central third of `[-D, 0]` to its terminal unit-width
window. The event is exactly the block event consumed by
`iidSequenceLaw_measure_mul_of_finiteMovingEntranceEvent_bridge`. -/
theorem exists_eventually_iidSequenceLaw_rightEndpointBridge_ge_stableCellLowerBound
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale 2 ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation 2 ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate 2 μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess 2 μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (ratio : ℝ) (hratio : 1 < ratio)
    (total : ℕ → ℕ) {duration : ℝ} (hduration : 0 < duration)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp
          ((C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
            (Asymptotics.balancedBlockCount
              (total n - stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n)
              (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale n) + 1) ≤
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              Combinatorics.Sequence.blockCoordinates 0 (total n) increment ∈
                {block |
                  RandomWalk.SmallDeviation.Mogulskii.Discrete.partitionCellCoreReturnBlockEvent
                    (scale n * (-ratio)) (scale n * (0 : ℝ))
                    (scale n * (-1 / 2)) (scale n * (1 / 6))
                    (scale n * (-ratio + 1 / 2)) (scale n * (1 / 2)) block}} := by
  let innerLower : ℝ := -ratio
  let innerUpper : ℝ := 0
  let startCenter : ℝ := -1 / 2
  let startRadius : ℝ := 1 / 6
  let endCenter : ℝ := -ratio + 1 / 2
  let endRadius : ℝ := 1 / 2
  let lower : ℝ := -ratio + 2 / 3 + 1 / 100
  let upper : ℝ := 1 / 3 - 1 / 100
  let epsilon : ℝ := 1 / 100
  let margin : ℝ := 1 / 100
  let delta : ℝ := 1
  have hlower : lower = innerLower + startRadius + margin - startCenter := by
    dsimp [lower, innerLower, startRadius, margin, startCenter]
    ring
  have hupper : upper = innerUpper - startRadius - margin - startCenter := by
    dsimp [upper, innerUpper, startRadius, margin, startCenter]
    ring
  have hmargin : 0 < margin := by norm_num [margin]
  have hepsilon : 0 < epsilon := by norm_num [epsilon]
  have hdelta : 0 < delta := by norm_num [delta]
  have hendpointBand : 3 * epsilon < (endRadius - startRadius) / 2 := by
    norm_num [epsilon, endRadius, startRadius]
  have hreturnWindows : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon := by
    intro i hi
    have hi' : (-3 : ℝ) ≤ (i : ℝ) ∧ (i : ℝ) ≤ 3 := by
      exact_mod_cast (Finset.mem_Icc.mp hi)
    constructor
    · dsimp [lower, epsilon]
      nlinarith [hratio, hi'.1]
    · dsimp [upper, epsilon]
      nlinarith [hi'.2]
  have hbridgeWindows :
      lower + 4 * epsilon < endCenter - startCenter - 4 * epsilon ∧
        endCenter - startCenter + 4 * epsilon < upper - 4 * epsilon := by
    constructor
    · dsimp [lower, epsilon, endCenter, startCenter]
      nlinarith [hratio]
    · dsimp [upper, epsilon, endCenter, startCenter]
      nlinarith [hratio]
  obtain ⟨amplitude, hamplitude, hcell⟩ :=
    exists_eventually_partitionCellCoreReturnBlockEvent_ge_exp_of_stableEscapeRate
      hscale (by norm_num) (by norm_num) hslow hEscape hX hcdf hDOA htightBase
      (innerLower := innerLower) (innerUpper := innerUpper)
      (startCenter := startCenter) (startRadius := startRadius)
      (endCenter := endCenter) (endRadius := endRadius)
      (lower := lower) (upper := upper) (epsilon := epsilon) (margin := margin)
      (delta := delta) hlower hupper hmargin hepsilon hdelta hendpointBand hreturnWindows
      hbridgeWindows total hduration htotal
  have hwidth : (upper - lower - 8 * epsilon) / 2 = ratio / 2 - 13 / 60 := by
    dsimp [upper, lower, epsilon]
    ring
  have hcoefficient :
      C / (((upper - lower - 8 * epsilon) / 2) ^ (2 : ℝ)) - delta =
        C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1 := by
    rw [hwidth]
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hcell] with n hn
  simpa only [hcoefficient, innerLower, innerUpper, startCenter, startRadius,
    endCenter, endRadius] using hn

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
