/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PartitionEnergyUpper
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.PartitionLower.EnergyLower

/-!
# Exact discrete finite-partition Mogulskii rate

The endpoint-core product lower bound and the selected-cell range upper bound
give the exact stable logarithmic rate for every admissible `M₂` step
corridor.
-/

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

open ProbabilityTheory.Process.SmallDeviation.Mogulskii
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete

/-- Exact stable small-deviation asymptotics for a finite-partition `M₂`
corridor. The returned positivity statement justifies the real logarithm for
all sufficiently large horizons. -/
theorem tendsto_scaledLog_normalizedStepCorridor_eq_energyRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (c : M2Corridor) :
    (∀ᶠ n : ℕ in atTop,
      0 < iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet
            c.upper c.lower}) ∧
    Tendsto (fun n => stableSmallDeviationRate α ν scale n * Real.log
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
          ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet
            c.upper c.lower}).toReal)
      atTop (𝓝 (C * 2 ^ α * (c.energy α).toReal)) := by
  classical
  let corridorProbability (n : ℕ) : ENNReal :=
    iidSequenceLaw ν {increment : ℕ → ℝ |
      RandomWalk.normalizedStepCadlagPathIcc scale n increment ∈
        ProbabilityTheory.Process.SmallDeviation.Mogulskii.corridorSet
          c.upper c.lower}
  let corridorRate (n : ℕ) : ℝ :=
    stableSmallDeviationRate α ν scale n * Real.log (corridorProbability n).toReal
  let target : ℝ := C * 2 ^ α * (c.energy α).toReal
  have hpositiveBound :=
    eventually_stableSmallDeviationRate_mul_log_normalizedStepCorridor_ge_energy
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c (error := 1) (by norm_num)
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < corridorProbability n := by
    filter_upwards [hpositiveBound] with n hn
    simpa [corridorProbability] using hn.1
  have hrateNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ stableSmallDeviationRate α ν scale n := by
    have hscaleTop := hscale.scale_tendsto_atTop
    have hslowPos : ∀ᶠ n : ℕ in atTop,
        0 < stableSlowVariation α ν (scale n) :=
      hscaleTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hscale.eventually_scale_pos,
      hslowPos] with n hn hs hL
    rw [stableSmallDeviationRate]
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hprobabilityLeOne (n : ℕ) : corridorProbability n ≤ 1 := by
    calc
      corridorProbability n ≤ iidSequenceLaw ν Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hrateLeZero : ∀ᶠ n : ℕ in atTop, corridorRate n ≤ 0 := by
    filter_upwards [hrateNonneg] with n hrate
    have hprobabilityTop : corridorProbability n ≠ ⊤ :=
      ne_of_lt ((hprobabilityLeOne n).trans_lt ENNReal.one_lt_top)
    have hprobabilityRealLe : (corridorProbability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hprobabilityTop ENNReal.one_ne_top).2
        (hprobabilityLeOne n)
    have hlogNonpos : Real.log (corridorProbability n).toReal ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg hprobabilityRealLe
    simpa [corridorRate] using
      mul_nonpos_of_nonneg_of_nonpos hrate hlogNonpos
  have hrateBounded : Filter.IsBoundedUnder (· ≤ ·) atTop corridorRate :=
    Filter.isBoundedUnder_of_eventually_le (a := 0) hrateLeZero
  have hupper : atTop.limsup corridorRate ≤ target := by
    simpa [corridorRate, corridorProbability, target] using
      limsup_scaledLog_normalizedStepCorridor_le_energyRate
        hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
  have hlimit : Tendsto corridorRate atTop (𝓝 target) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro y hy
      let ε : ℝ := (target - y) / 2
      have hε : 0 < ε := by dsimp [ε]; linarith
      have hlower :=
        eventually_stableSmallDeviationRate_mul_log_normalizedStepCorridor_ge_energy
          hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase c
          (error := ε) hε
      filter_upwards [hlower] with n hn
      have hrateLower : target - ε ≤ corridorRate n := by
        simpa [target, corridorRate, corridorProbability] using hn.2
      have hyLower : y < target - ε := by dsimp [ε]; linarith
      exact hyLower.trans_le hrateLower
    · intro y hy
      have hstrict : atTop.limsup corridorRate < y := lt_of_le_of_lt hupper hy
      exact Filter.eventually_lt_of_limsup_lt hstrict hrateBounded
  exact ⟨hpositive, by simpa [corridorRate, corridorProbability, target] using hlimit⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
