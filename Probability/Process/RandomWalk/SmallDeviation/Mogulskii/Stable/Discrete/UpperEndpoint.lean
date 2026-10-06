/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Block
public import Probability.Distributions.Stable.Attraction.Norming.Inverse
public import Probability.Process.RandomWalk.Kernel.Killed.Blocking
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
public import Probability.ConvergenceInDistribution.Portmanteau
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# A stable-domain discrete upper block estimate

At a stable block length, convergence of the block endpoint gives a uniform
upper bound on the probability of surviving one corridor block, uniformly
over every allowed starting point.  The killed-kernel blocking inequality
then raises this bound to the number of complete blocks.  This is a
non-sharp, endpoint-based subcase of the discrete upper comparison in
Mogulskii's Lemma 3; it does not require a path-space functional limit.

The strict endpoint-mass inequality is an explicit input.  It is the only
distributional estimate on the stable limit used here.
-/

open Filter MeasureTheory Set
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Along stable-domain assumptions, a strict one-block endpoint-mass bound
implies an exponential upper bound for the horizontal corridor probability.
The exponent is the number of complete blocks of length
`stableBlockLength α ν constant scale n`.  The hypotheses retain the
centering contribution and the limiting endpoint mass explicitly.

This is a discrete upper estimate, not the sharp stable small-deviation
constant: a path can leave the corridor and return between block endpoints,
so an endpoint bound alone only gives a non-sharp estimate. -/
theorem eventually_horizontalTubeProbability_le_pow_stableBlock_endpointMass
    (ν μ : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α constant : ℝ} (hα : 0 < α) (hα₂ : α ≤ 2)
    (hconstant : 0 < constant)
    {normalization center scale : ℕ → ℝ}
    (hnorm : IsStableNorming α ν normalization)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hscale : Tendsto scale atTop atTop)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hcenter : Tendsto
      (fun n => center (stableBlockLength α ν constant scale n) / scale n)
      atTop (nhds 0))
    {q : ℝ} (hq : 0 < q) (hq₁ : q < 1)
    (hmass : (μ.map (fun x : ℝ => constant ^ (1 / α) * x))
        (Set.Icc (-1 : ℝ) 1) < ENNReal.ofReal q)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      horizontalTubeProbability (iidSequenceLaw ν) a (scale n) n ≤
        ENNReal.ofReal q ^ (n / stableBlockLength α ν constant scale n) := by
  let block : ℕ → ℕ := stableBlockLength α ν constant scale
  let interval (n : ℕ) : Set ℝ :=
    Set.Icc ((-a) * scale n) ((1 - a) * scale n)
  let endpoint (n : ℕ) : ENNReal :=
    (iidSequenceLaw ν).map
      (fun increment => AdditivePath.displacement (block n) increment / scale n)
      (Set.Icc (-1 : ℝ) 1)

  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  have hscaleNe : ∀ᶠ n in atTop, scale n ≠ 0 :=
    hscalePos.mono fun _ h => h.ne'

  have htime : Tendsto (stableScaleTime α ν) atTop atTop :=
    _root_.ProbabilityTheory.stableScaleTime_tendsto_atTop_of_stableSlowVariation
      hα hα₂ hslow
  have hblockArgument : Tendsto
      (stableBlockArgument α ν constant scale) atTop atTop := by
    have hscaled := (htime.comp hscale).const_mul_atTop hconstant
    apply hscaled.congr'
    filter_upwards [] with n
    change constant * stableScaleTime α ν (scale n) =
      constant * scale n ^ α / stableSlowVariation α ν (scale n)
    rw [stableScaleTime]
    exact (mul_div_assoc _ _ _).symm
  have hblockTop : Tendsto block atTop atTop := by
    change Tendsto (Asymptotics.floorBlockLength
      (stableBlockArgument α ν constant scale)) atTop atTop
    exact Asymptotics.tendsto_floorBlockLength_atTop hblockArgument

  have hblockEq : block = Asymptotics.floorBlockLength
      (fun n => constant * stableScaleTime α ν (scale n)) := by
    funext n
    change ⌊stableBlockArgument α ν constant scale n⌋₊ =
      ⌊constant * stableScaleTime α ν (scale n)⌋₊
    congr 1
    change constant * scale n ^ α / stableSlowVariation α ν (scale n) =
      constant * stableScaleTime α ν (scale n)
    rw [stableScaleTime, mul_div_assoc]

  have hnormRatio : Tendsto
      (fun n => normalization (block n) / scale n) atTop
      (nhds (constant ^ (1 / α))) := by
    have hbase := hnorm.tendsto_floorBlock_normalization_div_scale
      hα hα₂ hslow hscale hconstant
    apply hbase.congr'
    filter_upwards [] with n
    simp only [hblockEq]

  have hendpointCLT : TendstoInDistribution
      (fun n increments => AdditivePath.displacement (block n) increments /
        scale n) atTop (fun x => constant ^ (1 / α) * x)
      (fun _ => iidSequenceLaw ν) μ := by
    have hsum := hDOA.tendstoInDistribution_partialSum_div
      block scale hblockTop hscaleNe hnormRatio hcenter
    simpa [block, AdditivePath.displacement] using hsum

  have hport : atTop.limsup endpoint ≤
      (μ.map (fun x : ℝ => constant ^ (1 / α) * x))
        (Set.Icc (-1 : ℝ) 1) := by
    simpa [endpoint] using
      hendpointCLT.limsup_measure_map_le_of_isClosed isClosed_Icc
  have hendpointBounded : Filter.IsBoundedUnder (· ≤ ·) atTop endpoint := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    apply Eventually.of_forall
    intro n
    have hmap : (iidSequenceLaw ν).map
        (fun increment => AdditivePath.displacement (block n) increment /
          scale n) Set.univ = 1 := by
      rw [Measure.map_apply
        ((displacement_measurable (block n)).div_const (scale n))
        MeasurableSet.univ]
      simp
    calc
      endpoint n ≤ (iidSequenceLaw ν).map
          (fun increment => AdditivePath.displacement (block n) increment /
            scale n) Set.univ := by
        dsimp [endpoint]
        exact measure_mono (Set.subset_univ _)
      _ = 1 := hmap
  have hendpointEventually : ∀ᶠ n in atTop,
      endpoint n < ENNReal.ofReal q :=
    eventually_lt_of_limsup_lt (hport.trans_lt hmass) hendpointBounded

  have hrowEventually : ∀ᶠ n in atTop,
      ∀ x : interval n,
        Kernel.remainingMass
          (killedIncrementKernelOn ν (interval n) measurableSet_Icc)
          (block n) x ≤ ENNReal.ofReal q := by
    filter_upwards [hendpointEventually, hscalePos,
      hblockTop.eventually (eventually_gt_atTop 0)] with n hendpoint hscaleN hblockN
    intro x
    rw [killedIncrementKernelOn_remainingMass_eq_iidSequenceLaw]
    have hsurvivalEndpoint :
        iidSequenceLaw ν
            {increment | StaysIn (interval n) (block n) (x : ℝ) increment} ≤
          endpoint n := by
      dsimp [endpoint]
      rw [Measure.map_apply
        ((displacement_measurable (block n)).div_const (scale n))
        measurableSet_Icc]
      unfold iidSequenceLaw
      apply measure_mono
      intro increment hstay
      have hclosed := (staysIn_Icc_iff_inClosedInterval
        ((-a) * scale n) ((1 - a) * scale n) (block n) (x : ℝ)
        x.property increment).mp hstay
      have hlast := hclosed ⟨block n, Nat.lt_succ_self (block n)⟩
      have hendpoint : (x : ℝ) + AdditivePath.displacement (block n) increment ∈
          Set.Icc ((-a) * scale n) ((1 - a) * scale n) := by
        simpa [InClosedInterval, InWindows, history_eq_fromIncrements,
          AdditivePath.fromIncrements] using hlast
      let normalizedStart : ℝ := (x : ℝ) / scale n
      have hnormalizedStart : normalizedStart ∈ Set.Icc (-a) (1 - a) := by
        constructor
        · apply (le_div_iff₀ hscaleN).2
          simpa [normalizedStart, mul_comm] using x.property.1
        · apply (div_le_iff₀ hscaleN).2
          simpa [normalizedStart, mul_comm] using x.property.2
      have hsumLower : -a - normalizedStart ≤
          AdditivePath.displacement (block n) increment / scale n := by
        have h := div_le_div_of_nonneg_right hendpoint.1 hscaleN.le
        have h' : -a ≤ normalizedStart +
            AdditivePath.displacement (block n) increment / scale n := by
          calc
            -a = ((-a) * scale n) / scale n := by
              field_simp [hscaleN.ne']
            _ ≤ ((x : ℝ) + AdditivePath.displacement (block n) increment) /
                scale n := h
            _ = normalizedStart +
                AdditivePath.displacement (block n) increment / scale n := by
              simp [normalizedStart, add_div]
        linarith
      have hsumUpper : AdditivePath.displacement (block n) increment / scale n ≤
          (1 - a) - normalizedStart := by
        have h := div_le_div_of_nonneg_right hendpoint.2 hscaleN.le
        have h' : normalizedStart +
            AdditivePath.displacement (block n) increment / scale n ≤ 1 - a := by
          calc
            normalizedStart +
                AdditivePath.displacement (block n) increment / scale n =
                ((x : ℝ) + AdditivePath.displacement (block n) increment) /
                  scale n := by
              simp [normalizedStart, add_div]
            _ ≤ ((1 - a) * scale n) / scale n := h
            _ = 1 - a := by
              field_simp [hscaleN.ne']
        linarith
      have hsum : AdditivePath.displacement (block n) increment / scale n ∈
          Set.Icc (-1) 1 := by
        constructor
        · have hstart := hnormalizedStart.2
          linarith
        · have hstart := hnormalizedStart.1
          linarith
      exact hsum
    exact hsurvivalEndpoint.trans (le_of_lt hendpoint)

  filter_upwards [hrowEventually, hscalePos] with n hrow hscaleN
  have hbound := Kernel.remainingMass_le_pow_div
    (killedIncrementKernelOn ν (interval n) measurableSet_Icc)
    (block n) n ⟨0, by
      constructor <;> nlinarith [hscaleN, ha₀, ha₁]⟩
    (ENNReal.ofReal q) (hrow)
  have hprobability :=
    remainingMass_killedIncrementKernelOn_Icc_eq_horizontalTubeProbability
      ν a (scale n) ha₀ ha₁ hscaleN.le n
  rw [← hprobability]
  exact hbound

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
