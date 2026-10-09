/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit.Block
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.PartitionEndpoint
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableRate
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableLower.PathLimit
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.EndpointBandTransfer.StableLower.EndpointMass

/-!
# Stable lower bounds for shifted endpoint-return blocks

This combines the stable escape rate, the variable-block path limit, and
open-set Portmanteau for an arbitrary shifted interval. It supplies the
finite endpoint-band probabilities needed by the discrete return kernel.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A single stable block amplitude gives discrete lower bounds for both the
seven same-core return windows and every member of a finite family of
different-core bridge windows. The returned block length is the canonical
rounded stable length at that amplitude. -/
theorem exists_eventually_commonReturnAndBridgeBlockMassLowerBound_of_stableEscapeRate
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
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hreturnWindows : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    {ι : Type*} [DecidableEq ι] (indices : Finset ι)
    (sourceCenter targetCenter : ι → ℝ)
    (hbridgeWindows : ∀ i ∈ indices,
      lower + 4 * epsilon < targetCenter i - sourceCenter i - 4 * epsilon ∧
        targetCenter i - sourceCenter i + 4 * epsilon < upper - 4 * epsilon) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        (∀ j ∈ Finset.Icc (-3 : ℤ) 3,
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ≤ iidSequenceLaw ν
            (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
              (epsilon * scale n) j
              (stableBlockLength α ν (amplitude ^ α) scale n))) ∧
        (∀ i ∈ indices, ∀ j ∈ Finset.Icc (-3 : ℤ) 3,
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ≤ iidSequenceLaw ν
            (endpointCorridorBridgeBlockEvent
              ((sourceCenter i + lower) * scale n)
              ((sourceCenter i + upper) * scale n) (epsilon * scale n)
              (sourceCenter i * scale n) (targetCenter i * scale n) j
              (stableBlockLength α ν (amplitude ^ α) scale n))) := by
  let bridgeIndices := indices.product (Finset.Icc (-3 : ℤ) 3)
  obtain ⟨amplitude, hamplitude, hreturnMass, hbridgeMass⟩ :=
    exists_commonStableEndpointBandAndBridgeMassLowerBound_of_escapeRate
      hEscape hX hcdf hlower hupper hepsilon hdelta hreturnWindows bridgeIndices
      (fun ij => targetCenter ij.1 - sourceCenter ij.1 +
        ((ij.2 : ℝ) - 1) * epsilon)
      (fun ij => targetCenter ij.1 - sourceCenter ij.1 +
        ((ij.2 : ℝ) + 1) * epsilon) (by
        intro ij hij
        rcases Finset.mem_product.mp hij with ⟨hi, hj⟩
        have hji : -3 ≤ (ij.2 : ℝ) ∧ (ij.2 : ℝ) ≤ 3 := by
          exact_mod_cast (Finset.mem_Icc.mp hj)
        have hwindowLower :
            targetCenter ij.1 - sourceCenter ij.1 - 4 * epsilon ≤
              targetCenter ij.1 - sourceCenter ij.1 +
                ((ij.2 : ℝ) - 1) * epsilon := by nlinarith [hji.1, hepsilon]
        have hwindowUpper :
            targetCenter ij.1 - sourceCenter ij.1 +
                ((ij.2 : ℝ) + 1) * epsilon ≤
              targetCenter ij.1 - sourceCenter ij.1 + 4 * epsilon := by
          nlinarith [hji.2, hepsilon]
        constructor
        · exact lt_of_lt_of_le (hbridgeWindows ij.1 hi).1 hwindowLower
        · refine ⟨?_, lt_of_le_of_lt hwindowUpper (hbridgeWindows ij.1 hi).2⟩
          nlinarith [hepsilon])
  let blockLength : ℕ → ℕ :=
    fun n => stableBlockLength α ν (amplitude ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hblockTop : Tendsto blockLength atTop atTop := by
    simpa [blockLength] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hblockRatio : Tendsto
      (fun n => (blockLength n : ℝ) / stableScaleTime α ν (scale n))
      atTop (nhds (amplitude ^ α)) := by
    simpa [blockLength] using
      tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
        hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  let lowerBound : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) * amplitude ^ α))
  have hreturnEventually :=
    eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase blockLength hblockTop
      hamplitude hblockRatio hlower hupper lowerBound hreturnMass
  have hbridgeEventually : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ indices, ∀ j ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ iidSequenceLaw ν
          (endpointCorridorBridgeBlockEvent
            ((sourceCenter i + lower) * scale n)
            ((sourceCenter i + upper) * scale n) (epsilon * scale n)
            (sourceCenter i * scale n) (targetCenter i * scale n) j
            (blockLength n)) := by
    apply indices.eventually_all.2
    intro i hi
    have hfamily :=
      eventually_endpointCorridorBlockProbabilityFamily_ge_of_stableScaleTimeRatio
        hscale hα hα₂ hslow hEscape hDOA htightBase blockLength hblockTop
        hamplitude hblockRatio (Finset.Icc (-3 : ℤ) 3)
        (fun _ => lower + 4 * epsilon) (fun _ => upper - 4 * epsilon)
        (fun j => targetCenter i - sourceCenter i + ((j : ℝ) - 1) * epsilon)
        (fun j => targetCenter i - sourceCenter i + ((j : ℝ) + 1) * epsilon)
        (by intro j hj; exact hlower) (by intro j hj; exact hupper)
        lowerBound (by
          intro j hj
          exact hbridgeMass (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩))
    filter_upwards [hfamily] with n hfamilyN
    intro j hj
    have hprob := hfamilyN j hj
    have hset : endpointCorridorBlockEvent
        ((lower + 4 * epsilon) * scale n)
        ((upper - 4 * epsilon) * scale n)
        ((targetCenter i - sourceCenter i + ((j : ℝ) - 1) * epsilon) * scale n)
        ((targetCenter i - sourceCenter i + ((j : ℝ) + 1) * epsilon) * scale n)
        (blockLength n) =
      endpointCorridorBridgeBlockEvent
        ((sourceCenter i + lower) * scale n)
        ((sourceCenter i + upper) * scale n) (epsilon * scale n)
        (sourceCenter i * scale n) (targetCenter i * scale n) j
        (blockLength n) := by
      rw [endpointCorridorBridgeBlockEvent_scale]
      congr 1 <;> ring
    rw [← hset]
    exact hprob
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hreturnEventually, hbridgeEventually] with n hreturnN hbridgeN
  constructor
  · simpa [lowerBound, blockLength] using hreturnN
  · simpa [lowerBound, blockLength] using hbridgeN

/-- A macroscopic corridor cell has a sharp lower probability bound while
connecting two different endpoint cores. The cell horizon reserves one
stable-scale block for the outgoing bridge; the remaining steps are split
into an exact balanced list of same-core returns. -/
theorem exists_eventually_endpointCoreCellBridgeLowerBound_of_stableEscapeRate
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
    {lower upper epsilon delta duration : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hreturnWindows : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    (sourceCenter targetCenter : ℝ)
    (hbridgeWindows :
      lower + 4 * epsilon < targetCenter - sourceCenter - 4 * epsilon ∧
        targetCenter - sourceCenter + 4 * epsilon < upper - 4 * epsilon)
    (total : ℕ → ℕ) (hduration : 0 < duration)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ x : Set.Icc
            (sourceCenter * scale n - 3 * (epsilon * scale n))
            (sourceCenter * scale n + 3 * (epsilon * scale n)),
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ^
                (Asymptotics.balancedBlockCount
                  (total n - stableBlockLength α ν (amplitude ^ α) scale n)
                  (stableBlockLength α ν (amplitude ^ α) scale n) + 1) ≤
            iidSequenceLaw ν
              {increment | RandomWalk.StaysIn
                  (Set.Icc ((sourceCenter + lower) * scale n)
                    ((sourceCenter + upper) * scale n))
                  (total n) (x : ℝ) increment ∧
                (x : ℝ) + AdditivePath.displacement (total n) increment ∈
                  Set.Icc (targetCenter * scale n - 3 * (epsilon * scale n))
                    (targetCenter * scale n + 3 * (epsilon * scale n))} := by
  let bands : Finset ℤ := Finset.Icc (-3 : ℤ) 3
  have hbridgeFamily : ∀ i ∈ bands,
      lower + 4 * epsilon < targetCenter - sourceCenter +
          ((i : ℝ) - 1) * epsilon ∧
        targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon <
          targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon ∧
        targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon <
          upper - 4 * epsilon := by
    intro i hi
    have hi' : -3 ≤ (i : ℝ) ∧ (i : ℝ) ≤ 3 := by
      exact_mod_cast (Finset.mem_Icc.mp hi)
    have hleft : targetCenter - sourceCenter - 4 * epsilon ≤
        targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon := by
      nlinarith [hi'.1, hepsilon]
    have hright : targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon ≤
        targetCenter - sourceCenter + 4 * epsilon := by
      nlinarith [hi'.2, hepsilon]
    exact ⟨lt_of_lt_of_le hbridgeWindows.1 hleft,
      by nlinarith [hepsilon], lt_of_le_of_lt hright hbridgeWindows.2⟩
  obtain ⟨amplitude, hamplitude, hreturnMass, hbridgeMass⟩ :=
    exists_commonStableEndpointBandAndBridgeMassLowerBound_of_escapeRate
      hEscape hX hcdf hlower hupper hepsilon hdelta hreturnWindows bands
      (fun i => targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon)
      (fun i => targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon)
      hbridgeFamily
  let reference : ℕ → ℕ :=
    fun n => stableBlockLength α ν (amplitude ^ α) scale n
  let mainLength : ℕ → ℕ := fun n => total n - reference n
  let returnLengths : ℕ → List ℕ := fun n =>
    Asymptotics.balancedBlockLengths (mainLength n) (reference n)
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hrateZero : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0) :=
    tendsto_stableSmallDeviationRate_zero_of_slowVariation
      hscale.stableNorming hscaleTop hscale.scale_div_normalization_tendsto_zero
      hα hα₂ hslow
  have hreferenceTop : Tendsto reference atTop atTop := by
    simpa [reference] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hreferencePositive : ∀ᶠ n : ℕ in atTop, 0 < reference n :=
    hreferenceTop.eventually (eventually_gt_atTop 0)
  have hreferenceRatioZero : Tendsto
      (fun n => (reference n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    simpa [reference] using tendsto_stableBlockLength_div_nat_zero_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop hrateZero
  have hmainDuration : Tendsto
      (fun n => (mainLength n : ℝ) / (n : ℝ)) atTop (nhds duration) := by
    simpa [mainLength] using
      Asymptotics.tendsto_nat_sub_div_nat_of_horizon_and_vanishingBlock
        htotal hreferenceRatioZero hduration
  have hreferenceLe : ∀ᶠ n : ℕ in atTop, reference n ≤ total n :=
    Asymptotics.eventually_block_le_horizon_of_positive_density
      htotal hreferenceRatioZero hduration
  have hbalanced := balancedStableCellBlock_asymptotics hscale hα hα₂ hslow
    mainLength hduration hamplitude hmainDuration
  rcases hbalanced with
    ⟨hcount, hshortTop, hlongTop, hshortRatio, hlongRatio⟩
  have hshortProbability :=
    eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase
      (fun n => Asymptotics.balancedBlockShortLength
        (mainLength n) (reference n)) hshortTop hamplitude hshortRatio
      hlower hupper
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
          amplitude ^ α))) hreturnMass
  have hlongProbability :=
    eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase
      (fun n => Asymptotics.balancedBlockShortLength
        (mainLength n) (reference n) + 1) hlongTop hamplitude hlongRatio
      hlower hupper
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
          amplitude ^ α))) hreturnMass
  have hreferenceRatio : Tendsto
      (fun n => (reference n : ℝ) / stableScaleTime α ν (scale n))
      atTop (nhds (amplitude ^ α)) := by
    simpa [reference] using tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hbridgeProbability :=
    eventually_endpointCorridorBlockProbabilityFamily_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase reference hreferenceTop
      hamplitude hreferenceRatio bands (fun _ => lower + 4 * epsilon)
      (fun _ => upper - 4 * epsilon)
      (fun i => targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon)
      (fun i => targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon)
      (by intro i hi; exact hlower) (by intro i hi; exact hupper)
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
          amplitude ^ α))) hbridgeMass
  have hscalePositive : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hcountPositive : ∀ᶠ n : ℕ in atTop,
      0 < Asymptotics.balancedBlockCount (mainLength n) (reference n) := by
    filter_upwards [hcount.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    exact_mod_cast hn
  have hreturnCount : ∀ᶠ n : ℕ in atTop,
      (returnLengths n).length =
        Asymptotics.balancedBlockCount (mainLength n) (reference n) := by
    filter_upwards [hcountPositive] with n hn
    simpa [returnLengths] using
      Asymptotics.balancedBlockLengths_length hn
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hshortProbability, hlongProbability, hbridgeProbability,
    hscalePositive, hreferenceLe, hcountPositive, hreturnCount]
    with n hshortN hlongN hbridgeN hscaleN hrefLe hcountN hlengthN
  let allowedLower : ℝ := (sourceCenter + lower) * scale n
  let allowedUpper : ℝ := (sourceCenter + upper) * scale n
  let source : ℝ := sourceCenter * scale n
  let target : ℝ := targetCenter * scale n
  let epsilonN : ℝ := epsilon * scale n
  have hepsilonN : 0 < epsilonN := mul_pos hepsilon hscaleN
  have hreturnEvents : ∀ length ∈ returnLengths n, ∀ i ∈ bands,
      ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) ≤ iidSequenceLaw ν
        (endpointBandReturnBlockEvent (allowedLower - source)
          (allowedUpper - source) epsilonN i length) := by
    intro length hlength i hi
    have hlength' : length ∈
        Asymptotics.balancedBlockLengths (mainLength n) (reference n) := by
      simpa [returnLengths] using hlength
    rcases Asymptotics.mem_balancedBlockLengths hlength' with hshort | hlong
    · have hlow : allowedLower - source = lower * scale n := by
        dsimp [allowedLower, source]
        ring
      have hupp : allowedUpper - source = upper * scale n := by
        dsimp [allowedUpper, source]
        ring
      rw [hlow, hupp, hshort]
      exact hshortN i hi
    · have hlow : allowedLower - source = lower * scale n := by
        dsimp [allowedLower, source]
        ring
      have hupp : allowedUpper - source = upper * scale n := by
        dsimp [allowedUpper, source]
        ring
      rw [hlow, hupp, hlong]
      exact hlongN i hi
  have hbridgeEvents : ∀ i ∈ bands,
      ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) ≤ iidSequenceLaw ν
        (endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilonN
          source target i (reference n)) := by
    intro i hi
    have hprob := hbridgeN i hi
    have hset : endpointCorridorBlockEvent
        ((lower + 4 * epsilon) * scale n)
        ((upper - 4 * epsilon) * scale n)
        ((targetCenter - sourceCenter + ((i : ℝ) - 1) * epsilon) * scale n)
        ((targetCenter - sourceCenter + ((i : ℝ) + 1) * epsilon) * scale n)
        (reference n) =
      endpointCorridorBridgeBlockEvent allowedLower allowedUpper epsilonN
        source target i (reference n) := by
      rw [endpointCorridorBridgeBlockEvent_scale]
      congr 1 <;> ring
    rw [← hset]
    exact hprob
  have hcell :=
    iidSequenceLaw_staysIn_endsIn_ge_of_endpointCorridorBridgeEvents
      ν hepsilonN (returnLengths n) (reference n)
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
          amplitude ^ α))) hreturnEvents hbridgeEvents
  have hreturnSum :
      ProbabilityTheory.Kernel.returnKernelSequenceLength (returnLengths n) =
        mainLength n := by
    rw [ProbabilityTheory.Kernel.returnKernelSequenceLength_eq_sum]
    simpa [returnLengths] using
      Asymptotics.balancedBlockLengths_sum hcountN
  have htotalExact :
      ProbabilityTheory.Kernel.returnKernelSequenceLength (returnLengths n) +
          reference n = total n := by
    rw [hreturnSum]
    exact Nat.sub_add_cancel hrefLe
  let p : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
      amplitude ^ α))
  rw [htotalExact] at hcell
  intro x
  have hgoal : p ^
      (Asymptotics.balancedBlockCount (mainLength n) (reference n) + 1) ≤
        iidSequenceLaw ν
          {increment | RandomWalk.StaysIn (Set.Icc allowedLower allowedUpper)
              (total n) (x : ℝ) increment ∧
            (x : ℝ) + AdditivePath.displacement (total n) increment ∈
              Set.Icc (target - 3 * epsilonN) (target + 3 * epsilonN)} := by
    rw [← hlengthN, pow_succ]
    exact hcell x
  simpa [p, allowedLower, allowedUpper, source, target, epsilonN,
    reference, mainLength] using hgoal

/-- Stable escape and block convergence give the required lower bound for a
single robust endpoint-core event. The spatial margin makes the killed path
event a subset of the open block corridor; the smaller terminal window lies
inside the prescribed increase of endpoint-core radius. -/
theorem exists_eventually_partitionCellCoreReturnBlockEvent_ge_exp_of_stableEscapeRate
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
    {innerLower innerUpper startCenter startRadius endCenter endRadius : ℝ}
    {lower upper epsilon margin delta duration : ℝ}
    (hlower : lower = innerLower + startRadius + margin - startCenter)
    (hupper : upper = innerUpper - startRadius - margin - startCenter)
    (hmargin : 0 < margin)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hendpointBand : 3 * epsilon < (endRadius - startRadius) / 2)
    (hreturnWindows : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    (hbridgeWindows :
      lower + 4 * epsilon < endCenter - startCenter - 4 * epsilon ∧
        endCenter - startCenter + 4 * epsilon < upper - 4 * epsilon)
    (total : ℕ → ℕ) (hduration : 0 < duration)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ENNReal.ofReal (Real.exp
          ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
            amplitude ^ α)) ^
              (Asymptotics.balancedBlockCount
                (total n - stableBlockLength α ν (amplitude ^ α) scale n)
                (stableBlockLength α ν (amplitude ^ α) scale n) + 1) ≤
          iidSequenceLaw ν
            {increment : ℕ → ℝ |
              ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete.partitionCellCoreReturnBlockEvent
                  (scale n * innerLower) (scale n * innerUpper)
                  (scale n * startCenter) (scale n * startRadius)
                  (scale n * endCenter) (scale n * endRadius)
                  (Combinatorics.Sequence.blockCoordinates 0 (total n) increment)} := by
  have hreturnLower := hreturnWindows (-3) (by norm_num)
  have hreturnUpper := hreturnWindows 3 (by norm_num)
  have hlower' : lower + 4 * epsilon < 0 := by
    have hi : ((-3 : ℤ) : ℝ) - 1 = -4 := by norm_num
    rw [hi] at hreturnLower
    nlinarith [hreturnLower.1, hepsilon]
  have hupper' : 0 < upper - 4 * epsilon := by
    have hi : ((3 : ℤ) : ℝ) + 1 = 4 := by norm_num
    rw [hi] at hreturnUpper
    nlinarith [hreturnUpper.2, hepsilon]
  obtain ⟨amplitude, hamplitude, hcellEventually⟩ :=
    exists_eventually_endpointCoreCellBridgeLowerBound_of_stableEscapeRate
      hscale hα hα₂ hslow hEscape hX hcdf hDOA htightBase
      hlower' hupper' hepsilon hdelta hreturnWindows startCenter endCenter
      hbridgeWindows total hduration htotal
  have hscalePositive : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hcellEventually, hscalePositive] with n hcellN hscaleN
  have hx : startCenter * scale n ∈
      Set.Icc (startCenter * scale n - 3 * (epsilon * scale n))
        (startCenter * scale n + 3 * (epsilon * scale n)) := by
    constructor <;> nlinarith [mul_pos (by positivity : 0 < 3 * epsilon) hscaleN]
  have hcell := hcellN ⟨startCenter * scale n, hx⟩
  have hzeroLower : innerLower + startRadius - startCenter < 0 := by
    rw [hlower] at hlower'
    nlinarith [hlower', hmargin]
  have hzeroUpper : 0 < innerUpper - startRadius - startCenter := by
    rw [hupper] at hupper'
    nlinarith [hupper', hmargin]
  have hsubset :
      {increment : ℕ → ℝ |
        RandomWalk.StaysIn
            (Set.Icc ((startCenter + lower) * scale n)
              ((startCenter + upper) * scale n))
            (total n) (startCenter * scale n) increment ∧
          startCenter * scale n + AdditivePath.displacement (total n) increment ∈
            Set.Icc (endCenter * scale n - 3 * (epsilon * scale n))
              (endCenter * scale n + 3 * (epsilon * scale n))} ⊆
      {increment : ℕ → ℝ |
        ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete.partitionCellCoreReturnBlockEvent
            (scale n * innerLower) (scale n * innerUpper)
            (scale n * startCenter) (scale n * startRadius)
            (scale n * endCenter) (scale n * endRadius)
            (Combinatorics.Sequence.blockCoordinates 0 (total n) increment)} := by
    intro increment hevent
    have hpath : RandomWalk.StaysIn
        (Set.Icc (scale n * (innerLower + startRadius + margin))
          (scale n * (innerUpper - startRadius - margin)))
        (total n) (scale n * startCenter) increment := by
      have hlow : (startCenter + lower) * scale n =
          scale n * (innerLower + startRadius + margin) := by
        rw [hlower]
        ring
      have hupp : (startCenter + upper) * scale n =
          scale n * (innerUpper - startRadius - margin) := by
        rw [hupper]
        ring
      rw [← hlow, ← hupp]
      convert hevent.1 using 1
      ring_nf
    have hend : scale n * startCenter +
        AdditivePath.displacement (total n) increment ∈
          Set.Icc (scale n * (endCenter - 3 * epsilon))
            (scale n * (endCenter + 3 * epsilon)) := by
      convert hevent.2 using 1 <;> ring_nf
    exact ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Discrete.partitionCellCoreReturnBlockEvent_of_staysIn_endsIn
        hscaleN hmargin hzeroLower hzeroUpper hendpointBand hpath hend
  calc
    _ ≤ iidSequenceLaw ν
        {increment : ℕ → ℝ |
          RandomWalk.StaysIn
              (Set.Icc ((startCenter + lower) * scale n)
                ((startCenter + upper) * scale n))
              (total n) (startCenter * scale n) increment ∧
            startCenter * scale n + AdditivePath.displacement (total n) increment ∈
              Set.Icc (endCenter * scale n - 3 * (epsilon * scale n))
                (endCenter * scale n + 3 * (epsilon * scale n))} := hcell
    _ ≤ _ := measure_mono hsubset

/-- The stable escape rate and block functional limit give a sharp lower
bound for a whole floor-rounded partition cell. The cell is split into
balanced adjacent block lengths, so the return-kernel iteration covers every
increment and has no terminal remainder. -/
theorem exists_eventually_balancedEndpointBandSurvival_ge_exp_of_stableEscapeRate
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
    {lower upper epsilon delta duration : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon)
    (total : ℕ → ℕ) (hduration : 0 < duration)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ x : Set.Icc (-3 * (epsilon * scale n)) (3 * (epsilon * scale n)),
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ^
                Asymptotics.balancedBlockCount (total n)
                  (stableBlockLength α ν (amplitude ^ α) scale n)
            ≤ iidSequenceLaw ν
              {increment | StaysIn
                (Set.Icc (lower * scale n) (upper * scale n))
                (total n) (x : ℝ) increment} := by
  obtain ⟨amplitude, hamplitude, hmass⟩ :=
    exists_stableEndpointBandReturnMassLowerBound_of_escapeRate
      hEscape hX hcdf hlower hupper hepsilon hdelta hbands
  let reference : ℕ → ℕ := fun n => stableBlockLength α ν (amplitude ^ α) scale n
  let shortBlock : ℕ → ℕ := fun n =>
    Asymptotics.balancedBlockShortLength (total n) (reference n)
  let longBlock : ℕ → ℕ := fun n => shortBlock n + 1
  have hdata := balancedStableCellBlock_asymptotics hscale hα hα₂ hslow
    total hduration hamplitude htotal
  rcases hdata with ⟨hcount, hshortTop, hlongTop, hshortRatio, hlongRatio⟩
  have hshortProbability :=
    eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase shortBlock hshortTop
      hamplitude hshortRatio hlower hupper
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) * amplitude ^ α)))
      (by
        intro i hi
        exact hmass i hi)
  have hlongProbability :=
    eventually_endpointBandReturnBlockProbability_ge_of_stableScaleTimeRatio
      hscale hα hα₂ hslow hEscape hDOA htightBase longBlock hlongTop
      hamplitude hlongRatio hlower hupper
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) * amplitude ^ α)))
      (by
        intro i hi
        exact hmass i hi)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hcountPos : ∀ᶠ n : ℕ in atTop,
      0 < Asymptotics.balancedBlockCount (total n) (reference n) := by
    filter_upwards [hcount.eventually (eventually_gt_atTop (0 : ℝ))] with n hn
    exact_mod_cast hn
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hshortProbability, hlongProbability, hscalePos, hcountPos]
    with n hshortN hlongN hscaleN hcountN
  intro x
  have hcell :=
    ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.iidSequenceLaw_staysIn_ge_pow_of_balancedEndpointBandBlocks
      ν (mul_pos hepsilon hscaleN) (total n) (reference n) hcountN
      (ENNReal.ofReal (Real.exp
        ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) * amplitude ^ α)))
      (by
        intro i hi
        simpa [shortBlock, reference] using hshortN i hi)
      (by
        intro i hi
        simpa [longBlock, shortBlock, reference] using hlongN i hi)
  simpa [Asymptotics.balancedBlockCount, reference] using hcell x

/-- For any fixed shifted corridor and a finite family of endpoint bands
strictly inside it, stable escape rates and the variable-block functional
limit give the sharp exponential lower bound for every one-block endpoint
event. The block amplitude is chosen large enough once and then kept fixed
while the walk horizon tends to infinity. -/
theorem exists_eventually_endpointBandReturnBlockProbability_ge_exp_of_stableEscapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    {lower upper epsilon delta : ℝ}
    (hlower : lower + 4 * epsilon < 0)
    (hupper : 0 < upper - 4 * epsilon)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta)
    (hbands : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lower + 4 * epsilon < (((i : ℝ) - 1) * epsilon) ∧
        ((i : ℝ) + 1) * epsilon < upper - 4 * epsilon) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
          ENNReal.ofReal (Real.exp
            ((C / (((upper - lower - 8 * epsilon) / 2) ^ α) - delta) *
              amplitude ^ α)) ≤
            iidSequenceLaw ν
              (endpointBandReturnBlockEvent (lower * scale n) (upper * scale n)
                (epsilon * scale n) i
                (stableBlockLength α ν (amplitude ^ α) scale n)) := by
  let corridorLower : ℝ := lower + 4 * epsilon
  let corridorUpper : ℝ := upper - 4 * epsilon
  let radius : ℝ := (corridorUpper - corridorLower) / 2
  have hradiusEq : radius = (upper - lower - 8 * epsilon) / 2 := by
    dsimp [radius, corridorLower, corridorUpper]
    ring
  have hradius : 0 < radius := by
    dsimp [radius, corridorLower, corridorUpper]
    linarith [hlower, hupper]
  obtain ⟨amplitude, hamplitude, hstableMass⟩ :=
    exists_stableEndpointBandReturnMassLowerBound_of_escapeRate
      hEscape hX hcdf hlower hupper hepsilon hdelta hbands
  have hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ENNReal.ofReal (Real.exp
        ((C / radius ^ α - delta) * amplitude ^ α)) <
        P.map (Skorokhod.scalePath amplitude)
          (Skorokhod.rangeInOpenIntervalEndsIn corridorLower corridorUpper
            (((i : ℝ) - 1) * epsilon) (((i : ℝ) + 1) * epsilon)) := by
    intro i hi
    simpa [corridorLower, corridorUpper, radius, hradiusEq] using hstableMass i hi
  let blockLength : ℕ → ℕ := fun n =>
    stableBlockLength α ν (amplitude ^ α) scale n
  have hscaleTop : Tendsto scale atTop atTop :=
    IsStableMogulskiiScale.scale_tendsto_atTop hscale
  have hblockTop : Tendsto blockLength atTop atTop := by
    simpa [blockLength] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hblockPos : ∀ᶠ n : ℕ in atTop, 0 < blockLength n :=
    hblockTop.eventually (eventually_gt_atTop 0)
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    IsStableMogulskiiScale.eventually_scale_pos hscale
  have hnormBlockPos : ∀ᶠ n : ℕ in atTop,
      0 < normalization (blockLength n) :=
    (hscale.stableNorming.2.1.comp hblockTop).eventually
      (eventually_gt_atTop 0)
  have hblockEq : blockLength = Asymptotics.floorBlockLength
      (fun n => amplitude ^ α * stableScaleTime α ν (scale n)) := by
    funext n
    change ⌊stableBlockArgument α ν (amplitude ^ α) scale n⌋₊ =
      ⌊amplitude ^ α * stableScaleTime α ν (scale n)⌋₊
    rw [stableBlockArgument_eq_constant_mul_stableScaleTime]
  have hnormRatioBase := hscale.stableNorming.tendsto_floorBlock_normalization_div_scale
    hα hα₂ hslow hscaleTop (Real.rpow_pos_of_pos hamplitude α)
  have hnormRatio : Tendsto
      (fun n => normalization (blockLength n) / scale n)
      atTop (𝓝 amplitude) := by
    have hbase : Tendsto
        (fun n => normalization (blockLength n) / scale n)
        atTop (𝓝 ((amplitude ^ α) ^ (1 / α))) := by
      apply hnormRatioBase.congr'
      filter_upwards [] with n
      simp [blockLength, hblockEq]
    have hroot : (amplitude ^ α) ^ (1 / α) = amplitude := by
      rw [← Real.rpow_mul (le_of_lt hamplitude) α (1 / α)]
      have hmul : α * (1 / α) = 1 := by field_simp [ne_of_gt hα]
      rw [hmul, Real.rpow_one]
    convert hbase using 1
    exact congrArg nhds hroot.symm
  have hlimit :=
    RandomWalk.FunctionalLimit.Stable.tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
      hDOA hEscape.isStableClockProcessLaw htightBase hblockTop
      hscalePos hnormBlockPos hnormRatio
  have hscaleMapMeas : Measurable (Skorokhod.scalePath amplitude) :=
    (Skorokhod.continuous_scalePath.comp
      (continuous_const.prodMk continuous_id)).measurable
  have hlimit' := hlimit.congr_limit (μ'' := P)
    (Z' := Skorokhod.scalePath amplitude) hscaleMapMeas.aemeasurable (by simp)
  have hdiscrete :=
    eventually_endpointBandReturnBlockProbability_ge_of_stablePathLimit
      ν scale blockLength (Z := Skorokhod.scalePath amplitude) hlimit'
      hscalePos hblockPos hlower hupper
      (ENNReal.ofReal (Real.exp ((C / radius ^ α - delta) * amplitude ^ α))) hbelow
  refine ⟨amplitude, hamplitude, ?_⟩
  filter_upwards [hdiscrete] with n hdiscreteN
  simpa [blockLength, hradiusEq] using hdiscreteN

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
