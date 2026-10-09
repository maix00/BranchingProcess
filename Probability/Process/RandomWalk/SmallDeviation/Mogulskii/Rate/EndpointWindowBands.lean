/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.SpectralEndpointBands
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Horizontal lower rate from endpoint-window block bounds

This is the logarithmic scale-transfer step for the narrow endpoint windows
used by the `α = 2` spectral argument. The block probability estimate and the
asymptotic block-count ratio are explicit hypotheses; this file only composes
the return kernel and passes to the Mogulskii normalization.
-/

open Filter MeasureTheory Set Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- A uniform seven-window block lower bound yields the corresponding
horizontal-tube logarithmic lower rate. The outer tube must contain the
return corridor after rescaling a diffusive block. -/
theorem one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_endpointWindowBlocks
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {radius spacing windowRadius : ℕ → ℝ} {constant : ℝ}
    (blockLength : ℕ → ℕ)
    (hblockLengthPos : ∀ᶠ n in atTop, 0 < blockLength n)
    (hcountLimit : Tendsto
      (fun n => ((n / blockLength n + 1 : ℕ) : ℝ) *
        scale n ^ 2 / (n : ℝ)) atTop (nhds (1 / constant)))
    (hspacing : ∀ᶠ n in atTop, 0 < spacing n)
    (hwindow : ∀ᶠ n in atTop, 0 < windowRadius n)
    (hwindowLe : ∀ᶠ n in atTop, windowRadius n ≤ 2 * spacing n)
    (_hconstant : 0 < constant)
    (hfit : ∀ᶠ n in atTop,
      2 * (radius n + 3 * spacing n + windowRadius n) *
        Real.sqrt (blockLength n) ≤ scale n)
    (lowerBound : ENNReal) (hlowerBound : 0 < lowerBound)
    (hlowerBoundOne : lowerBound ≤ 1)
    (hblock : ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ normalizedEndpointWindowProbabilityAlong ν
        radius spacing windowRadius i
        (fun n => Real.sqrt (blockLength n)) blockLength n) :
    ((1 / constant) * Real.log lowerBound.toReal ≤
      atTop.liminf (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) ∧
      (∀ᶠ n in atTop, 0 < horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n) ∧
      Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) := by
  let length : ℕ → ℕ := blockLength
  let count : ℕ → ℕ := fun n => n / length n + 1
  let probability : ℕ → ENNReal := fun n => horizontalTubeProbability
    (iidSequenceLaw ν) (1 / 2) (scale n) n
  let ratio : ℕ → ℝ := fun n => scale n ^ 2 / (n : ℝ)
  let coefficient : ℕ → ℝ := fun n => (count n : ℝ) * ratio n

  have hlengthPos : ∀ᶠ n in atTop, 0 < length n := by simpa [length] using hblockLengthPos
  have hcoefficientLimit : Tendsto coefficient atTop (nhds (1 / constant)) := by
    convert hcountLimit using 1
    · simp only [coefficient, count, ratio, length]
      funext n
      push_cast
      ring

  have hpower : ∀ᶠ n in atTop,
      lowerBound ^ count n ≤ probability n := by
    filter_upwards [hblock, hfit, hspacing, hwindow, hwindowLe, hlengthPos,
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale]
      with n hbands hfitN hspacingN hwindowN hwindowLeN hlengthN hscaleN
    have hcover : n ≤ count n * length n := by
      have hdiv := Nat.lt_mul_div_succ n hlengthN
      dsimp [count]
      simpa [Nat.mul_comm] using hdiv.le
    have hsqrt : 0 < Real.sqrt (length n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hlengthN)
    have hbandsMapped : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ iidSequenceLaw (ν.map fun x : ℝ => x / Real.sqrt (length n))
          (endpointWindowBlockEvent (radius n) (spacing n) (windowRadius n) i (length n)) := by
      intro i hi
      rw [iidSequenceLaw_map_div_endpointWindowBlockEvent_eq_normalizedAlong
        ν radius spacing windowRadius i
        (fun k => Real.sqrt (length k))
        length n hsqrt]
      simpa [length] using hbands i hi
    have hprefix := horizontalTubeProbability_ge_pow_endpointWindows
      (ν.map fun x : ℝ => x / Real.sqrt (length n)) hspacingN hwindowN hwindowLeN
      (count n) (length n) lowerBound hbandsMapped
    have hprefixHorizon := hprefix.trans
      (horizontalTubeProbability_mono_horizon
      (iidSequenceLaw (ν.map fun x : ℝ => x / Real.sqrt (length n)))
        (1 / 2) (2 * (radius n + 3 * spacing n + windowRadius n)) hcover)
    have hmap := horizontalTubeProbability_map_div ν (1 / 2 : ℝ)
      (2 * (radius n + 3 * spacing n + windowRadius n) * Real.sqrt (length n))
      n hsqrt
    have hmapWidth :
        (2 * (radius n + 3 * spacing n + windowRadius n) * Real.sqrt (length n)) /
            Real.sqrt (length n) = 2 * (radius n + 3 * spacing n + windowRadius n) := by
      field_simp [hsqrt.ne']
    rw [hmapWidth] at hmap
    have houter : lowerBound ^ count n ≤
        horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
          (2 * (radius n + 3 * spacing n + windowRadius n) * Real.sqrt (length n)) n :=
      hprefixHorizon.trans_eq hmap
    have hwide := horizontalTubeProbability_mono_width
      (iidSequenceLaw ν) (a := (1 / 2 : ℝ))
      (width₁ := 2 * (radius n + 3 * spacing n + windowRadius n) * Real.sqrt (length n))
      (width₂ := scale n) (n := n) (by norm_num) (by norm_num) hfitN
    exact houter.trans hwide

  have hpositive : ∀ᶠ n in atTop, 0 < probability n := by
    filter_upwards [hpower] with n hn
    have hpow : 0 < lowerBound ^ count n := by positivity
    exact lt_of_lt_of_le hpow hn

  have hlogPointwise : ∀ᶠ n in atTop,
      coefficient n * Real.log lowerBound.toReal ≤
        ratio n * Real.log (probability n).toReal := by
    filter_upwards [hpower, hlengthPos,
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale,
      eventually_gt_atTop 0] with n hprob hlen hscaleN hn
    have hprobOne : probability n ≤ 1 := by
      calc
        probability n ≤ iidSequenceLaw ν Set.univ := by
          dsimp [probability]
          exact measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ⊤ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have hlowerBoundTop : lowerBound ≠ ⊤ :=
      ne_of_lt (hlowerBoundOne.trans_lt ENNReal.one_lt_top)
    have hpowTop : lowerBound ^ count n ≠ ⊤ :=
      ENNReal.pow_ne_top hlowerBoundTop
    have hprobReal : (lowerBound ^ count n).toReal ≤
        (probability n).toReal :=
      (ENNReal.toReal_le_toReal hpowTop hprobTop).2 hprob
    have hlowerBoundReal : 0 < lowerBound.toReal :=
      ENNReal.toReal_pos hlowerBound.ne' hlowerBoundTop
    have hlog := Real.log_le_log
      (by simpa [ENNReal.toReal_pow] using pow_pos hlowerBoundReal (count n)) hprobReal
    rw [ENNReal.toReal_pow, Real.log_pow] at hlog
    have hratioNonneg : 0 ≤ ratio n := by
      dsimp [ratio]
      positivity
    calc
      coefficient n * Real.log lowerBound.toReal =
          ratio n * ((count n : ℝ) * Real.log lowerBound.toReal) := by
        dsimp [coefficient]
        ring
      _ ≤ ratio n * Real.log (probability n).toReal :=
        mul_le_mul_of_nonneg_left hlog hratioNonneg

  have hleft : Tendsto
      (fun n => coefficient n * Real.log lowerBound.toReal) atTop
      (nhds ((1 / constant) * Real.log lowerBound.toReal)) :=
    hcoefficientLimit.mul_const _

  have hboundedBelow : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n => ratio n * Real.log (probability n).toReal) := by
    have heventually : ∀ᶠ n in atTop,
        ((1 / constant) * Real.log lowerBound.toReal - 1) <
          coefficient n * Real.log lowerBound.toReal :=
      hleft.eventually (Ioi_mem_nhds (by linarith))
    have hpointwiseLower : ∀ᶠ n in atTop,
        (1 / constant) * Real.log lowerBound.toReal - 1 ≤
          ratio n * Real.log (probability n).toReal := by
      filter_upwards [heventually, hlogPointwise] with n hleftN hrightN
      exact hleftN.le.trans hrightN
    exact Filter.isBoundedUnder_of_eventually_ge hpointwiseLower

  have hrightUpper : ∀ᶠ n in atTop,
      ratio n * Real.log (probability n).toReal ≤ 0 := by
    filter_upwards [
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.eventually_pos hscale,
      eventually_gt_atTop 0] with n hs hn
    have hprobOne : probability n ≤ 1 := by
      calc
        probability n ≤ iidSequenceLaw ν Set.univ := by
          dsimp [probability]
          exact measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ⊤ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have htoRealOne : (probability n).toReal ≤ 1 :=
      (ENNReal.toReal_le_toReal hprobTop ENNReal.one_ne_top).2 hprobOne
    have hlogNonpos : Real.log (probability n).toReal ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg htoRealOne
    have hratioNonneg : 0 ≤ ratio n := by
      dsimp [ratio]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hratioNonneg hlogNonpos

  have hrate : (1 / constant) * Real.log lowerBound.toReal ≤
      atTop.liminf (fun n => ratio n * Real.log (probability n).toReal) := by
   calc
    (1 / constant) * Real.log lowerBound.toReal =
        atTop.liminf (fun n => coefficient n * Real.log lowerBound.toReal) :=
      hleft.liminf_eq.symm
    _ ≤ atTop.liminf (fun n => ratio n * Real.log (probability n).toReal) :=
      Filter.liminf_le_liminf hlogPointwise hleft.isBoundedUnder_ge
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop hrightUpper)
    _ = _ := rfl
  exact ⟨by simpa [ratio, probability] using hrate,
    by simpa [probability] using hpositive,
    by simpa [ratio, probability] using hboundedBelow⟩

/-- Assemble the spectral Rademacher estimate, the two Donsker/Portmanteau
transfers, and the endpoint return kernel into a horizontal-tube lower rate.
The integer parameters and strict limiting corridor margins are exposed so
the final real-parameter selection can be checked independently. -/
theorem one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_spectralEndpointWindows
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {constant : ℝ} (hconstant : 0 < constant)
    (blockLength time latticeScale spacing windowRadius : ℕ → ℕ)
    (hblockLengthPos : ∀ᶠ n in atTop, 0 < blockLength n)
    (hcountLimit : Tendsto
      (fun n => ((n / blockLength n + 1 : ℕ) : ℝ) *
        scale n ^ 2 / (n : ℝ)) atTop (nhds (1 / constant)))
    (htime : ∀ n, 0 < time n)
    (htimeTop : Tendsto time atTop atTop)
    (htimeEq : ∀ᶠ n in atTop, time n = blockLength n)
    (hlatticeScale : ∀ n, 0 < latticeScale n)
    (hwindow : ∀ n, 2 ≤ windowRadius n)
    (hfitSpectral : ∀ n,
      3 * spacing n + windowRadius n ≤ 2 * latticeScale n)
    {c p spectralLower applicationLower : ℝ}
    (hwidth : Tendsto (fun n => ((8 * latticeScale n : ℕ) : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
        ((8 * latticeScale n : ℕ) : ℝ) ^ 2) atTop (nhds c))
    (hproportion : Tendsto (fun n => ((windowRadius n - 1 : ℕ) : ℝ) /
        ((8 * latticeScale n : ℕ) : ℝ)) atTop (nhds p))
    (hp : 0 < p)
    (hsmallLimit : Real.exp (c * (-(Real.pi ^ 2) / 2)) <
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p) /
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p + 8))
    (hspectralLower : spectralLower <
      p * Real.exp (c * (-(Real.pi ^ 2) / 2)))
    (happlicationLower : 0 < applicationLower)
    (happlicationLowerOne : applicationLower ≤ 1)
    (happlicationBelow : applicationLower < spectralLower)
    {closedRadius closedWindow openRadius openWindow meshLimit : ℝ}
    (hclosedRadius : 0 ≤ closedRadius)
    (hclosedOpenRadius : closedRadius < openRadius)
    (hclosedOpenWindow : closedWindow < openWindow)
    (applicationRadius applicationWindow : ℕ → ℝ)
    (hwindowLimit : ∀ i ∈ Finset.Icc (-3 : ℤ) 3, ∀ᶠ n in atTop,
      4 * (latticeScale n : ℝ) / Real.sqrt (time n) ≤ closedRadius ∧
        (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n)) -
            (windowRadius n : ℝ) / Real.sqrt (time n) ≥
          (i : ℝ) * meshLimit - closedWindow ∧
        (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n)) +
            (windowRadius n : ℝ) / Real.sqrt (time n) ≤
          (i : ℝ) * meshLimit + closedWindow)
    (happlicationContainsOpen : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ∀ᶠ n in atTop,
        openRadius ≤ applicationRadius n ∧
          (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n)) -
              applicationWindow n ≤
            (i : ℝ) * meshLimit - openWindow ∧
          (i : ℝ) * meshLimit + openWindow ≤
            (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n)) +
              applicationWindow n)
    (hspacingPositive : ∀ᶠ n in atTop,
      0 < (spacing n : ℝ) / Real.sqrt (time n))
    (happlicationWindowPositive : ∀ᶠ n in atTop, 0 < applicationWindow n)
    (hreturnWindowLe : ∀ᶠ n in atTop,
      applicationWindow n ≤ 2 * ((spacing n : ℝ) / Real.sqrt (time n)))
    (houterFit : ∀ᶠ n in atTop,
      2 * (applicationRadius n + 3 * ((spacing n : ℝ) / Real.sqrt (time n)) +
        applicationWindow n) * Real.sqrt (blockLength n) ≤ scale n) :
    ((1 / constant) * Real.log applicationLower ≤
      atTop.liminf (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal) ∧
      (∀ᶠ n in atTop, 0 < horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n) ∧
      Filter.IsBoundedUnder (· ≥ ·) atTop (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) := by
  have hnormalized :=
    eventually_forall_sevenCenteredUnitVarianceEndpointWindowProbability_ge_of_spectralBands
      ν hν hB hcontinuous hmeasurable latticeScale time spacing windowRadius
      hlatticeScale htime htimeTop hwindow hfitSpectral hwidth hratio hproportion
      hp hsmallLimit hspectralLower (le_of_lt happlicationLower)
      happlicationBelow hclosedRadius hclosedOpenRadius hclosedOpenWindow
      applicationRadius applicationWindow hwindowLimit happlicationContainsOpen
  have hblock : ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ENNReal.ofReal applicationLower ≤
        normalizedEndpointWindowProbabilityAlong ν applicationRadius
          (fun n => (spacing n : ℝ) / Real.sqrt (time n)) applicationWindow
          i (fun n => Real.sqrt (blockLength n)) blockLength n := by
    filter_upwards [hnormalized, htimeEq] with n hprob heq
    intro i hi
    have hroot : Real.sqrt (time n : ℝ) = Real.sqrt (blockLength n : ℝ) := by
      rw [heq]
    simpa [normalizedEndpointWindowProbabilityAlong, heq, hroot] using hprob i hi
  have hrate :=
    one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_endpointWindowBlocks
      ν hscale blockLength hblockLengthPos hcountLimit hspacingPositive
      happlicationWindowPositive hreturnWindowLe hconstant houterFit
      (ENNReal.ofReal applicationLower)
      (ENNReal.ofReal_pos.mpr happlicationLower)
      (ENNReal.ofReal_le_one.mpr happlicationLowerOne) hblock
  have htoReal : (ENNReal.ofReal applicationLower).toReal = applicationLower :=
    ENNReal.toReal_ofReal (le_of_lt happlicationLower)
  refine ⟨?_, ?_, ?_⟩
  · simpa [htoReal] using hrate.1
  · exact hrate.2.1
  · exact hrate.2.2

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
