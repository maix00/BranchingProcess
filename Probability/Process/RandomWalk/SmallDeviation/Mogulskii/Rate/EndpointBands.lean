/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.BlockScale
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.DonskerEndpointBands
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Mogulskii lower rate from the endpoint-band block comparison

This composes the fixed diffusive-block Donsker estimate with the original
endpoint-band return argument at block length `⌊c * aₙ²⌋`.  The only
probabilistic input left open here is the explicit Brownian mass of the seven
endpoint-band events; scale transfer and the logarithmic normalization are
proved in this file.
-/

open Filter MeasureTheory Set Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- The endpoint-band lower block estimate gives a Mogulskii logarithmic
lower bound along every subdiffusive scale.  The outer corridor is required
to fit inside the target tube; the coefficient `1 / constant` is the limit
of the number of blocks multiplied by `aₙ² / n`.

This is the scale-transfer step in the original lower-bound route.  The
Brownian endpoint-band masses are explicit hypotheses, not hidden in a
support or positivity axiom. -/
theorem one_div_constant_mul_log_toReal_le_liminf_scaledLog_horizontalTubeProbability_of_endpointBands
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {radius ε constant : ℝ}
    (hradius : 0 < radius) (hε : 0 < ε) (hconstant : 0 < constant)
    (hfit : 2 * (radius + 4 * ε) * Real.sqrt constant < 1)
    (lowerBound : ENNReal) (hlowerBound : 0 < lowerBound)
    (hlowerBoundOne : lowerBound ≤ 1)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε))) :
    (1 / constant) * Real.log lowerBound.toReal ≤
      atTop.liminf (fun n => scale n ^ 2 / (n : ℝ) *
        Real.log (horizontalTubeProbability (independentIncrementLaw ν)
          (1 / 2) (scale n) n).toReal) := by
  let length : ℕ → ℕ := diffusiveBlockLength constant scale
  let count : ℕ → ℕ := fun n => n / length n + 1
  let probability : ℕ → ENNReal := fun n => horizontalTubeProbability
    (independentIncrementLaw ν) (1 / 2) (scale n) n
  let ratio : ℕ → ℝ := fun n => scale n ^ 2 / (n : ℝ)
  let coefficient : ℕ → ℝ := fun n => (count n : ℝ) * ratio n

  have hlengthTop : Tendsto length atTop atTop := by
    simpa [length] using hscale.tendsto_diffusiveBlockLength_atTop hconstant
  have hlengthPos : ∀ᶠ n in atTop, 0 < length n := by
    simpa [length] using hscale.eventually_diffusiveBlockLength_pos hconstant
  have hcountRatio : Tendsto coefficient atTop (nhds (1 / constant)) := by
    convert hscale.tendsto_succ_completeBlockCount_mul_sq_div
      hconstant using 1
    · simp only [coefficient, count, ratio, length]
      funext n
      ring

  have hbandEventually := eventually_forall_normalizedEndpointBandProbability_ge
    ν hν hB hcontinuous hmeasurable hradius ε lowerBound hbelow
  have hbandAtBlockLength : ∀ᶠ n in atTop,
      ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
        lowerBound ≤ normalizedEndpointBandProbability ν radius ε i (length n) :=
    hlengthTop.eventually hbandEventually

  have hfitEventually : ∀ᶠ n in atTop,
      2 * (radius + 4 * ε) * Real.sqrt (length n) ≤ scale n := by
    have hsqrtRatio := hscale.tendsto_sqrt_diffusiveBlockLength_div hconstant
    have hnormalized : Tendsto
        (fun n => 2 * (radius + 4 * ε) *
          (Real.sqrt (length n) / scale n)) atTop
        (nhds (2 * (radius + 4 * ε) * Real.sqrt constant)) := by
      simpa using (tendsto_const_nhds.mul hsqrtRatio)
    have hstrict : ∀ᶠ n in atTop,
        2 * (radius + 4 * ε) *
          (Real.sqrt (length n) / scale n) < 1 :=
      hnormalized.eventually (eventually_lt_nhds hfit)
    filter_upwards [hstrict, hscale.eventually_pos] with n hn hscalePos
    have heq : 2 * (radius + 4 * ε) *
        (Real.sqrt (length n) / scale n) =
          (2 * (radius + 4 * ε) * Real.sqrt (length n)) / scale n := by
      ring
    rw [heq] at hn
    have hlt := (div_lt_iff₀ hscalePos).mp hn
    exact le_of_lt (by simpa only [one_mul] using hlt)

  have hpower : ∀ᶠ n in atTop,
      lowerBound ^ count n ≤ probability n := by
    filter_upwards [hbandAtBlockLength, hfitEventually,
      hlengthPos, hscale.eventually_pos] with n hbands hfitN hlengthN hscaleN
    have hcover : n ≤ count n * length n := by
      have hdiv := Nat.lt_mul_div_succ n hlengthN
      dsimp [count]
      simpa [Nat.mul_comm] using hdiv.le
    have hsqrt : 0 < Real.sqrt (length n) :=
      Real.sqrt_pos.2 (by exact_mod_cast hlengthN)
    have hprefix := horizontalTubeProbability_ge_pow_endpointBands_of_horizon_le
      (ν.map fun x : ℝ => x / Real.sqrt (length n)) hε
      (count n) (length n) n hcover lowerBound (hbands)
    have hmap := horizontalTubeProbability_map_div ν (1 / 2 : ℝ)
      (2 * (radius + 4 * ε) * Real.sqrt (length n)) n hsqrt
    have hmapWidth :
        (2 * (radius + 4 * ε) * Real.sqrt (length n)) /
            Real.sqrt (length n) = 2 * (radius + 4 * ε) := by
      field_simp [hsqrt.ne']
    rw [hmapWidth] at hmap
    have houter : lowerBound ^ count n ≤
        horizontalTubeProbability (independentIncrementLaw ν) (1 / 2)
          (2 * (radius + 4 * ε) * Real.sqrt (length n)) n :=
      hprefix.trans_eq hmap
    have hwide := horizontalTubeProbability_mono_width
      (independentIncrementLaw ν) (a := (1 / 2 : ℝ))
      (width₁ := 2 * (radius + 4 * ε) * Real.sqrt (length n))
      (width₂ := scale n) (n := n) (by norm_num) (by norm_num) hfitN
    exact houter.trans hwide

  have hlogPointwise : ∀ᶠ n in atTop,
      coefficient n * Real.log lowerBound.toReal ≤
        ratio n * Real.log (probability n).toReal := by
    filter_upwards [hpower, hlengthPos, hscale.eventually_pos,
      eventually_gt_atTop 0] with n hprob hlen hscaleN hn
    have hprobOne : probability n ≤ 1 := by
      calc
        probability n ≤ independentIncrementLaw ν Set.univ := by
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
      (by simpa [ENNReal.toReal_pow] using
        pow_pos hlowerBoundReal (count n)) hprobReal
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
    hcountRatio.mul_const _

  have hrightUpper : ∀ᶠ n in atTop,
      ratio n * Real.log (probability n).toReal ≤ 0 := by
    filter_upwards [hscale.eventually_pos, eventually_gt_atTop 0] with n hs hn
    have hprobOne : probability n ≤ 1 := by
      calc
        probability n ≤ independentIncrementLaw ν Set.univ := by
          dsimp [probability]
          exact measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hprobTop : probability n ≠ ⊤ :=
      ne_of_lt (hprobOne.trans_lt ENNReal.one_lt_top)
    have htoRealOne : (probability n).toReal ≤ 1 := by
      exact (ENNReal.toReal_le_toReal hprobTop ENNReal.one_ne_top).2 hprobOne
    have hlogNonpos : Real.log (probability n).toReal ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg htoRealOne
    have hratioNonneg : 0 ≤ ratio n := by
      dsimp [ratio]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hratioNonneg hlogNonpos

  calc
    (1 / constant) * Real.log lowerBound.toReal =
        atTop.liminf (fun n => coefficient n * Real.log lowerBound.toReal) :=
      hleft.liminf_eq.symm
    _ ≤ atTop.liminf (fun n => ratio n * Real.log (probability n).toReal) :=
      Filter.liminf_le_liminf hlogPointwise hleft.isBoundedUnder_ge
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop hrightUpper)
    _ = _ := rfl

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
