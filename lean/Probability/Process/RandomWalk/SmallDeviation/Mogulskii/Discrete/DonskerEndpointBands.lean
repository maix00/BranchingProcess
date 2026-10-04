/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Corridor.Brownian.Endpoint
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.EndpointBands

/-!
# Donsker transfer for finite endpoint bands

The finite collection of open block events is chosen to match the lower
endpoint-band comparison. The corridor radius and band spacing are explicit
parameters, so later scale-diagonal arguments need not assume a unit block
radius.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-- A block event for increments normalized by the diffusive scale `√n`. -/
noncomputable def normalizedEndpointBandProbability
    (ν : Measure ℝ) (radius ε : ℝ) (i : ℤ) (n : ℕ) : ENNReal :=
  iidSequenceLaw (ν.map fun x : ℝ => x / Real.sqrt n)
    (endpointBandBlockEvent radius ε i n)

/-- The endpoint-band block event under the normalized increment law is
exactly the open tube and normalized endpoint event used by Donsker's
Portmanteau theorem. -/
theorem iidSequenceLaw_normalizedEndpointBand_eq
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (radius ε : ℝ) (i : ℤ) (n : ℕ) (hn : 0 < n) :
    normalizedEndpointBandProbability ν radius ε i n =
      iidSequenceLaw ν {increment |
        InOpenHorizontalTube (1 / 2) (2 * radius * Real.sqrt n) n increment ∧
          AdditivePath.displacement n increment / Real.sqrt n ∈
            Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)} := by
  unfold normalizedEndpointBandProbability
  rw [← iidSequenceLaw_map_coordinatewise ν
    (fun x : ℝ => x / Real.sqrt n) (measurable_id.div_const _)]
  rw [Measure.map_apply]
  · congr 1
    ext increment
    have hsqrt : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hwidth : (2 * radius * Real.sqrt n) / Real.sqrt n = 2 * radius := by
      field_simp [hsqrt.ne']
    have hpath := inOpenHorizontalTube_div_iff
      (1 / 2) (2 * radius * Real.sqrt n) n increment hsqrt
    have hsum : AdditivePath.displacement n (fun k => increment k / Real.sqrt n) =
        AdditivePath.displacement n increment / Real.sqrt n := by
      simp [AdditivePath.displacement, div_eq_mul_inv, Finset.sum_mul]
    change InOpenHorizontalTube (1 / 2) (2 * radius) n
        (fun k => increment k / Real.sqrt n) ∧
      AdditivePath.displacement n (fun k => increment k / Real.sqrt n) ∈
        Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε) ↔ _
    rw [hwidth] at hpath
    simp only [hpath, hsum]
    simp only [Set.mem_ofPred_eq]
  · exact Measurable.of_eval fun k =>
      (measurable_id.div_const (Real.sqrt n)).comp (measurable_pi_apply k)
  · exact measurableSet_endpointBandBlockEvent radius ε i n

/-- Brownian mass in an open corridor with the specified endpoint band is a
lower bound for the limiting probability of the normalized block event. -/
theorem brownianEndpointBand_le_liminf_normalizedEndpointBandProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {radius : ℝ} (hradius : 0 < radius) (ε : ℝ) (i : ℤ) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)) ≤
      atTop.liminf (fun n => normalizedEndpointBandProbability ν radius ε i n) := by
  have hcltRadius := RandomWalk.brownian_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn
    (ν := ν) hν hB hcontinuous hmeasurable (width := 2 * radius)
    (endpointLower := (((i : ℝ) - 1) * ε))
    (endpointUpper := (((i : ℝ) + 1) * ε)) (by positivity)
  have hclt' :
      P.map (Skorokhod.ofContinuousMap ∘
          continuousunitIntervalPath B hcontinuous)
          (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
            (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)) ≤
        atTop.liminf (fun n : ℕ => iidSequenceLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (2 * radius * Real.sqrt (n : ℝ)) n increment ∧
            AdditivePath.displacement n increment / Real.sqrt (n : ℝ) ∈
              Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)}) := by
    simpa [independentIncrementLaw] using hcltRadius
  have heventuallyEq : ∀ᶠ n : ℕ in atTop,
      normalizedEndpointBandProbability ν radius ε i n =
        iidSequenceLaw ν {increment |
        InOpenHorizontalTube (1 / 2) (2 * radius * Real.sqrt n) n increment ∧
            AdditivePath.displacement n increment / Real.sqrt n ∈
              Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)} := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact iidSequenceLaw_normalizedEndpointBand_eq ν radius ε i n hn
  calc
    _ ≤ atTop.liminf (fun n : ℕ => iidSequenceLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (2 * radius * Real.sqrt (n : ℝ)) n increment ∧
            AdditivePath.displacement n increment / Real.sqrt (n : ℝ) ∈
              Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)}) := hclt'
    _ = atTop.liminf (fun n => normalizedEndpointBandProbability ν radius ε i n) := by
      apply liminf_congr
      filter_upwards [heventuallyEq] with n hn
      exact hn.symm

/-- A strict common lower bound for the seven Brownian endpoint-band masses
transfers, by Donsker, to an eventual common lower bound for all seven
normalized random-walk block probabilities. -/
theorem eventually_forall_normalizedEndpointBandProbability_ge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {radius : ℝ} (hradius : 0 < radius) (ε : ℝ) (lowerBound : ENNReal)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε))) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound ≤ normalizedEndpointBandProbability ν radius ε i n := by
  apply (Finset.Icc (-3 : ℤ) 3).eventually_all.2
  intro i hi
  have hliminf :=
    brownianEndpointBand_le_liminf_normalizedEndpointBandProbability
      ν hν hB hcontinuous hmeasurable hradius ε i
  have hstrict : lowerBound < atTop.liminf
      (fun n => normalizedEndpointBandProbability ν radius ε i n) :=
    (hbelow i hi).trans_le hliminf
  have hbounded : Filter.IsBoundedUnder (· ≥ ·) atTop
      (fun n => normalizedEndpointBandProbability ν radius ε i n) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_lt_of_lt_liminf hstrict hbounded] with n hn
  exact hn.le

/-- Donsker's finite endpoint-band bounds, followed by the discrete return
kernel iteration, yield a horizontal-tube lower bound up to any horizon
covered by complete blocks. The block count may depend on the horizon. The
Brownian endpoint-band masses are explicit hypotheses; establishing their
positivity is a separate Brownian support estimate. -/
theorem eventually_horizontalTubeProbability_ge_pow_endpointBands
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {radius ε : ℝ} (hradius : 0 < radius) (hε : 0 < ε)
    (blocks horizon : ℕ → ℕ) (lowerBound : ENNReal)
    (hcover : ∀ᶠ n : ℕ in atTop, horizon n ≤ blocks n * n)
    (hbelow : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      lowerBound < P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath B hcontinuous)
        (Skorokhod.rangeInOpenIntervalEndsIn (-radius) radius
          (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε))) :
    ∀ᶠ n : ℕ in atTop,
      lowerBound ^ blocks n ≤ horizontalTubeProbability
        (independentIncrementLaw ν) (1 / 2)
        (2 * (radius + 4 * ε) * Real.sqrt n) (horizon n) := by
  have hbands := eventually_forall_normalizedEndpointBandProbability_ge
    ν hν hB hcontinuous hmeasurable hradius ε lowerBound hbelow
  filter_upwards [hbands, hcover, eventually_gt_atTop 0] with n hbands hcoverN hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hprefix := horizontalTubeProbability_ge_pow_endpointBands_of_horizon_le
    (ν.map fun x : ℝ => x / Real.sqrt n) hε (blocks n) n (horizon n)
    hcoverN lowerBound hbands
  have hscale := horizontalTubeProbability_map_div
    ν (1 / 2) (2 * (radius + 4 * ε) * Real.sqrt n) (horizon n) hsqrt
  have hwidth :
      (2 * (radius + 4 * ε) * Real.sqrt n) / Real.sqrt n =
        2 * (radius + 4 * ε) := by
    field_simp [hsqrt.ne']
  rw [hwidth] at hscale
  have hprefix' : lowerBound ^ blocks n ≤ horizontalTubeProbability
      (independentIncrementLaw (ν.map fun x : ℝ => x / Real.sqrt n))
      (1 / 2) (2 * (radius + 4 * ε)) (horizon n) := by
    exact hprefix
  exact hprefix'.trans_eq hscale

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
