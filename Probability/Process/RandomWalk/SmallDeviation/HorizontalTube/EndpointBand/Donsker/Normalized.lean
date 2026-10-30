/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Skorokhod
public import Probability.Distributions.Moments.Real
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic
public import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Endpoint
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Iteration
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Scale
/-!
# Donsker transfer for finite endpoint bands

The finite collection of open block events is chosen to match the lower
endpoint-band comparison. The corridor radius and band spacing are explicit
parameters, so later scale-diagonal arguments need not assume a unit block
radius.

For partial sums $S_k=\sum_{j<k}\xi_j$, the normalized endpoint-band
probability is
\[
 p_{n,i}=\mathbb P_\nu\!\left(
   |S_k|<r\sqrt n\ (1\le k\le n),\quad
   \frac{S_n}{\sqrt n}\in((i-1)\varepsilon,(i+1)\varepsilon)
 \right).
\]
The Donsker comparison gives $\mathbb P(B\in\mathcal O_{r,i})
\leq\liminf_{n\to\infty}p_{n,i}$ for the open Brownian event
\[
 \mathcal O_{r,i}=\{f\in C([0,1]): |f(t)|<r\ (0\leq t\leq1),\quad
                 f(1)\in((i-1)\varepsilon,(i+1)\varepsilon)\},
\]
where $B$ is standard Brownian motion.

## Public declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand.normalizedEndpointBandProbability`:
  the probability of a normalized strict tube with the terminal displacement
  in the `i`th endpoint band.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand.brownianEndpointBand_le_liminf_normalizedEndpointBandProbability`:
  for centered unit-variance increments, the Brownian open-corridor mass is at
  most the liminf of the matching endpoint-band probabilities.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand.eventually_forall_normalizedEndpointBandProbability_ge`:
  a strict Brownian lower bound for each `i ∈ [-3,3]` gives an eventual common
  lower bound for those seven discrete probabilities.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand.eventually_horizontalTubeProbability_ge_pow_endpointBands`:
  if `horizon n ≤ blocks n * n`, the same lower bound raised to `blocks n`
  bounds the horizontal-tube probability from below.

These results use the Donsker endpoint Portmanteau theorem in
`Probability.Process.RandomWalk.FunctionalLimit.Donsker.Corridor.Brownian.Endpoint`;
the functional limit is Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2. The final
estimate uses the reusable finite-block return-kernel iteration.
-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand


/-- A block event for increments normalized by the diffusive scale `√n`. -/
noncomputable def normalizedEndpointBandProbability
    (ν : Measure ℝ) (radius ε : ℝ) (i : ℤ) (n : ℕ) : ENNReal :=
  iidSequenceLaw (ν.map fun x : ℝ => x / Real.sqrt n)
    (endpointWindowBlockEvent radius ε ε i n)

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
  let limit := Skorokhod.ofContinuousMap ∘
    continuousunitIntervalPath B hcontinuous
  have hscale : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hlimit : TendstoInDistribution
      (fun n => RandomWalk.normalizedStepCadlagPathIcc
        (fun n => Real.sqrt n) n)
      atTop limit (fun _ => iidSequenceLaw ν) P := by
    exact RandomWalk.tendstoInDistribution_normalizedStepCadlagPath_brownian
      ν hν.1 hν.2 hB hcontinuous hmeasurable
  have hcltRadius :=
    RandomWalk.measure_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn_of_functionalLimit
      P ν (fun n => Real.sqrt n) hscale limit hlimit
      (width := 2 * radius) (endpointLower := (((i : ℝ) - 1) * ε))
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
    simpa [iidSequenceLaw] using hcltRadius
  have heventuallyEq : ∀ᶠ n : ℕ in atTop,
      normalizedEndpointBandProbability ν radius ε i n =
        iidSequenceLaw ν {increment |
        InOpenHorizontalTube (1 / 2) (2 * radius * Real.sqrt n) n increment ∧
            AdditivePath.displacement n increment / Real.sqrt n ∈
              Set.Ioo (((i : ℝ) - 1) * ε) (((i : ℝ) + 1) * ε)} := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrt : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast hn)
    simpa only [normalizedEndpointBandProbability,
      show ((i : ℝ) - 1) * ε = (i : ℝ) * ε - ε by ring,
      show ((i : ℝ) + 1) * ε = (i : ℝ) * ε + ε by ring] using
      (iidSequenceLaw_endpointWindowBlockEvent_scale ν
        (fun _ => Real.sqrt n) n n hsqrt radius ε ε i).symm
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
        (iidSequenceLaw ν) (1 / 2)
        (2 * (radius + 4 * ε) * Real.sqrt n) (horizon n) := by
  have hbands := eventually_forall_normalizedEndpointBandProbability_ge
    ν hν hB hcontinuous hmeasurable hradius ε lowerBound hbelow
  filter_upwards [hbands, hcover, eventually_gt_atTop 0] with n hbands hcoverN hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hprefix := horizontalTubeProbability_ge_pow_endpointWindows_of_horizon_le
    (ν.map fun x : ℝ => x / Real.sqrt n) hε hε (by linarith [hε])
    (blocks n) n (horizon n) hcoverN lowerBound
    (by simpa [normalizedEndpointBandProbability] using hbands)
  have hprefix' : lowerBound ^ blocks n ≤ horizontalTubeProbability
      (iidSequenceLaw (ν.map fun x : ℝ => x / Real.sqrt n))
      (1 / 2) (2 * (radius + 4 * ε)) (horizon n) := by
    simpa only [show radius + 3 * ε + ε = radius + 4 * ε by ring] using hprefix
  have hscale := horizontalTubeProbability_map_div
    ν (1 / 2) (2 * (radius + 4 * ε) * Real.sqrt n) (horizon n) hsqrt
  have hwidth :
      (2 * (radius + 4 * ε) * Real.sqrt n) / Real.sqrt n =
        2 * (radius + 4 * ε) := by
    field_simp [hsqrt.ne']
  rw [hwidth] at hscale
  exact hprefix'.trans_eq hscale

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointBand
