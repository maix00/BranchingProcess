/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.HorizontalTube.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.HorizontalTube.Scales
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.HorizontalTube.EndpointWindowEvent
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.HorizontalTube.Lemmas.EndpointWindowCorridor
import Analysis.Asymptotics.Scale.Sampling
/-!
# Endpoint-window form of the finite-variance horizontal-tube rate

The public declarations in this module are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_along`: the endpoint-window logarithmic rate $-\pi^2\sigma^2/2$ along sampled times and widths whose endpoint interval contains a fixed subinterval of $(0,1)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_realWidthAlong`: the corresponding sampled rate for real widths.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_realWidth`: the rate as $D\to\infty$ for real-width indexed integer horizons.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate`: the rate for integer widths and superquadratic horizons.

These results formalize Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii). The source-path rate is A. A. Mogul'skii, Theorem 3, Section 4, p. 764, in “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(1) (1975), 726–736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open Asymptotics
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Sampled-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii). The endpoint
window eventually contains a fixed interior interval. Its rate input is
Mogul'skii, Theorem 3, Section 4, p. 764, in “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(1) (1975), 726–736, DOI
10.1137/1119081. -/
theorem centeredFiniteVariance_endpointWindowProbabilityRate_along
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {time width : ℕ → ℕ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidth : Tendsto (fun k : ℕ => (width k : ℝ)) atTop atTop)
    (hwidthSq : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ)) atTop (𝓝 0))
    {v₁ v₂ : ℕ → ℝ} {a u v : ℝ}
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hwindow : ∀ᶠ k : ℕ in atTop,
      v₁ (width k) ≤ u ∧ v ≤ v₂ (width k))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν) :
    Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (width k : ℝ) (time k - 1) (v₁ (width k)) (v₂ (width k))).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let scale := sampledIntegerWidthScale time width htime
  let corridorUnion := endpointWindowCorridorUnion a u v ha haOne hu huv hv
  let sourceProbability : ℕ → ℝ≥0∞ := fun n => iidSequenceLaw ν
    {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈ corridorUnion.toSet}
  let targetProbability : ℕ → ℝ≥0∞ := fun k =>
    horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
      (width k : ℝ) (time k - 1) (v₁ (width k)) (v₂ (width k))
  let tubeProbability : ℕ → ℝ≥0∞ := fun k =>
    horizontalTubeProbability (iidSequenceLaw ν) a (width k : ℝ) (time k - 1)
  let limit : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  have hsmall := sampledIntegerWidthScale_isSmallDeviationScale
    htime htimePos hwidth hwidthSq
  have hscaleEq (k : ℕ) : scale (time k) = (width k : ℝ) := by
    simp [scale, sampledIntegerWidthScale,
      sampledTimeIntervalIndex_at_time htime]
  have hsource :=
    centeredFiniteVariance_sourceFiniteCorridorUnionProbabilityRate
      hsmall hcentered hsquare hvariance corridorUnion
  have hsourcePositive : ∀ᶠ k : ℕ in atTop,
      0 < (sourceProbability (time k)).toReal := by
    filter_upwards [htime.tendsto_atTop.eventually hsource.1] with k hk
    simpa [sourceProbability] using hk
  have hsourceRateAtTime : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) *
        Real.log (sourceProbability (time k)).toReal)
      atTop (𝓝 limit) := by
    have hrate := hsource.2.comp htime.tendsto_atTop
    have heq : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) *
        Real.log (sourceProbability (time k)).toReal) =ᶠ[atTop]
        (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) *
          Real.log (sourceProbability (time k)).toReal) := by
      filter_upwards with k
      rw [hscaleEq k]
    have hrate' := hrate.congr' heq
    have henergy := endpointWindowCorridorUnion_realEnergy
      a u v ha haOne hu huv hv
    simpa [sourceProbability, corridorUnion, limit, henergy] using hrate'
  have hsourceRatePred : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (sourceProbability (time k)).toReal)
      atTop (𝓝 limit) :=
    tendsto_scaledRate_div_predTime htime.tendsto_atTop hsourceRateAtTime
  have htubeRate :=
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate_along
      htime htimePos hwidth hwidthSq hcentered hsquare hvariance ha haOne
  have hscalePositive : ∀ᶠ k : ℕ in atTop, 0 < scale (time k) :=
    htime.tendsto_atTop.eventually hsmall.eventually_pos
  have hlogSqueeze : ∀ᶠ k : ℕ in atTop,
      (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (sourceProbability (time k)).toReal ≤
        (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (targetProbability k).toReal ∧
      (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (targetProbability k).toReal ≤
        (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (tubeProbability k).toReal := by
    filter_upwards [hsourcePositive, hscalePositive, hwindow]
      with k hsourcePos hscalePos hwindowK
    have hsourceSubset :
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ⊆
          horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1)
            (v₁ (width k)) (v₂ (width k)) := by
      have hfixed :
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ⊆
            horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1) u v := by
        rw [endpointWindowCorridorUnion_toSet a u v ha haOne hu huv hv]
        simpa [hscaleEq k] using
          sourceTerminalJumpCorridor_subset_endpointWindow
            (n := time k) (scale := scale) (a := a) (u := u) (v := v)
            (htimePos k) hscalePos ha haOne hu huv hv
      intro increment hinc
      rcases hfixed hinc with ⟨htube, ⟨hlower, hupper⟩⟩
      constructor
      · exact htube
      · constructor
        · apply le_trans _ hlower
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (width k))
          linarith [hwindowK.1]
        · apply le_trans hupper _
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (width k))
          linarith [hwindowK.2]
    have hsourceMeasure : sourceProbability (time k) ≤ targetProbability k := by
      change iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ≤
        iidSequenceLaw ν
          (horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1)
            (v₁ (width k)) (v₂ (width k)))
      exact measure_mono hsourceSubset
    have htargetSubset :
        horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1)
          (v₁ (width k)) (v₂ (width k)) ⊆
        {increment | InHorizontalTube a (width k : ℝ) (time k - 1) increment} := by
      intro increment h
      exact h.1
    have htargetMeasure : targetProbability k ≤ tubeProbability k := by
      change iidSequenceLaw ν
        (horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1)
          (v₁ (width k)) (v₂ (width k))) ≤
        iidSequenceLaw ν
          {increment | InHorizontalTube a (width k : ℝ) (time k - 1) increment}
      exact measure_mono htargetSubset
    have hsourceReal := ENNReal.toReal_mono (measure_ne_top _ _) hsourceMeasure
    have htargetPos : 0 < (targetProbability k).toReal :=
      lt_of_lt_of_le hsourcePos hsourceReal
    have htargetReal := ENNReal.toReal_mono (measure_ne_top _ _) htargetMeasure
    have htubePos : 0 < (tubeProbability k).toReal :=
      lt_of_lt_of_le htargetPos htargetReal
    have hlogLower : Real.log (sourceProbability (time k)).toReal ≤
        Real.log (targetProbability k).toReal :=
      Real.log_le_log hsourcePos hsourceReal
    have hlogUpper : Real.log (targetProbability k).toReal ≤
        Real.log (tubeProbability k).toReal :=
      Real.log_le_log htargetPos htargetReal
    have hfactor : 0 ≤ (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) :=
      div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    exact ⟨mul_le_mul_of_nonneg_left hlogLower hfactor,
      mul_le_mul_of_nonneg_left hlogUpper hfactor⟩
  have hrate : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (targetProbability k).toReal)
      atTop (𝓝 limit) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hsourceRatePred htubeRate ?_ ?_
    · filter_upwards [hlogSqueeze] with k hk
      exact hk.1
    · filter_upwards [hlogSqueeze] with k hk
      exact hk.2
  simpa [targetProbability, limit] using hrate

/-- Real-width sampled form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii).
For positive real widths $D_k\to\infty$, time scales $t_k$ with
$D_k^2/t_k\to0$, and a terminal window eventually containing a fixed
$[u,v]\subset(0,1)$, the endpoint-window logarithmic rate is
$-\pi^2\sigma^2/2$. The proof uses the same terminal-jump source
corridor and upper horizontal-tube squeeze as the integer-width form.
The source rate is A. A. Mogul'skii, Theorem 3, Section 4, p. 764, in “Small
deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(1)
(1975), 726–736, DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_endpointWindowProbabilityRate_realWidthAlong
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {time : ℕ → ℕ} {width : ℕ → ℝ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidthPos : ∀ k, 0 < width k)
    (hwidth : Tendsto width atTop atTop)
    (hwidthSq : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ)) atTop (𝓝 0))
    {v₁ v₂ : ℝ → ℝ} {a u v : ℝ}
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hwindow : ∀ᶠ k : ℕ in atTop,
      v₁ (width k) ≤ u ∧ v ≤ v₂ (width k))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν) :
    Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (width k) (time k - 1) (v₁ (width k)) (v₂ (width k))).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let scale := sampledRealWidthScale time width htime
  let corridorUnion := endpointWindowCorridorUnion a u v ha haOne hu huv hv
  let sourceProbability : ℕ → ℝ≥0∞ := fun n => iidSequenceLaw ν
    {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈ corridorUnion.toSet}
  let targetProbability : ℕ → ℝ≥0∞ := fun k =>
    horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
      (width k) (time k - 1) (v₁ (width k)) (v₂ (width k))
  let tubeProbability : ℕ → ℝ≥0∞ := fun k =>
    horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)
  let limit : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  have hsmall := sampledRealWidthScale_isSmallDeviationScale
    htime htimePos hwidthPos hwidth hwidthSq
  have hscaleEq (k : ℕ) : scale (time k) = width k := by
    simp [scale, sampledRealWidthScale,
      sampledTimeIntervalIndex_at_time htime]
  have hsource :=
    centeredFiniteVariance_sourceFiniteCorridorUnionProbabilityRate
      hsmall hcentered hsquare hvariance corridorUnion
  have hsourcePositive : ∀ᶠ k : ℕ in atTop,
      0 < (sourceProbability (time k)).toReal := by
    filter_upwards [htime.tendsto_atTop.eventually hsource.1] with k hk
    simpa [sourceProbability] using hk
  have hsourceRateAtTime : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ) *
        Real.log (sourceProbability (time k)).toReal)
      atTop (𝓝 limit) := by
    have hrate := hsource.2.comp htime.tendsto_atTop
    have heq : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) *
        Real.log (sourceProbability (time k)).toReal) =ᶠ[atTop]
        (fun k : ℕ => width k ^ 2 / (time k : ℝ) *
          Real.log (sourceProbability (time k)).toReal) := by
      filter_upwards with k
      rw [hscaleEq k]
    have hrate' := hrate.congr' heq
    have henergy := endpointWindowCorridorUnion_realEnergy
      a u v ha haOne hu huv hv
    simpa [sourceProbability, corridorUnion, limit, henergy] using hrate'
  have hsourceRatePred : Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (sourceProbability (time k)).toReal)
      atTop (𝓝 limit) :=
    tendsto_scaledRate_div_predTime htime.tendsto_atTop hsourceRateAtTime
  have htubeRate :=
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong
      htime htimePos hwidthPos hwidth hwidthSq hcentered hsquare hvariance ha haOne
  have hscalePositive : ∀ᶠ k : ℕ in atTop, 0 < scale (time k) :=
    htime.tendsto_atTop.eventually hsmall.eventually_pos
  have hlogSqueeze : ∀ᶠ k : ℕ in atTop,
      width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (sourceProbability (time k)).toReal ≤
        width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (targetProbability k).toReal ∧
      width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (targetProbability k).toReal ≤
        width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (tubeProbability k).toReal := by
    filter_upwards [hsourcePositive, hscalePositive, hwindow]
      with k hsourcePos hscalePos hwindowK
    have hsourceSubset :
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ⊆
          horizontalTubeEndpointWindowEvent a (width k) (time k - 1)
            (v₁ (width k)) (v₂ (width k)) := by
      have hfixed :
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ⊆
            horizontalTubeEndpointWindowEvent a (width k) (time k - 1) u v := by
        rw [endpointWindowCorridorUnion_toSet a u v ha haOne hu huv hv]
        simpa [hscaleEq k] using
          sourceTerminalJumpCorridor_subset_endpointWindow
            (n := time k) (scale := scale) (a := a) (u := u) (v := v)
            (htimePos k) hscalePos ha haOne hu huv hv
      intro increment hinc
      rcases hfixed hinc with ⟨htube, ⟨hlower, hupper⟩⟩
      constructor
      · exact htube
      · constructor
        · apply le_trans _ hlower
          apply mul_le_mul_of_nonneg_right _ (hwidthPos k).le
          linarith [hwindowK.1]
        · apply le_trans hupper _
          apply mul_le_mul_of_nonneg_right _ (hwidthPos k).le
          linarith [hwindowK.2]
    have hsourceMeasure : sourceProbability (time k) ≤ targetProbability k := by
      change iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ≤
        iidSequenceLaw ν
          (horizontalTubeEndpointWindowEvent a (width k) (time k - 1)
            (v₁ (width k)) (v₂ (width k)))
      exact measure_mono hsourceSubset
    have htargetSubset :
        horizontalTubeEndpointWindowEvent a (width k) (time k - 1)
          (v₁ (width k)) (v₂ (width k)) ⊆
        {increment | InHorizontalTube a (width k) (time k - 1) increment} := by
      intro increment h
      exact h.1
    have htargetMeasure : targetProbability k ≤ tubeProbability k := by
      change iidSequenceLaw ν
        (horizontalTubeEndpointWindowEvent a (width k) (time k - 1)
          (v₁ (width k)) (v₂ (width k))) ≤
        iidSequenceLaw ν
          {increment | InHorizontalTube a (width k) (time k - 1) increment}
      exact measure_mono htargetSubset
    have hsourceReal := ENNReal.toReal_mono (measure_ne_top _ _) hsourceMeasure
    have htargetPos : 0 < (targetProbability k).toReal :=
      lt_of_lt_of_le hsourcePos hsourceReal
    have htargetReal := ENNReal.toReal_mono (measure_ne_top _ _) htargetMeasure
    have htubePos : 0 < (tubeProbability k).toReal :=
      lt_of_lt_of_le htargetPos htargetReal
    have hlogLower : Real.log (sourceProbability (time k)).toReal ≤
        Real.log (targetProbability k).toReal :=
      Real.log_le_log hsourcePos hsourceReal
    have hlogUpper : Real.log (targetProbability k).toReal ≤
        Real.log (tubeProbability k).toReal :=
      Real.log_le_log htargetPos htargetReal
    have hfactor : 0 ≤ width k ^ 2 / ((time k - 1 : ℕ) : ℝ) :=
      div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    exact ⟨mul_le_mul_of_nonneg_left hlogLower hfactor,
      mul_le_mul_of_nonneg_left hlogUpper hfactor⟩
  have hrate : Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (targetProbability k).toReal)
      atTop (𝓝 limit) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hsourceRatePred htubeRate ?_ ?_
    · filter_upwards [hlogSqueeze] with k hk
      exact hk.1
    · filter_upwards [hlogSqueeze] with k hk
      exact hk.2
  simpa [targetProbability, limit] using hrate

/-- Real-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii). For
$L_D/D^2\to\infty$ and endpoint windows containing a fixed interval
$[u,v]\subset(0,1)$ eventually, the logarithmic endpoint-window probability
has rate $-\pi^2\sigma^2/2$. The proof reduces a counterexample real-width
sequence to the sampled-width form above. The rate input is A. A. Mogul'skii,
“Small deviations in the sample function space,” Theorem 3, Section 4, p. 764
(1974); English translation, “Small Deviations in a Space of Trajectories,”
DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_endpointWindowProbabilityRate_realWidth
    {L : ℝ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Tendsto (fun D : ℝ => D ^ 2 / (L D : ℝ)) atTop (𝓝 0))
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a u v : ℝ} (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {v₁ v₂ : ℝ → ℝ}
    (hwindow : ∀ᶠ D : ℝ in atTop, v₁ D ≤ u ∧ v ≤ v₂ D) :
    Tendsto
      (fun D : ℝ => D ^ 2 / (L D : ℝ) * Real.log
        (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          D (L D) (v₁ D) (v₂ D)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  apply tendsto_realWidthRate_of_sampledTime
    (rate := fun D n => D ^ 2 / (n : ℝ) * Real.log
      (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
        D n (v₁ D) (v₂ D)).toReal)
    (limit := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)) hL hquadratic
  intro time width htime htimePos hwidthPos hwidth hwidthSq
  have hwindowSample : ∀ᶠ k : ℕ in atTop,
      v₁ (width k) ≤ u ∧ v ≤ v₂ (width k) :=
    hwidth.eventually hwindow
  simpa using centeredFiniteVariance_endpointWindowProbabilityRate_realWidthAlong
    htime htimePos hwidthPos hwidth hwidthSq ha haOne hu huv hv
    hwindowSample hcentered hsquare hvariance

/-- Integer-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii). The endpoint
window eventually contains one fixed nonempty interval strictly inside the
tube, and the scale condition is `L Δ / Δ² → ∞`. The rate input is Mogul'skii,
Theorem 3, Section 4, p. 764, in “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(1) (1975), 726–736, DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_endpointWindowProbabilityRate
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a u v : ℝ} (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {v₁ v₂ : ℕ → ℝ}
    (hwindow : ∀ᶠ Δ : ℕ in atTop, v₁ Δ ≤ u ∧ v ≤ v₂ Δ) :
    Tendsto
      (fun Δ : ℕ => (Δ : ℝ) ^ 2 / (L Δ : ℝ) * Real.log
        (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (Δ : ℝ) (L Δ) (v₁ Δ) (v₂ Δ)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let rate : ℕ → ℝ := fun Δ => (Δ : ℝ) ^ 2 / (L Δ : ℝ) * Real.log
    (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
      (Δ : ℝ) (L Δ) (v₁ Δ) (v₂ Δ)).toReal
  let c : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hbad : ∀ N : ℕ, ∃ Δ > N, ε ≤ dist (rate Δ) c := by
    intro N
    by_contra hN
    apply hnot
    refine ⟨N + 1, ?_⟩
    intro Δ hΔ
    by_contra hdist
    apply hN
    refine ⟨Δ, lt_of_lt_of_le (Nat.lt_succ_self N) hΔ,
      le_of_not_gt hdist⟩
  obtain ⟨widthSeq, hwidthStrict, hwidthBad⟩ :=
    Nat.exists_strictMono_subsequence hbad
  let rawTime : ℕ → ℕ := fun k => L (widthSeq k) + 1
  have hLwidth : Tendsto (fun k => L (widthSeq k)) atTop atTop :=
    hL.comp hwidthStrict.tendsto_atTop
  have hrawTime : Tendsto rawTime atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hLwidth.eventually (eventually_ge_atTop b)] with k hk
    dsimp [rawTime]
    omega
  obtain ⟨φ, hφ, hφtime⟩ := strictMono_subseq_of_tendsto_atTop hrawTime
  let widthSub : ℕ → ℕ := fun k => widthSeq (φ k)
  let timeSub : ℕ → ℕ := fun k => rawTime (φ k)
  have htimeSub : StrictMono timeSub := by
    simpa [timeSub, rawTime, Function.comp_def] using hφtime
  have hwidthSubTop : Tendsto widthSub atTop atTop :=
    hwidthStrict.tendsto_atTop.comp hφ.tendsto_atTop
  have hwidthSubRealTop : Tendsto (fun k => (widthSub k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthSubTop
  have hwidthSqRaw : Tendsto
      (fun k => (widthSeq k : ℝ) ^ 2 / ((L (widthSeq k) : ℝ) + 1))
      atTop (𝓝 0) :=
    (Asymptotics.tendsto_width_sq_div_shiftedScale_of_superquadratic hquadratic).comp
      hwidthStrict.tendsto_atTop
  have hwidthSqSub : Tendsto
      (fun k => (widthSub k : ℝ) ^ 2 / (timeSub k : ℝ))
      atTop (𝓝 0) := by
    simpa [widthSub, timeSub, rawTime, Function.comp_def] using
      hwidthSqRaw.comp hφ.tendsto_atTop
  have hwindowSub : ∀ᶠ k : ℕ in atTop,
      v₁ (widthSub k) ≤ u ∧ v ≤ v₂ (widthSub k) :=
    hwidthSubTop.eventually hwindow
  have hrateSub :=
    centeredFiniteVariance_endpointWindowProbabilityRate_along
      htimeSub (fun k => by dsimp [timeSub, rawTime]; omega)
      hwidthSubRealTop hwidthSqSub ha haOne hu huv hv hwindowSub
      hcentered hsquare hvariance
  have hrateOnWidths : Tendsto (fun k => rate (widthSub k)) atTop (𝓝 c) := by
    simpa [rate, widthSub, timeSub, rawTime, Function.comp_def,
      Nat.add_sub_cancel_right] using hrateSub
  have hclose : ∀ᶠ k : ℕ in atTop, dist (rate (widthSub k)) c < ε :=
    hrateOnWidths.eventually (Metric.ball_mem_nhds c hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hclose
  have hlt := hN N le_rfl
  have hge : ε ≤ dist (rate (widthSub N)) c := hwidthBad (φ N)
  exact (not_lt_of_ge hge) hlt

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
