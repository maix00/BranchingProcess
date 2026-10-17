/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.InverseScale
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.ContinuousBoundary
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.HorizontalTube.SourceCorridor
/-!
# Finite-variance closed horizontal-tube rate

The public theorem in this module is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_closedHorizontalTubeProbabilityRate`: if $x_n\to\infty$ and $x_n^2/n\to0$, then for a centered increment law with variance $0<\sigma^2<\infty$, the logarithmic probability of the closed horizontal tube has rate $-\pi^2\sigma^2/2$.

This is the core real-scale input for Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i). The proof transfers the strict source-path corridor rate in A. A. Mogul'skii, Theorem 3, Section 4, p. 764 of “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Finite-variance form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i). Its rate input
is A. A. Mogul'skii, Theorem 3, Section 4, p. 764, in “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081. The time horizon is `n - 1`, matching the terminal-left
source path. -/
theorem centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (scale n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let room : ℝ := min a (1 - a) / 4
  let ε : ℕ → ℝ := fun m => room / ((m : ℝ) + 1)
  let c : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  let innerRate : ℕ → ℝ := fun m => c * ((1 - 2 * ε m) ^ 2)⁻¹
  let outerRate : ℕ → ℝ := fun m => c * ((1 + 2 * ε m) ^ 2)⁻¹
  have hroom : 0 < room := by
    dsimp [room]
    exact div_pos (lt_min ha (sub_pos.mpr haOne)) (by norm_num)
  have hεpos (m : ℕ) : 0 < ε m := by
    dsimp [ε]
    positivity
  have hεa (m : ℕ) : ε m < a := by
    have hle : ε m ≤ room := by
      dsimp [ε]
      have hden : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        exact_mod_cast (show 1 ≤ m + 1 by omega)
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hroom, hden])
    have hroomA : room < a := by
      dsimp [room]
      nlinarith [min_le_left a (1 - a), hroom]
    exact lt_of_le_of_lt hle hroomA
  have hεone (m : ℕ) : ε m < 1 - a := by
    have hle : ε m ≤ room := by
      dsimp [ε]
      have hden : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        exact_mod_cast (show 1 ≤ m + 1 by omega)
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hroom, hden])
    have hroomOne : room < 1 - a := by
      dsimp [room]
      nlinarith [min_le_right a (1 - a), hroom]
    exact lt_of_le_of_lt hle hroomOne
  have hεlimit : Tendsto ε atTop (𝓝 0) := by
    have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hroom : Tendsto (fun _ : ℕ => room) atTop (𝓝 room) := tendsto_const_nhds
    have hmul := hroom.mul hbase
    simpa [ε, room, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hinnerRateLimit : Tendsto innerRate atTop (𝓝 c) := by
    have hwidth : Tendsto (fun m : ℕ => 1 - 2 * ε m) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hεlimit)
    have hwidthSq : Tendsto (fun m : ℕ => (1 - 2 * ε m) ^ 2)
        atTop (𝓝 (1 : ℝ)) := by simpa using hwidth.pow 2
    have hinv := hwidthSq.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have hmul := hconst.mul hinv
    simpa [innerRate] using hmul
  have houterRateLimit : Tendsto outerRate atTop (𝓝 c) := by
    have hwidth : Tendsto (fun m : ℕ => 1 + 2 * ε m) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hεlimit)
    have hwidthSq : Tendsto (fun m : ℕ => (1 + 2 * ε m) ^ 2)
        atTop (𝓝 (1 : ℝ)) := by simpa using hwidth.pow 2
    have hinv := hwidthSq.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have hmul := hconst.mul hinv
    simpa [outerRate] using hmul
  let tubeProbability : ℕ → ℝ≥0∞ := fun n =>
    horizontalTubeProbability (iidSequenceLaw ν) a (scale n) (n - 1)
  let tubeRate : ℕ → ℝ := fun n =>
    (scale n) ^ 2 / (n : ℝ) * Real.log (tubeProbability n).toReal
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hsmall.eventually_pos
  have hnPos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hvalid : ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < scale n :=
    hnPos.and hscalePos
  let hbaseSet : ℝ → ℝ → ℕ → Set (ℕ → ℝ) := fun lower upper n =>
    sourceRelativeConstantCorridorEvent scale n lower upper
  have hinnerBoundaryData (m : ℕ) :=
    centeredFiniteVariance_sourceRelativeContinuousBoundaryProbabilityRate
      hsmall hcentered hsquare hvariance
      (constantBoundary (-a + ε m)) (constantBoundary (1 - a - ε m))
      (by
        intro t
        simp only [constantBoundary, ContinuousMap.const_apply]
        linarith [hεa m, hεone m])
      (by
        simp only [constantBoundary, ContinuousMap.const_apply]
        linarith [hεa m])
      (by
        simp only [constantBoundary, ContinuousMap.const_apply]
        linarith [hεone m])
  have houterBoundaryData (m : ℕ) :=
    centeredFiniteVariance_sourceRelativeContinuousBoundaryProbabilityRate
      hsmall hcentered hsquare hvariance
      (constantBoundary (-a - ε m)) (constantBoundary (1 - a + ε m))
      (by
        intro t
        simp only [constantBoundary, ContinuousMap.const_apply]
        nlinarith [hεpos m])
      (by
        simp only [constantBoundary, ContinuousMap.const_apply]
        nlinarith [ha, hεpos m])
      (by
        simp only [constantBoundary, ContinuousMap.const_apply]
        nlinarith [haOne, hεpos m])
  have hinnerPositive (m : ℕ) : ∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal := by
    have hinnerBoundaryRate := hinnerBoundaryData m
    simpa [hbaseSet, sourceRelativeConstantCorridorEvent, constantBoundary] using
      hinnerBoundaryRate.1
  have houterPositive (m : ℕ) : ∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal := by
    have houterBoundaryRate := houterBoundaryData m
    simpa [hbaseSet, sourceRelativeConstantCorridorEvent, constantBoundary] using
      houterBoundaryRate.1
  have hinnerRate (m : ℕ) :
      Tendsto (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal)
        atTop (𝓝 (innerRate m)) := by
    have hboundaryRate := hinnerBoundaryData m
    have hdensity : continuousBoundaryDensity 2
        (constantBoundary (-a + ε m)) (constantBoundary (1 - a - ε m)) =
          fun _ => (1 - 2 * ε m) ^ (-2 : ℝ) := by
      funext t
      simp only [continuousBoundaryDensity, constantBoundary,
        ContinuousMap.const_apply]
      congr 1
      ring
    have henergy :
        ∫ t : unitInterval, continuousBoundaryDensity 2
          (constantBoundary (-a + ε m))
          (constantBoundary (1 - a - ε m)) t ∂volume =
          (1 - 2 * ε m) ^ (-2 : ℝ) := by
      rw [hdensity]
      simp
    have hwidthPos : 0 < 1 - 2 * ε m := by
      linarith [hεa m, hεone m]
    have henergyInv :
        ∫ t : unitInterval, continuousBoundaryDensity 2
          (constantBoundary (-a + ε m))
          (constantBoundary (1 - a - ε m)) t ∂volume =
          ((1 - 2 * ε m) ^ 2)⁻¹ := by
      rw [henergy, Real.rpow_neg hwidthPos.le]
      exact congrArg (fun z : ℝ => z⁻¹)
        (Real.rpow_natCast (1 - 2 * ε m) 2)
    have hrateConstant : -(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν) *
        ((1 - 2 * ε m) ^ 2)⁻¹ =
        innerRate m := by
      dsimp [innerRate, c]
    have hboundaryRate' := hboundaryRate.2
    rw [henergyInv, hrateConstant] at hboundaryRate'
    simpa [hbaseSet, sourceRelativeConstantCorridorEvent, constantBoundary,
      innerRate, c] using hboundaryRate'
  have houterRate (m : ℕ) :
      Tendsto (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal)
        atTop (𝓝 (outerRate m)) := by
    have hboundaryRate := houterBoundaryData m
    have hdensity : continuousBoundaryDensity 2
        (constantBoundary (-a - ε m)) (constantBoundary (1 - a + ε m)) =
          fun _ => (1 + 2 * ε m) ^ (-2 : ℝ) := by
      funext t
      simp only [continuousBoundaryDensity, constantBoundary,
        ContinuousMap.const_apply]
      congr 1
      ring
    have henergy :
        ∫ t : unitInterval, continuousBoundaryDensity 2
          (constantBoundary (-a - ε m))
          (constantBoundary (1 - a + ε m)) t ∂volume =
          (1 + 2 * ε m) ^ (-2 : ℝ) := by
      rw [hdensity]
      simp
    have hwidthPos : 0 < 1 + 2 * ε m := by positivity
    have henergyInv :
        ∫ t : unitInterval, continuousBoundaryDensity 2
          (constantBoundary (-a - ε m))
          (constantBoundary (1 - a + ε m)) t ∂volume =
          ((1 + 2 * ε m) ^ 2)⁻¹ := by
      rw [henergy, Real.rpow_neg hwidthPos.le]
      exact congrArg (fun z : ℝ => z⁻¹)
        (Real.rpow_natCast (1 + 2 * ε m) 2)
    have hrateConstant : -(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν) *
        ((1 + 2 * ε m) ^ 2)⁻¹ =
        outerRate m := by
      dsimp [outerRate, c]
    have hboundaryRate' := hboundaryRate.2
    rw [henergyInv, hrateConstant] at hboundaryRate'
    simpa [hbaseSet, sourceRelativeConstantCorridorEvent, constantBoundary,
      outerRate, c] using hboundaryRate'
  have hinnerEvent (m n : ℕ) (hn : 0 < n) (hs : 0 < scale n) :
      hbaseSet (-a + ε m) (1 - a - ε m) n ⊆
        {increment | InHorizontalTube a (scale n) (n - 1) increment} := by
    simpa [hbaseSet] using
      (sourceRelativeConstantCorridor_subset_horizontalTube hn hs
        (by linarith [hεpos m]) (by linarith [hεpos m]))
  have houterEvent (m n : ℕ) (hn : 0 < n) (hs : 0 < scale n) :
      {increment | InHorizontalTube a (scale n) (n - 1) increment} ⊆
        hbaseSet (-a - ε m) (1 - a + ε m) n := by
    simpa [hbaseSet] using
      (horizontalTube_subset_sourceRelativeConstantCorridor hn hs ha.le haOne.le
        (by linarith [hεpos m]) (by linarith [hεpos m]))
  have hTubePositive : ∀ᶠ n : ℕ in atTop, 0 < (tubeProbability n).toReal := by
    filter_upwards [hvalid, hinnerPositive 0] with n hn hinner
    have hmeasure : iidSequenceLaw ν
        (hbaseSet (-a + ε 0) (1 - a - ε 0) n) ≤ tubeProbability n := by
      change iidSequenceLaw ν (hbaseSet (-a + ε 0) (1 - a - ε 0) n) ≤
        iidSequenceLaw ν {increment |
          InHorizontalTube a (scale n) (n - 1) increment}
      exact measure_mono (hinnerEvent 0 n hn.1 hn.2)
    have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
    exact lt_of_lt_of_le hinner hreal
  have hlogSqueeze (m : ℕ) : ∀ᶠ n : ℕ in atTop,
      (scale n) ^ 2 / (n : ℝ) * Real.log
          (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal ≤
        tubeRate n ∧
      tubeRate n ≤ (scale n) ^ 2 / (n : ℝ) * Real.log
          (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal := by
    filter_upwards [hvalid, hinnerPositive m, houterPositive m, hTubePositive]
      with n hn hinner houter htube
    have hinnerMeasure : iidSequenceLaw ν
        (hbaseSet (-a + ε m) (1 - a - ε m) n) ≤ tubeProbability n := by
      change iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n) ≤
        iidSequenceLaw ν {increment |
          InHorizontalTube a (scale n) (n - 1) increment}
      exact measure_mono (hinnerEvent m n hn.1 hn.2)
    have houterMeasure : tubeProbability n ≤ iidSequenceLaw ν
        (hbaseSet (-a - ε m) (1 - a + ε m) n) := by
      change iidSequenceLaw ν {increment |
          InHorizontalTube a (scale n) (n - 1) increment} ≤
        iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)
      exact measure_mono (houterEvent m n hn.1 hn.2)
    have hinnerReal := ENNReal.toReal_mono (measure_ne_top _ _) hinnerMeasure
    have houterReal := ENNReal.toReal_mono (measure_ne_top _ _) houterMeasure
    have hlogInner : Real.log
        (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal ≤
          Real.log (tubeProbability n).toReal :=
      Real.log_le_log hinner hinnerReal
    have hlogOuter : Real.log (tubeProbability n).toReal ≤
        Real.log (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal :=
      Real.log_le_log htube houterReal
    have hfactor : 0 ≤ (scale n) ^ 2 / (n : ℝ) := by positivity
    exact ⟨mul_le_mul_of_nonneg_left hlogInner hfactor,
      mul_le_mul_of_nonneg_left hlogOuter hfactor⟩
  have hrateLimit : Tendsto tubeRate atTop (𝓝 c) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    let η : ℝ := δ / 4
    have hη : 0 < η := by dsimp [η]; positivity
    have hrateNear : ∀ᶠ m : ℕ in atTop,
        |innerRate m - c| < η ∧ |outerRate m - c| < η := by
      filter_upwards [
        hinnerRateLimit.eventually (Metric.ball_mem_nhds c hη),
        houterRateLimit.eventually (Metric.ball_mem_nhds c hη)] with m hmI hmO
      exact ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hmI,
        by simpa [Metric.mem_ball, Real.dist_eq] using hmO⟩
    obtain ⟨m, hmRates⟩ := hrateNear.exists
    have hinnerNear : ∀ᶠ n : ℕ in atTop,
        |((scale n) ^ 2 / (n : ℝ) * Real.log
          (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal) -
            innerRate m| < η := by
      filter_upwards [
        hinnerRate m |>.eventually (Metric.ball_mem_nhds (innerRate m) hη)]
        with n hn
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    have houterNear : ∀ᶠ n : ℕ in atTop,
        |((scale n) ^ 2 / (n : ℝ) * Real.log
          (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal) -
            outerRate m| < η := by
      filter_upwards [
        houterRate m |>.eventually (Metric.ball_mem_nhds (outerRate m) hη)]
        with n hn
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    filter_upwards [hinnerNear, houterNear, hlogSqueeze m] with n hi ho hsqueeze
    have hi' := abs_lt.mp hi
    have ho' := abs_lt.mp ho
    have hmI := abs_lt.mp hmRates.1
    have hmO := abs_lt.mp hmRates.2
    have hbounds : c - δ < tubeRate n ∧ tubeRate n < c + δ := by
      constructor
      · linarith [hi'.1, hmI.1, hsqueeze.1, show 4 * η = δ by dsimp [η]; ring]
      · linarith [ho'.2, hmO.2, hsqueeze.2, show 4 * η = δ by dsimp [η]; ring]
    have hdist : -δ < tubeRate n - c ∧ tubeRate n - c < δ := by
      constructor <;> linarith [hbounds.1, hbounds.2]
    have hdist' : |tubeRate n - c| < δ := abs_lt.mpr hdist
    simpa [Metric.mem_ball, Real.dist_eq] using hdist'
  simpa [tubeRate, tubeProbability] using hrateLimit


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
