/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Capacity
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.FiniteVariance

/-!
# Positive probability for the first right-tail corridor

Finite variance supplies a quantitative spine-corridor lower bound along the
the logarithmic first-stage horizon.  A slightly narrower terminal window
absorbs the floor in `floor ((log N)^(5/2))` and lies inside the corridor used
by the first-stage population estimate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

private theorem tendsto_rightTailPositiveAFirstCutoff_twoFifths_div_log
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => logarithmicSmallDeviationScale
      (rightTailPositiveAFirstCutoff N n) /
        logarithmOfSampleSize N n) atTop (𝓝 1) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let arg : ℕ → ℝ := fun n => L n ^ ((5 : ℝ) / 2)
  let cutoff : ℕ → ℝ := fun n => (rightTailPositiveAFirstCutoff N n : ℝ)
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have harg : Tendsto arg atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 2)).comp hL
  have hfloor : Tendsto (fun n => cutoff n / arg n) atTop (𝓝 1) := by
    have h := (tendsto_nat_floor_div_atTop.comp harg)
    have heq : (fun n => cutoff n / arg n) =ᶠ[atTop]
        fun n => (Nat.floor (arg n) : ℝ) / arg n := by
      filter_upwards [] with n
      simp [cutoff, arg, L, rightTailPositiveAFirstCutoff,
        logarithmOfSampleSize]
    exact h.congr' heq.symm
  have hpower : Tendsto (fun n => (cutoff n / arg n) ^ ((2 : ℝ) / 5))
      atTop (𝓝 1) := by
    simpa using hfloor.rpow_const
      (x := (1 : ℝ)) (p := (2 : ℝ) / 5) (Or.inl (by norm_num))
  have hratio : Tendsto (fun n => cutoff n ^ ((2 : ℝ) / 5) / L n)
      atTop (𝓝 1) := by
    have heq : (fun n => cutoff n ^ ((2 : ℝ) / 5) / L n) =ᶠ[atTop]
        fun n => (cutoff n / arg n) ^ ((2 : ℝ) / 5) := by
      filter_upwards [hL.eventually_gt_atTop 0] with n hn
      have hargPos : 0 < arg n := Real.rpow_pos_of_pos hn _
      have hargPow : arg n ^ ((2 : ℝ) / 5) = L n := by
        dsimp [arg]
        rw [← Real.rpow_mul hn.le]
        norm_num [Real.rpow_one]
      rw [Real.div_rpow (by positivity) hargPos.le, hargPow]
    exact hpower.congr' heq.symm
  simpa [cutoff, logarithmicSmallDeviationScale] using hratio

private theorem logarithmicSmallDeviationScale_mul_isMogulskiiScale
    {c : ℝ} (hc : 0 < c) :
    IsMogulskiiScale
      (fun k : ℕ => c * logarithmicSmallDeviationScale k) := by
  have hbase : IsMogulskiiScale logarithmicSmallDeviationScale :=
    logarithmicSmallDeviationScale_isSmallDeviationScale
  refine ⟨?_, ?_⟩
  · exact hbase.1.const_mul_atTop hc
  · have hmul :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c)).mul hbase.2
    have heq : (fun k : ℕ =>
        c * logarithmicSmallDeviationScale k / Real.sqrt (k : ℝ)) =ᶠ[atTop]
        fun k => c *
          (logarithmicSmallDeviationScale k / Real.sqrt (k : ℝ)) := by
      filter_upwards [] with k
      ring
    simpa only [mul_zero] using hmul.congr' heq.symm

/-- Explicit finite-variance lower bound for the first-stage tilted-spine
corridor. The scale is `v/2` times the logarithmic small-deviation scale;
the extra margins absorb the floor in the first-stage horizon. -/
noncomputable def rightTailPositiveASpineCorridorLowerBound
    (ν : Measure ℝ) (b v C amplitude : ℝ) (q : ℝ≥0∞)
    (horizon : ℕ) : ℝ≥0∞ := by
  let scale : ℕ → ℝ := fun k => (v / 2) * logarithmicSmallDeviationScale k
  let ratio : ℝ := (b - v / 4) / (v / 2)
  exact ENNReal.ofReal (Real.exp
      ((C / ((ratio / 2 - 13 / 60) ^ (2 : ℝ)) - 1) * amplitude ^ (2 : ℝ))) ^
      (Asymptotics.balancedBlockCount
        (ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceBridgeLength
          scale horizon -
          stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale horizon)
        (stableBlockLength 2 ν (amplitude ^ (2 : ℝ)) scale horizon) + 1) *
      (q / (ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceEntranceLength
        scale horizon : ℝ≥0∞))

/-- For the first cutoff `floor (log N)^(5/2)`, finite variance implies
strict positivity of the tilted-spine mass of the fixed tube used by the
right-tail first stage.  The proof uses a narrower tube with endpoint width
`v/2`; the factor `exp(-O(sqrt(log N)))` from the finite-variance corridor
estimate is retained in the lower bound and is enough to certify positivity. -/
theorem eventually_rightTailPositiveA_spineCorridor_lowerBound_of_centeredSecondMoment
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Combinatorics.Branching.Step ℕ ℝ))
    [IsProbabilityMeasure μ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma b v : ℝ}
    (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (hb : 0 < b) (hv : 0 < v) (hvb : v < b) :
    ∃ C : ℝ, C < 0 ∧ ∃ q : ℝ≥0∞, 0 < q ∧
      ∃ amplitude : ℝ, 0 < amplitude ∧ ∀ᶠ n : ℕ in atTop,
        rightTailPositiveASpineCorridorLowerBound ν b v C amplitude q
          (rightTailPositiveAFirstCutoff N n) ≤
          (tiltedIncrementFieldLaw realPotential μ)
        {increment : ℕ → ℝ |
          RandomWalk.history (rightTailPositiveAFirstCutoff N n) 0 increment ∈
            affineCorridorThrough (rightTailPositiveAFirstCutoff N n)
              (-b * logarithmOfSampleSize N n) 0
              (b * logarithmOfSampleSize N n)
              ((-b + v) * logarithmOfSampleSize N n)} := by
  let ell : ℕ → ℕ := rightTailPositiveAFirstCutoff N
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let v₀ : ℝ := v / 2
  let b₀ : ℝ := b - v / 4
  let ratio : ℝ := b₀ / v₀
  let scale : ℕ → ℝ := fun k => v₀ * logarithmicSmallDeviationScale k
  have hv₀ : 0 < v₀ := by dsimp [v₀]; linarith
  have hb₀ : 0 < b₀ := by dsimp [b₀]; linarith
  have hb₀v₀ : v₀ < b₀ := by dsimp [v₀, b₀]; linarith
  have hratio : 1 < ratio := by
    dsimp [ratio]
    exact (lt_div_iff₀ hv₀).2 (by dsimp [b₀, v₀]; linarith)
  have hscale : IsMogulskiiScale scale := by
    simpa [scale] using logarithmicSmallDeviationScale_mul_isMogulskiiScale hv₀
  have hcutoffPow := tendsto_rightTailPositiveAFirstCutoff_twoFifths_div_log hN
  have hbottomRatio : Tendsto (fun n => b₀ *
      (logarithmicSmallDeviationScale (ell n) / L n)) atTop (𝓝 b₀) := by
    simpa using hcutoffPow.const_mul b₀
  have hupperRatio : Tendsto (fun n => (-b₀ + v₀) *
      (logarithmicSmallDeviationScale (ell n) / L n)) atTop
      (𝓝 (-b₀ + v₀)) := by
    simpa using hcutoffPow.const_mul (-b₀ + v₀)
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  obtain ⟨C, hC, q, hq, amplitude, hamplitude, n₀, hcorridor⟩ :=
    ProbabilityTheory.BranchingRandomWalk.Spine.exists_eventually_tiltedIncrementFieldLaw_affineCorridor_lowerBound_of_centeredSecondMoment
      realPotential μ hν hνMoment hsigma hscale ratio hratio
  refine ⟨C, hC, q, hq, amplitude, hamplitude, ?_⟩
  have hell : Tendsto ell atTop atTop := by
    simpa [ell] using tendsto_rightTailPositiveAFirstCutoff_atTop hN
  have hscaleAtCutoff : Tendsto (fun n => scale (ell n)) atTop atTop :=
    hscale.1.comp hell
  have hlowerTube : ∀ᶠ n : ℕ in atTop,
      -b₀ * logarithmicSmallDeviationScale (ell n) ≥ -b * L n := by
    have hmargin : b₀ < b := by dsimp [b₀]; linarith
    filter_upwards [hbottomRatio.eventually (Iio_mem_nhds hmargin),
      hL.eventually_gt_atTop 0] with n hn hLn
    have hprod := mul_lt_mul_of_pos_right hn hLn
    have heq : b₀ *
        (logarithmicSmallDeviationScale (ell n) / L n) * L n =
          b₀ * logarithmicSmallDeviationScale (ell n) := by
      field_simp [ne_of_gt hLn]
    rw [heq] at hprod
    linarith
  have hupperTube : ∀ᶠ n : ℕ in atTop,
      (-b₀ + v₀) * logarithmicSmallDeviationScale (ell n) ≤
        (-b + v) * L n := by
    have hmargin : -b₀ + v₀ < -b + v := by
      dsimp [b₀, v₀]
      linarith
    filter_upwards [hupperRatio.eventually (Iio_mem_nhds hmargin),
      hL.eventually_gt_atTop 0] with n hn hLn
    have hprod := mul_lt_mul_of_pos_right hn hLn
    have heq : (-b₀ + v₀) *
        (logarithmicSmallDeviationScale (ell n) / L n) * L n =
          (-b₀ + v₀) * logarithmicSmallDeviationScale (ell n) := by
      field_simp [ne_of_gt hLn]
    rw [heq] at hprod
    exact le_of_lt hprod
  have hindex : ∀ᶠ n : ℕ in atTop, n₀ ≤ ell n :=
    hell.eventually_ge_atTop n₀
  filter_upwards [hindex, hlowerTube, hupperTube]
    with n hnIndex hnLower hnUpper
  have hquant := hcorridor (ell n) hnIndex
  let d := logarithmicSmallDeviationScale (ell n)
  let source : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history (ell n) 0 increment ∈
      affineCorridorThrough (ell n) (-ratio * scale (ell n)) 0
        (ratio * scale (ell n)) ((-ratio + 1) * scale (ell n))}
  let target : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history (ell n) 0 increment ∈
      affineCorridorThrough (ell n) (-b * L n) 0 (b * L n)
        ((-b + v) * L n)}
  have hsourceSubset : source ⊆ target := by
    intro increment hinc
    change RandomWalk.history (ell n) 0 increment ∈
      affineCorridorThrough (ell n) (-ratio * scale (ell n)) 0
        (ratio * scale (ell n)) ((-ratio + 1) * scale (ell n)) at hinc
    change RandomWalk.history (ell n) 0 increment ∈
      affineCorridorThrough (ell n) (-b * L n) 0 (b * L n)
        ((-b + v) * L n)
    simp only [affineCorridorThrough, Set.mem_setOf_eq,
      zero_mul, add_zero] at hinc ⊢
    have hsourceWidth : -ratio * scale (ell n) +
        ratio * scale (ell n) = 0 := by ring
    have htargetWidth : -b * L n + b * L n = 0 := by ring
    rw [hsourceWidth] at hinc
    rw [htargetWidth]
    have hbottom : -ratio * scale (ell n) = -b₀ * d := by
      dsimp [ratio, scale, v₀, b₀, d]
      unfold logarithmicSmallDeviationScale
      field_simp
    have htop : (-ratio + 1) * scale (ell n) = (-b₀ + v₀) * d := by
      dsimp [ratio, scale, v₀, b₀, d]
      unfold logarithmicSmallDeviationScale
      field_simp
    rw [hbottom, htop] at hinc
    constructor
    · intro k
      rcases hinc.1 k with ⟨hlo, hhi⟩
      exact ⟨hnLower.trans hlo, hhi⟩
    · exact hinc.2.trans hnUpper
  have htargetBound : rightTailPositiveASpineCorridorLowerBound ν b v C
      amplitude q (ell n) ≤ (tiltedIncrementFieldLaw realPotential μ) target := by
    simpa [rightTailPositiveASpineCorridorLowerBound, source, target,
      scale, ratio, v₀, b₀] using hquant.trans (measure_mono hsourceSubset)
  simpa only [target, L, ell] using htargetBound

private theorem rightTailPositiveASpineCorridorLowerBound_pos
    (ν : Measure ℝ) (b v C amplitude : ℝ) (q : ℝ≥0∞)
    (hq : 0 < q) (horizon : ℕ) :
    0 < rightTailPositiveASpineCorridorLowerBound ν b v C amplitude q horizon := by
  dsimp [rightTailPositiveASpineCorridorLowerBound]
  have hbase : 0 < ENNReal.ofReal (Real.exp
      ((C / (((b - v / 4) / (v / 2) / 2 - 13 / 60) ^ (2 : ℝ)) - 1) *
        amplitude ^ (2 : ℝ))) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.exp_pos _
  have hpow := ENNReal.pow_pos hbase
    (Asymptotics.balancedBlockCount
      (ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceBridgeLength
        (fun k => (v / 2) * logarithmicSmallDeviationScale k) horizon -
        stableBlockLength 2 ν (amplitude ^ (2 : ℝ))
          (fun k => (v / 2) * logarithmicSmallDeviationScale k) horizon)
      (stableBlockLength 2 ν (amplitude ^ (2 : ℝ))
        (fun k => (v / 2) * logarithmicSmallDeviationScale k) horizon) + 1)
  have hdiv := ENNReal.div_pos (ne_of_gt hq)
    (by finiteness :
      (ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteVarianceEntranceLength
        (fun k => (v / 2) * logarithmicSmallDeviationScale k) horizon :
        ℝ≥0∞) ≠ ∞)
  exact ENNReal.mul_pos hpow.ne' hdiv.ne'

/-- Positivity follows from the explicit entrance and bridge lower bound. -/
theorem eventually_rightTailPositiveA_spineCorridor_pos_of_centeredSecondMoment
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (μ : Measure (Combinatorics.Branching.Step ℕ ℝ))
    [IsProbabilityMeasure μ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma b v : ℝ}
    (hνMoment : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) (hb : 0 < b) (hv : 0 < v) (hvb : v < b) :
    ∀ᶠ n : ℕ in atTop,
      0 < (tiltedIncrementFieldLaw realPotential μ)
        {increment : ℕ → ℝ |
          RandomWalk.history (rightTailPositiveAFirstCutoff N n) 0 increment ∈
            affineCorridorThrough (rightTailPositiveAFirstCutoff N n)
              (-b * logarithmOfSampleSize N n) 0
              (b * logarithmOfSampleSize N n)
              ((-b + v) * logarithmOfSampleSize N n)} := by
  obtain ⟨C, _hC, q, hq, amplitude, _hamplitude, hlower⟩ :=
    eventually_rightTailPositiveA_spineCorridor_lowerBound_of_centeredSecondMoment
      hN μ ν hν hνMoment hsigma hb hv hvb
  filter_upwards [hlower] with n hn
  have hboundPos := rightTailPositiveASpineCorridorLowerBound_pos
    ν b v C amplitude q hq (rightTailPositiveAFirstCutoff N n)
  exact hboundPos.trans_le hn

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
