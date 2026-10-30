/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Limit.FiniteHorizon
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Continuous
public import Probability.Process.Brownian.Scaling.FiniteHorizon
import Probability.ConvergenceInDistribution.Basic

/-!
# Finite-horizon polygonal random-walk paths

## Public declarations

- `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon_scaledBrownian`:
  for centered, unit-second-moment increments and every positive integer
  $m$, the path on $[0,m]$ converges to $t\mapsto\sqrt m B(t/m)$.
- `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon_brownian`:
  when $B$ is Brownian, the same finite-horizon limit has the projected law
  $P^m$.
- `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon`:
  for every $s\le m$ and positive integer $m$, restriction to $[0,s]$
  converges to the Brownian restriction on $[0,s]$.

The finite-horizon statement is the path-law form of the rescaling used to
apply Donsker's theorem to $Q_n\Pi_s^{-1}$ in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Section 3, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- With diffusive normalization, stretching the time interval by
`m` multiplies the unit-time path values by $\sqrt m$. -/
private lemma restrict_normalizedLinearContinuousPathUnbounded_sqrt
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (increment : ℕ → ℝ) :
    restrictPathTo (m : ℝ≥0)
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment) =
      rescaleUnitPath (m : ℝ≥0) (by exact_mod_cast hm)
        (Real.sqrt m)
        (normalizedLinearContinuousPathIcc
          (fun n => Real.sqrt n) (m * n) increment) := by
  have hscale : Real.sqrt (n : ℝ) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
  have hscaleMN : Real.sqrt ((m * n : ℕ) : ℝ) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by exact_mod_cast Nat.mul_pos hm hn)).ne'
  have hbase := restrict_normalizedLinearContinuousPathUnbounded_eq_rescaleUnitPath
    (fun n => Real.sqrt n) m n hm hscale hscaleMN increment
  have hamp : Real.sqrt ((m * n : ℕ) : ℝ) / Real.sqrt n =
      Real.sqrt m := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
    field_simp
  simpa only [hamp] using hbase

/-- Donsker's principle on an integer finite horizon, first expressed
with the time-rescaled unit-interval Brownian limit. -/
theorem tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon_scaledBrownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (m : ℕ) (hm : 0 < m) :
    TendstoInDistribution
      (fun n increment => restrictPathTo (m : ℝ≥0)
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment))
      atTop
      (fun ω => rescaleUnitPath (m : ℝ≥0) (by exact_mod_cast hm)
        (Real.sqrt m) (continuousunitIntervalPath B hcontinuous ω))
      (fun _ => iidSequenceLaw nu) P := by
  have hreindex : Tendsto (fun n : ℕ => m * n) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with n hn
    calc
      b ≤ n := hn
      _ = 1 * n := by simp
      _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hm)
  have hunit := tendstoInDistribution_normalizedLinearContinuousPath_brownian
    nu hcentered hsecondMoment hB hcontinuous hmeasurable
  have hscaled := (hunit.comp_tendsto hreindex).continuous_comp
    (continuous_rescaleUnitPath (m : ℝ≥0) (by exact_mod_cast hm)
      (Real.sqrt m))
  apply hscaled.congr_eventually
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply Filter.Eventually.of_forall
    intro increment
    exact (restrict_normalizedLinearContinuousPathUnbounded_sqrt
      m n hm hn increment).symm
  · intro n
    exact ((continuous_restrictPathTo (m : ℝ≥0)).measurable.comp
      (measurable_normalizedLinearContinuousPathUnbounded
        (fun n => Real.sqrt n) n)).aemeasurable

/-- The finite-horizon polygonal walk converges to the Brownian path
observed through time `m`; its limit law is the projected path law $P^m$. -/
theorem tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon_brownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (m : ℕ) (hm : 0 < m) :
    TendstoInDistribution
      (fun n increment => restrictPathTo (m : ℝ≥0)
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment))
      atTop
      (fun ω => restrictPathTo (m : ℝ≥0)
        (hB.continuousPathMap hmeasurable ω))
      (fun _ => iidSequenceLaw nu) P := by
  have hscaled :=
    tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon_scaledBrownian
      nu hcentered hsecondMoment hB.toIsPreBrownianReal
      hcontinuous hmeasurable m hm
  apply hscaled.congr_limit
  · exact (continuous_restrictPathTo (m : ℝ≥0)).measurable.comp
      (hB.measurable_continuousPathMap hmeasurable) |>.aemeasurable
  · have hlaw := hB.measure_rescaleUnitPath_eq_finiteHorizonPathLaw
      hcontinuous hmeasurable (m : ℝ≥0) (by exact_mod_cast hm)
    have hprojection :
        finiteHorizonPathLaw
          (P.map (hB.continuousPathMap hmeasurable)) (m : ℝ≥0) =
        P.map (fun ω => restrictPathTo (m : ℝ≥0)
          (hB.continuousPathMap hmeasurable ω)) := by
      rw [finiteHorizonPathLaw, Measure.map_map]
      · rfl
      · exact (continuous_restrictPathTo (m : ℝ≥0)).measurable
      · exact hB.measurable_continuousPathMap hmeasurable
    calc
      _ = finiteHorizonPathLaw
          (P.map (hB.continuousPathMap hmeasurable)) (m : ℝ≥0) := by
            simpa only [NNReal.coe_natCast] using hlaw
      _ = _ := hprojection

/-- Donsker's theorem on any finite horizon covered by a positive integer
horizon; successive path restrictions give the exact projected law $P^s$. -/
theorem tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (s : ℝ≥0) (m : ℕ) (hm : 0 < m) (hsm : s ≤ m) :
    TendstoInDistribution
      (fun n increment => restrictPathTo s
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment))
      atTop
      (fun ω => restrictPathTo s
        (hB.continuousPathMap hmeasurable ω))
      (fun _ => iidSequenceLaw nu) P := by
  have hwhole :=
    tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon_brownian
      nu hcentered hsecondMoment hB hcontinuous hmeasurable m hm
  have hrestricted := hwhole.continuous_comp
    (continuous_restrictFinitePathTo s (m : ℝ≥0) hsm)
  simpa only [Function.comp_def, restrictFinitePathTo_restrictPathTo]
    using hrestricted

end ProbabilityTheory.RandomWalk

end
