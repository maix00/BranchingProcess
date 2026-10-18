/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Scaling.FiniteHorizon
public import Probability.Process.RandomWalk.Path.Interpolation.Limit.Unbounded
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Continuous
public import Probability.Process.Brownian.Scaling.FiniteHorizon

/-!
# Finite-horizon polygonal random-walk paths

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.restrict_normalizedLinearContinuousPathUnbounded_eq_rescaleUnitPath`:
  on the interval $[0,m]$, the normalized polygonal walk of mesh
  $1/n$ is the time-rescaled first-$mn$-increment path on $[0,1]$,
  with amplitude factor $a_{mn}/a_n$.
- `ProbabilityTheory.RandomWalk.restrict_normalizedLinearContinuousPathUnbounded_sqrt`:
  for $a_n=\sqrt n$, the amplitude factor is $\sqrt m$.
- `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon_scaledBrownian`:
  for each positive integer $m$, the path on $[0,m]$ converges
  to the time-amplitude rescaling $t\mapsto\sqrt m B(t/m)$.
- `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon_brownian`:
  the same finite-horizon limit has the projected Brownian law $P^m$.
- `ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon`:
  for every finite $s\le m$ and positive integer $m$, the path restricted
  to $[0,s]$ converges to the Brownian restriction on $[0,s]$.

This deterministic identity is the path-level step for applying
Donsker's theorem to $Q_n\Pi_s^{-1}$ in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Section 3, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Finite-horizon restriction of the whole-time polygonal path is
exactly a rescaled unit-time polygonal path with the corresponding
number of increments. -/
theorem restrict_normalizedLinearContinuousPathUnbounded_eq_rescaleUnitPath
    (scale : ℕ → ℝ) (m n : ℕ) (hm : 0 < m)
    (hscale : scale n ≠ 0) (hscaleMN : scale (m * n) ≠ 0)
    (increment : ℕ → ℝ) :
    restrictPathTo (m : ℝ≥0)
        (normalizedLinearContinuousPathUnbounded scale n increment) =
      rescaleUnitPath (m : ℝ≥0) (by exact_mod_cast hm)
        (scale (m * n) / scale n)
        (normalizedLinearContinuousPathIcc scale (m * n) increment) := by
  ext t
  let u : unitInterval := unitTimeOfFiniteTime (m : ℝ≥0)
    (by exact_mod_cast hm) t
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have harg : ((m * n : ℕ) : ℝ) * (u : ℝ) = (n : ℝ) * (t.1 : ℝ) := by
    change ((m * n : ℕ) : ℝ) * ((t.1 : ℝ) / (m : ℝ)) =
      (n : ℝ) * (t.1 : ℝ)
    push_cast
    field_simp
  have hcap : (n : ℝ) * (t.1 : ℝ) ≤ (m * n : ℕ) := by
    have ht : (t.1 : ℝ) ≤ m := NNReal.coe_le_coe.mpr t.property.2
    calc
      (n : ℝ) * (t.1 : ℝ) ≤ (n : ℝ) * m :=
        mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
      _ = (m * n : ℕ) := by push_cast; ring
  have hweights (i : ℕ) :
      linearIncrementWeight (m * n) i (u : ℝ) =
        linearIncrementWeight n i (t.1 : ℝ) := by
    unfold linearIncrementWeight
    rw [harg]
  have hsum :
      (∑ i ∈ Finset.range (m * n),
        linearIncrementWeight (m * n) i (u : ℝ) * increment i) =
      ∑ i ∈ Finset.range (m * n),
        linearIncrementWeight n i (t.1 : ℝ) * increment i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hweights]
  change normalizedLinearPathUnbounded scale n increment t.1 =
    (scale (m * n) / scale n) *
      normalizedLinearPath scale (m * n) increment u
  rw [normalizedLinearPathUnbounded_eq_sum_range
    scale n increment t.1 (m * n) hcap]
  unfold normalizedLinearPath
  rw [hsum]
  field_simp

/-- With diffusive normalization, stretching the time interval by
`m` multiplies the unit-time path values by $\sqrt m$. -/
theorem restrict_normalizedLinearContinuousPathUnbounded_sqrt
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
