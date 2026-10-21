/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Analysis.SpecialFunctions.Trigonometric.LogAsymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Asymptotics of the symmetric-walk ground-state eigenvalue

The public spectral limits are:

* `tendsto_sq_mul_log_cos_pi_div`:
  $L^2\log\cos(\pi/L)\to-\pi^2/2$ as $L\to\infty$.
* `tendsto_log_sin_pi_div_add_log`:
  $\log\sin(\pi/L)+\log L\to\log\pi$ as $L\to\infty$.
-/

open Filter Set
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The logarithm of the principal Dirichlet eigenvalue has the exact
`π² / 2` diffusive-scale asymptotic used in the symmetric small-ball
estimate. -/
theorem tendsto_sq_mul_log_cos_pi_div :
    Tendsto (fun length : ℝ =>
      length ^ 2 * Real.log (Real.cos (Real.pi / length)))
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
  have hzero : Tendsto (fun length : ℝ => Real.pi / length) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hpunc : Tendsto (fun length : ℝ => Real.pi / length)
      atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with length hlength
    simp [Real.pi_ne_zero, hlength.ne']
  have h := (Real.tendsto_log_cos_div_sq.comp hpunc).const_mul (Real.pi ^ 2)
  have hbase : Tendsto (fun length : ℝ => Real.pi ^ 2 *
      (Real.log (Real.cos (Real.pi / length)) / (Real.pi / length) ^ 2))
      atTop (𝓝 (Real.pi ^ 2 * (-1 / 2 : ℝ))) := by
    simpa only [Function.comp_apply] using h
  have h' : Tendsto (fun length : ℝ => Real.pi ^ 2 *
      (Real.log (Real.cos (Real.pi / length)) / (Real.pi / length) ^ 2))
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
    have heq : Real.pi ^ 2 * (-1 / 2 : ℝ) = -(Real.pi ^ 2) / 2 := by ring
    rw [← heq]
    exact hbase
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with length hlength
  field_simp [Real.pi_ne_zero, hlength.ne']

/-- The endpoint sine weight is asymptotic to `π / length` on the logarithmic
scale.  This identifies exactly the prefactor lost by the elementary
ground-state upper bound. -/
theorem tendsto_log_sin_pi_div_add_log :
    Tendsto (fun length : ℝ =>
      Real.log (Real.sin (Real.pi / length)) + Real.log length)
      atTop (𝓝 (Real.log Real.pi)) := by
  have hzero : Tendsto (fun length : ℝ => Real.pi / length)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hpunc : Tendsto (fun length : ℝ => Real.pi / length)
      atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hzero, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with length hlength
    simp [Real.pi_ne_zero, hlength.ne']
  have hratio : Tendsto (fun length : ℝ =>
      Real.sin (Real.pi / length) / (Real.pi / length))
      atTop (𝓝 1) := by
    convert Real.tendsto_sin_div_nhdsNE_zero.comp hpunc using 1
    funext length
    rfl
  have hlogRatio : Tendsto (fun length : ℝ =>
      Real.log (Real.sin (Real.pi / length) / (Real.pi / length)))
      atTop (𝓝 0) := by
    have hlog : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact hlog.comp hratio
  have htarget := hlogRatio.add_const (Real.log Real.pi)
  have heq : (fun length : ℝ =>
      Real.log (Real.sin (Real.pi / length) / (Real.pi / length)) +
        Real.log Real.pi) =ᶠ[atTop]
      (fun length : ℝ =>
        Real.log (Real.sin (Real.pi / length)) + Real.log length) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with length hlength
    have hlengthPos : 0 < length := zero_lt_one.trans hlength
    have hzPos : 0 < Real.pi / length := div_pos Real.pi_pos hlengthPos
    have hzLtPi : Real.pi / length < Real.pi := by
      exact (div_lt_iff₀ hlengthPos).2 (by
        nlinarith [Real.pi_pos])
    have hsinPos : 0 < Real.sin (Real.pi / length) :=
      Real.sin_pos_of_pos_of_lt_pi hzPos hzLtPi
    rw [← Real.log_mul hsinPos.ne' hlengthPos.ne',
      ← Real.log_mul (div_pos hsinPos hzPos).ne' Real.pi_ne_zero]
    congr 1
    field_simp [Real.pi_ne_zero, hlengthPos.ne']
  simpa only [zero_add] using htarget.congr' heq

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
