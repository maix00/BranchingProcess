import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Asymptotics of the symmetric-walk ground-state eigenvalue
-/

open Filter Set
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii

theorem tendsto_sin_div_self :
    Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  simpa [div_eq_inv_mul, mul_comm] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

theorem tendsto_tan_div_self :
    Tendsto (fun x : ℝ => Real.tan x / x) (𝓝[≠] 0) (𝓝 1) := by
  have hcos : Tendsto Real.cos (𝓝[≠] 0) (𝓝 1) := by
    have hc : Tendsto Real.cos (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa using Real.continuous_cos.tendsto 0
    exact tendsto_nhdsWithin_of_tendsto_nhds hc
  convert tendsto_sin_div_self.div hcos one_ne_zero using 1
  · funext x
    rw [Real.tan_eq_sin_div_cos]
    simp only [Pi.div_apply, div_div]
    rw [mul_comm]
  · norm_num

/-- The local logarithmic asymptotic which produces the `1 / 2` in the
small-deviation constant. -/
theorem tendsto_log_cos_div_sq :
    Tendsto (fun x : ℝ => Real.log (Real.cos x) / x ^ 2)
      (𝓝[≠] 0) (𝓝 (-1 / 2 : ℝ)) := by
  apply HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun x => -Real.tan x) (g' := fun x => 2 * x)
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds
        (Real.continuous_cos.continuousAt.eventually_ne (by norm_num : Real.cos 0 ≠ 0))] with x hx
    convert (Real.hasDerivAt_cos x).log hx using 1
    rw [Real.tan_eq_sin_div_cos, neg_div]
  · exact Eventually.of_forall fun x => by simpa using (hasDerivAt_pow 2 x)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  · have hc : Tendsto Real.cos (𝓝 (0 : ℝ)) (𝓝 1) := by
      simpa using Real.continuous_cos.tendsto 0
    have hl : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
      simpa using (Real.continuousAt_log one_ne_zero).tendsto
    exact tendsto_nhdsWithin_of_tendsto_nhds (hl.comp hc)
  · exact tendsto_nhdsWithin_of_tendsto_nhds <| by
      simpa using (continuous_pow 2).tendsto (0 : ℝ)
  · have h := tendsto_tan_div_self.const_mul (-1 / 2 : ℝ)
    convert h using 1
    · funext x
      field_simp
    · norm_num

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
  have h := (tendsto_log_cos_div_sq.comp hpunc).const_mul (Real.pi ^ 2)
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
    convert tendsto_sin_div_self.comp hpunc using 1
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

end ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii
