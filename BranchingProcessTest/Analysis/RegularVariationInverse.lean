import Probability.Distributions.Stable.Attraction.Norming.Inverse

open Filter MeasureTheory
open scoped Topology

/-- The compact-uniform ratio API is available for monotone power functions. -/
example {ρ : ℝ} (hρ : 0 ≤ ρ) :
    TendstoUniformlyOn
      (fun x c : ℝ => (c * x) ^ ρ / x ^ ρ) (fun c => c ^ ρ)
      atTop (Set.Icc 1 2) := by
  have hmono : Asymptotics.IsEventuallyMonotoneAtTop (fun x : ℝ => x ^ ρ) := by
    refine ⟨0, ?_⟩
    intro x y hx hxy
    exact Real.rpow_le_rpow hx hxy hρ
  have hreg := Asymptotics.IsRegularlyVaryingAtTop.rpow ρ
  exact hreg.tendstoUniformlyOn_ratio_of_eventuallyMonotone
    hmono (by norm_num) (by norm_num)

example {f : ℝ → ℝ} {ρ r : ℝ} {x y : ℕ → ℝ}
    (hreg : Asymptotics.IsRegularlyVaryingAtTop f ρ)
    (hmono : Asymptotics.IsEventuallyMonotoneAtTop f)
    (hρ : 0 < ρ) (hr : 0 < r)
    (hx : Tendsto x atTop atTop) (hy : Tendsto y atTop atTop)
    (hvalue : Tendsto (fun n => f (y n) / f (x n)) atTop (nhds (r ^ ρ))) :
    Tendsto (fun n => y n / x n) atTop (nhds r) :=
  Asymptotics.IsRegularlyVaryingAtTop.tendsto_div_of_tendsto_value_ratio
    hreg hmono hρ hr hx hy hvalue

example {V : ℝ → ℝ} {β r : ℝ} {x y : ℕ → ℝ}
    (hV : Asymptotics.IsRegularlyVaryingAtTop V β)
    (hVmono : Asymptotics.IsEventuallyMonotoneAtTop V)
    (hβ : 0 ≤ β) (hβ₂ : β < 2) (hr : 0 < r)
    (hx : Tendsto x atTop atTop) (hy : Tendsto y atTop atTop)
    (hquotient : Tendsto
      (fun n => y n ^ 2 / V (y n) / (x n ^ 2 / V (x n))) atTop
      (nhds (r ^ (2 - β)))) :
    Tendsto (fun n => y n / x n) atTop (nhds r) :=
  Asymptotics.IsRegularlyVaryingAtTop.tendsto_div_of_tendsto_squareQuotient_ratio
    hV hVmono hβ hβ₂ hr hx hy hquotient

example {α : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ} {constant : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (ProbabilityTheory.stableSlowVariation α ν))
    (hnorm : ProbabilityTheory.IsStableNorming α ν normalization)
    (hscale : Tendsto scale atTop atTop) (hconstant : 0 < constant) :
    Tendsto
      (fun n => normalization
        (Asymptotics.floorBlockLength
          (fun n => constant * ProbabilityTheory.stableScaleTime α ν (scale n)) n) /
        scale n)
      atTop (nhds (constant ^ (1 / α))) :=
  ProbabilityTheory.IsStableNorming.tendsto_floorBlock_normalization_div_scale
    hα₀ (le_of_lt hα₂) hslow hnorm hscale hconstant

example {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ} {constant : ℝ}
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (ProbabilityTheory.truncatedSecondMoment ν))
    (hnorm : ProbabilityTheory.IsStableNorming 2 ν normalization)
    (hscale : Tendsto scale atTop atTop) (hconstant : 0 < constant) :
    Tendsto
      (fun n => normalization
        (Asymptotics.floorBlockLength
          (fun n => constant * ProbabilityTheory.stableScaleTime 2 ν (scale n)) n) /
        scale n)
      atTop (nhds (constant ^ (1 / (2 : ℝ)))) := by
  have hslow' : Asymptotics.IsSlowlyVaryingAtTop
      (ProbabilityTheory.stableSlowVariation 2 ν) := by
    have hEq : ProbabilityTheory.stableSlowVariation 2 ν =
        ProbabilityTheory.truncatedSecondMoment ν := by
      funext u
      exact ProbabilityTheory.stableSlowVariation_two ν u
    rw [hEq]
    exact hslow
  simpa using
    ProbabilityTheory.IsStableNorming.tendsto_floorBlock_normalization_div_scale
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 2)
      hslow' hnorm hscale hconstant

#print axioms Asymptotics.IsRegularlyVaryingAtTop.tendstoUniformlyOn_ratio_of_eventuallyMonotone
#print axioms Asymptotics.IsRegularlyVaryingAtTop.tendsto_div_of_tendsto_value_ratio
#print axioms Asymptotics.IsRegularlyVaryingAtTop.tendsto_div_of_tendsto_squareQuotient_ratio
#print axioms ProbabilityTheory.truncatedSecondMoment_isRegularlyVarying_of_stableSlowVariation
#print axioms ProbabilityTheory.stableScaleTime_tendsto_atTop_of_stableSlowVariation
#print axioms ProbabilityTheory.IsStableNorming.tendsto_floorBlock_normalization_div_scale
