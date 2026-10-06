import Analysis.Asymptotics.RegularVariation.SlowScale
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale

open Filter ProbabilityTheory
open MeasureTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

example {f : ℝ → ℝ} {ρ : ℝ} {x r : ℕ → ℝ}
    (hreg : Asymptotics.IsRegularlyVaryingAtTop f ρ)
    (hx : Tendsto x atTop atTop)
    (hr : Tendsto r atTop (nhds 0))
    (hr_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ r n) :
    ∃ a : ℕ → ℝ, Monotone a ∧ Tendsto a atTop atTop ∧
      Tendsto (fun n => a n * r n) atTop (nhds 0) ∧
      Tendsto (fun n => (f (a n * x n) / f (x n)) / (a n ^ ρ))
        atTop (nhds 1) :=
  hreg.exists_tendsto_slowScale hx hr hr_nonneg

example {α : ℝ} {ν : Measure ℝ} {b a : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν b a)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    ∃ c : ℕ → ℝ, Monotone c ∧ Tendsto c atTop atTop ∧
      Tendsto (fun n => c n * (a n / b n)) atTop (nhds 0) ∧
      Tendsto (fun n =>
        (stableScaleTime α ν (c n * a n) / stableScaleTime α ν (a n)) /
          c n ^ α) atTop (nhds 1) :=
  IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier hscale hslow

example {α : ℝ} {ν : Measure ℝ} {b a : ℕ → ℝ} {P : ℕ → ℕ → Prop}
    (hscale : IsStableMogulskiiScale α ν b a)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hfixed : ∀ k, ∀ᶠ n : ℕ in atTop, P k n) :
    ∃ d : ℕ → ℕ, Monotone d ∧ Tendsto d atTop atTop ∧
      (∀ᶠ n : ℕ in atTop, P (d n + 1) n) ∧
      Tendsto (fun n => ((d n : ℝ) + 1) * (a n / b n)) atTop (nhds 0) ∧
      Tendsto (fun n =>
        (stableScaleTime α ν (((d n : ℝ) + 1) * a n) /
          stableScaleTime α ν (a n)) / (((d n : ℝ) + 1) ^ α))
        atTop (nhds 1) :=
  IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier_of_eventually
    hscale hslow hfixed

#print axioms Asymptotics.IsRegularlyVaryingAtTop.exists_tendsto_slowScale
#print axioms Asymptotics.IsRegularlyVaryingAtTop.exists_tendsto_slowScale_of_eventually
#print axioms IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier
#print axioms IsStableMogulskiiScale.exists_tendsto_slowStableScaleTime_multiplier_of_eventually
