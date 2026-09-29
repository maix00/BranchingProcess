import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.UnitInterval
import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Skorokhod
import Probability.BranchingRandomWalk.Walk.FunctionalLimit.NormalizedStep
import Probability.Distributions.Stable.SmallDeviation

/-!
# `α = 2`: Donsker's theorem as the Gaussian case of the stable route

The stable route of Mogulskii's small-deviation theorem assumes that the càdlàg step paths normalized by the
norming `b n` converge in Skorokhod `J₁` to a limit process
(`IsNormalizedStepFunctionalLimit`). At `α = 2` that input
is not a new theorem: it is Donsker's invariance principle,
`tendstoInDistribution_normalizedStepCadlagPath_brownian`, and this module records that identification.

The second item is the formal interface between general finite-variance increments and the Brownian estimate.
Mogulskii's norming at `α = 2` solves `b n ^ 2 / L* (b n) = n` with `L*` the slowly varying function, while
Donsker's normalization is `√n`. Since `L* (u)` tends to the variance as `u → ∞`, the two normalizations are
asymptotically equal: `b n / √n → σ` with `σ ^ 2 = ∫ x ^ 2 ∂μ`. This is what lets the Gaussian specialization be
read off the general `α` statement instead of being proved separately.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- At `α = 2` the functional-limit input of the stable route is Donsker's
invariance principle for the normalized right-continuous step path. -/
theorem isStableFunctionalLimit_two
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0) (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω)) (hmeasurable : ∀ t, Measurable (B t)) :
    IsNormalizedStepFunctionalLimit nu (fun n => Real.sqrt n) P
      (Skorokhod.ofContinuousMap ∘ continuousunitIntervalPath B hcontinuous) :=
  tendstoInDistribution_normalizedStepCadlagPath_brownian
    nu hcentered hsecondMoment hB hcontinuous hmeasurable

end ProbabilityTheory.RandomWalk

namespace ProbabilityTheory

/-- At `α = 2` Mogulskii's norming satisfies `b n ^ 2 / n → σ ^ 2`, the variance of
the increment law. This is the identity `b n ^ 2 / L* (b n) = n` read together with
the convergence of the truncated second moment to the full second moment. -/
theorem IsStableNorming.tendsto_sq_div_nat
    {μ : Measure ℝ} (hμ : Integrable (fun x : ℝ => x ^ 2) μ)
    {b : ℕ → ℝ} (h : IsStableNorming 2 μ b) :
    Tendsto (fun n : ℕ => b n ^ 2 / (n : ℝ)) atTop (nhds (∫ x, x ^ 2 ∂μ)) := by
  have hnat : Tendsto (fun n : ℕ => truncatedSecondMoment μ (b n)) atTop
      (nhds (∫ x, x ^ 2 ∂μ)) :=
    (tendsto_truncatedSecondMoment μ hμ).comp h.2.1
  refine hnat.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hEq : b n ^ 2 / truncatedSecondMoment μ (b n) = (n : ℝ) := by
    simpa [stableSlowVariation_two] using h.2.2 n hn
  have hmem : truncatedSecondMoment μ (b n) ≠ 0 := by
    intro hzero
    rw [hzero, div_zero] at hEq
    exact hnpos.ne' hEq.symm
  have hmul : b n ^ 2 = (n : ℝ) * truncatedSecondMoment μ (b n) :=
    (div_eq_iff hmem).mp hEq
  rw [hmul, mul_div_cancel_left₀ _ hnpos.ne']

/-- The same statement in the normalization actually used by Donsker's theorem. -/
theorem IsStableNorming.tendsto_div_sqrt_nat
    {μ : Measure ℝ} (hμ : Integrable (fun x : ℝ => x ^ 2) μ)
    {b : ℕ → ℝ} (h : IsStableNorming 2 μ b) :
    Tendsto (fun n : ℕ => b n / Real.sqrt n) atTop
      (nhds (Real.sqrt (∫ x, x ^ 2 ∂μ))) := by
  have hsq := h.tendsto_sq_div_nat hμ
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (b n ^ 2 / (n : ℝ))) atTop
      (nhds (Real.sqrt (∫ x, x ^ 2 ∂μ))) :=
    (Real.continuous_sqrt.tendsto _).comp hsq
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbn : 0 < b n := h.1 n hn
  have hrewrite : b n ^ 2 / (n : ℝ) = (b n / Real.sqrt n) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hrewrite, Real.sqrt_sq
    (div_nonneg hbn.le (Real.sqrt_nonneg n))]

end ProbabilityTheory
