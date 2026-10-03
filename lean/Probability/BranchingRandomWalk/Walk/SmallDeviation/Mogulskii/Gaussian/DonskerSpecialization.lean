module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.UnitInterval
public import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Skorokhod
public import Probability.BranchingRandomWalk.Walk.FunctionalLimit.NormalizedStep
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Normalization

/-!
# `α = 2`: Donsker's theorem as the Gaussian case of the stable route

The stable route of Mogulskii's small-deviation theorem assumes that the
càdlàg step paths normalized by `b n` converge in Skorokhod `J₁` to a limit
process (`IsNormalizedStepFunctionalLimit`). At `α = 2`, Donsker's invariance
principle supplies this input through
`tendstoInDistribution_normalizedStepCadlagPath_brownian`.

The second result connects finite-variance increments with the Brownian
estimate. For increment law `ν`, `L*ν(u)` tends to `∫ x ^ 2 ∂ν`; together with
the stable norming condition this gives `b n / √n → σ`, where
`σ ^ 2 = ∫ x ^ 2 ∂ν`.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- At `α = 2` the functional-limit input of the stable route is Donsker's
invariance principle for the normalized right-continuous step path. -/
theorem isNormalizedStepFunctionalLimit_two
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

/-- The same statement in the normalization actually used by Donsker's theorem. -/
theorem IsStableNorming.tendsto_div_sqrt_nat
    {ν : Measure ℝ} (hν : Integrable (fun x : ℝ => x ^ 2) ν)
    {b : ℕ → ℝ} (h : IsStableNorming 2 ν b) :
    Tendsto (fun n : ℕ => b n / Real.sqrt n) atTop
      (nhds (Real.sqrt (∫ x, x ^ 2 ∂ν))) := by
  have hsq := h.tendsto_sq_div_nat hν
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (b n ^ 2 / (n : ℝ))) atTop
      (nhds (Real.sqrt (∫ x, x ^ 2 ∂ν))) :=
    (Real.continuous_sqrt.tendsto _).comp hsq
  refine hsqrt.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hbn : 0 < b n := h.1 n hn
  have hrewrite : b n ^ 2 / (n : ℝ) = (b n / Real.sqrt n) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hrewrite, Real.sqrt_sq
    (div_nonneg hbn.le (Real.sqrt_nonneg n))]

/-! The Gaussian truncated-variance limit belongs to this Mogulskii adapter:
the stable-distribution layer only needs the stability law itself. -/

/-- For a centered Gaussian stable law, Mogulskii's `L*` at exponent two
converges to the variance parameter. -/
theorem tendsto_stableSlowVariation_two_gaussianReal_zero (v : ℝ≥0) :
    Tendsto (stableSlowVariation 2 (gaussianReal 0 v)) Filter.atTop
      (nhds (v : ℝ)) := by
  have hintegrable : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) := by
    simpa [id] using (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hsecond : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = (v : ℝ) := by
    have hvariance : variance id (gaussianReal 0 v) = (v : ℝ) :=
      variance_id_gaussianReal
    rw [variance_of_integral_eq_zero measurable_id.aemeasurable (by simp)] at hvariance
    simpa [id] using hvariance
  have h := tendsto_truncatedSecondMoment (gaussianReal 0 v) hintegrable
  rw [hsecond] at h
  convert h using 1
  funext u
  exact stableSlowVariation_two _ _

end ProbabilityTheory
