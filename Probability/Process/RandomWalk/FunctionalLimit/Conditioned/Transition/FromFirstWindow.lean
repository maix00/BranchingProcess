/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.Limit
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.Event

/-!
# Transition estimate from the centered first-window limit

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_transitionConditionalProbability_ge_of_firstWindowSupport`:
  for centered unit-variance increments, if the Brownian first-window
  path law has $t\mapsto7t/16$ in its support and
  $\Delta_n/\sqrt{n+1}\to1$, then some $q>0$ satisfies
  $\mathbb P(D_{n+1,\Delta_n}\mid C_{n+1})\ge q$ eventually.

The conditional path convergence is proved from the centered first-window
construction of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098, Theorem 3.2. The support point is the remaining
Brownian-meander identification used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.5, and Appendix A.2, Lemma A.7.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

/-- The conditioned path limit supplies the transition estimate once the
support of its explicit Brownian first-window limit is established. -/
theorem exists_eventually_transitionConditionalProbability_ge_of_firstWindowSupport
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hsupport : Skorokhod.straightPath (7 / 16 : ℝ) ∈
      (P.map (fun ω => Skorokhod.ofContinuousMap
        (restrictPathToUnitInterval
          (centeredFirstWindowShift
            (hB.continuousPathMap hmeasurable ω))))).support)
    {width : ℕ → ℝ} (hwidth : ∀ n, 0 ≤ width n)
    (hratio : Tendsto (fun n => width n / Real.sqrt (n + 1))
      atTop (𝓝 1)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν (n + 1)
        (nonnegativeTransitionEvent (n + 1) (width n)) := by
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment
      ν hν (n + 1)
  have hlimit : TendstoInDistribution
      (fun n increment => normalizedLinearCadlagPathIcc
        (fun j => (1 : ℝ) * Real.sqrt j) (n + 1) increment)
      atTop
      (fun ω => Skorokhod.ofContinuousMap
        (restrictPathToUnitInterval
          (centeredFirstWindowShift
            (hB.continuousPathMap hmeasurable ω))))
      (fun n => survivalConditionedLaw ν (n + 1)) P := by
    simpa only [one_mul, normalizedLinearCadlagPathIcc] using
      (tendstoInDistribution_survivalConditionedInterpolatedCadlagPath
        ν hν hB hcontinuous hmeasurable)
  exact exists_eventually_interpolatedTransitionConditionalProbability_ge
    (sigma := 1) (rho := rho) (by norm_num) hrho hrhoSmall
    hlimit
    (by simpa only [div_one] using hsupport) hwidth hratio

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
