/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.MeanderIdentification
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.MeanderVariance
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.TransitionFromFirstWindow
public import Probability.Process.Brownian.Meander.LastZeroSupport

/-!
# Conditional transition probability from Brownian meander

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_transitionConditionalProbability_ge_of_unitVariance`:
  if $S$ is a centered unit-variance walk and $\Delta_n/\sqrt{n+1}\to1$,
  then for some $q>0$,
  $\mathbb P(D_{n+1,\Delta_n}\mid S_1,\ldots,S_{n+1}\ge0)\ge q$
  eventually.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_transitionConditionalProbability_ge_of_centeredSecondMoment`:
  the same conclusion for variance $\sigma^2>0$, with paths normalized
  by $\sigma\sqrt n$.

This is the conditioned Brownian-meander transition step in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, used in the proof of Lemma 3.5. The functional limit follows
Erwin Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485,
Theorem 3.2; its identification with the terminal excursion is due to
Donald L. Iglehart, *Functional Central Limit Theorems for Random Walks
Conditioned to Stay Positive*, Ann. Probab. 2(4) (1974), 608--619,
Section 3.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

/-- The conditioned unit-variance transition estimate with the meander
limit and support established from Brownian motion. -/
theorem exists_eventually_transitionConditionalProbability_ge_of_unitVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    {width : ℕ → ℝ} (hwidth : ∀ n, 0 ≤ width n)
    (hratio : Tendsto (fun n => width n / Real.sqrt (n + 1))
      atTop (𝓝 1)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν (n + 1)
        (nonnegativeTransitionEvent (n + 1) (width n)) := by
  have hlast : Skorokhod.linearPath (7 / 16 : ℝ) ∈
      ((hB.lastZeroMeanderPathLaw hmeasurable).map
        Skorokhod.ofContinuousMap).support :=
    hB.linearPath_mem_lastZeroMeanderCadlagLaw_support
      hmeasurable (by norm_num)
  have hlaw : P.map (fun ω => Skorokhod.ofContinuousMap
      (restrictPathToUnitInterval
        (centeredFirstWindowShift
          (hB.continuousPathMap hmeasurable ω)))) =
      (hB.lastZeroMeanderPathLaw hmeasurable).map
        Skorokhod.ofContinuousMap := by
    have hfirst : Measurable (fun ω => restrictPathToUnitInterval
        (centeredFirstWindowShift
          (hB.continuousPathMap hmeasurable ω))) :=
      continuous_restrictPathToUnitInterval.measurable.comp
        (measurable_centeredFirstWindowShift.comp
          (hB.measurable_continuousPathMap hmeasurable))
    rw [← law_centeredFirstWindowShift_eq_lastZeroMeanderPathLaw
      hB hcontinuous hmeasurable]
    exact (Measure.map_map Skorokhod.measurable_ofContinuousMap hfirst).symm
  have hsupport : Skorokhod.straightPath (7 / 16 : ℝ) ∈
      (P.map (fun ω => Skorokhod.ofContinuousMap
        (restrictPathToUnitInterval
          (centeredFirstWindowShift
            (hB.continuousPathMap hmeasurable ω))))).support := by
    rw [hlaw]
    exact hlast
  exact exists_eventually_transitionConditionalProbability_ge_of_firstWindowSupport
    ν hν hB hcontinuous hmeasurable hrho hrhoSmall hsupport hwidth hratio

/-- The meander transition bound for the original positive finite
variance, with no conditional-limit or support hypothesis. -/
theorem exists_eventually_transitionConditionalProbability_ge_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    {width : ℕ → ℝ} (hwidth : ∀ n, 0 ≤ width n)
    (hratio : Tendsto (fun n => width n / Real.sqrt (n + 1))
      atTop (𝓝 1)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν (n + 1)
        (nonnegativeTransitionEvent (n + 1) (width n)) := by
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredSecondMoment
      ν hν hsigma (n + 1)
  have hlimit : TendstoInDistribution
      (fun n increment => normalizedLinearCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment)
      atTop (fun ω => Skorokhod.ofContinuousMap
        (hB.lastZeroMeanderPath hmeasurable ω))
      (fun n => survivalConditionedLaw ν (n + 1)) P := by
    have hcomp :=
      (tendstoInDistribution_survivalConditionedPath_meander_of_centeredSecondMoment
        ν hν hsigma hB hcontinuous hmeasurable).continuous_comp
          Skorokhod.continuous_ofContinuousMap
    apply TendstoInDistribution.congr (h := hcomp)
    · intro n
      filter_upwards [] with increment
      rfl
    · filter_upwards [] with ω
      rfl
  have hlast : Skorokhod.linearPath ((7 / 16) / sigma) ∈
      ((hB.lastZeroMeanderPathLaw hmeasurable).map
        Skorokhod.ofContinuousMap).support :=
    hB.linearPath_mem_lastZeroMeanderCadlagLaw_support
      hmeasurable (div_pos (by norm_num) hsigma)
  have hlaw : P.map (fun ω => Skorokhod.ofContinuousMap
      (hB.lastZeroMeanderPath hmeasurable ω)) =
      (hB.lastZeroMeanderPathLaw hmeasurable).map
        Skorokhod.ofContinuousMap := by
    rw [IsBrownianReal.lastZeroMeanderPathLaw]
    exact (Measure.map_map Skorokhod.measurable_ofContinuousMap
      (hB.measurable_lastZeroMeanderPath hmeasurable)).symm
  have hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (P.map (fun ω => Skorokhod.ofContinuousMap
        (hB.lastZeroMeanderPath hmeasurable ω))).support := by
    rw [hlaw]
    exact hlast
  exact exists_eventually_interpolatedTransitionConditionalProbability_ge
    hsigma hrho hrhoSmall hlimit hsupport hwidth hratio

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
