/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Transition.FromMeander

/-!
# Meander transition at a diffusive entrance horizon

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveTransitionConditionalProbability_ge_of_centeredSecondMoment`:
  for $N_{\Delta,m}=\lfloor\Delta^2\rfloor-m$, centered increments of
  positive finite variance, and $\Delta\to\infty$, there is $q>0$
  such that $\mathbb P(D_{N_{\Delta,m},\Delta}\mid C_{N_{\Delta,m}})
  \ge q$ eventually.

This is the Brownian-meander transition step in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, used in the proof of Lemma 3.5. The conditional limit is
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485,
Theorem 3.2; the meander identification follows Iglehart,
*Functional Central Limit Theorems for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 2(4) (1974), 608--619, Section 3.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

/-- The conditional transition bound at the shifted diffusive time,
with the meander limit and support proved from the walk hypotheses. -/
theorem exists_eventually_diffusiveTransitionConditionalProbability_ge_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {rho : ℝ} (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν
        (diffusiveTransitionHorizon width offset n)
        (nonnegativeTransitionEvent
          (diffusiveTransitionHorizon width offset n) (width n)) := by
  let N := diffusiveTransitionHorizon width offset
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredSecondMoment
      ν hν hsigma (n + 1)
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (N n)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredSecondMoment
      ν hν hsigma (N n)
  have hargument : Tendsto (fun n => width n ^ 2) atTop atTop := by
    have hmul : Tendsto (fun n => width n * width n) atTop atTop :=
      hwidth.atTop_mul_atTop₀ hwidth
    simpa [pow_two] using hmul
  have hN : Tendsto N atTop atTop := by
    change Tendsto (fun n =>
      Asymptotics.floorBlockLength (fun k => width k ^ 2) n - offset)
      atTop atTop
    exact (tendsto_sub_atTop_nat offset).comp
      (Asymptotics.tendsto_floorBlockLength_atTop hargument)
  have hNpos : ∀ᶠ n : ℕ in atTop, 0 < N n :=
    hN.eventually (eventually_gt_atTop 0)
  have hindex : Tendsto (fun n => N n - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hN
  have hbase : TendstoInDistribution
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
  have hdiff : TendstoInDistribution
      (fun n increment => normalizedLinearCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (N n) increment)
      atTop (fun ω => Skorokhod.ofContinuousMap
        (hB.lastZeroMeanderPath hmeasurable ω))
      (fun n => survivalConditionedLaw ν (N n)) P := by
    have hreindex := hbase.comp_tendsto hindex
    refine ⟨fun n => (measurable_normalizedLinearCadlagPathIcc _ _).aemeasurable,
      hbase.aemeasurable_limit, ?_⟩
    apply hreindex.tendsto.congr'
    filter_upwards [hNpos] with n hn
    apply Subtype.ext
    simp only [Nat.sub_add_cancel hn]
  have hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (P.map (fun ω => Skorokhod.ofContinuousMap
        (hB.lastZeroMeanderPath hmeasurable ω))).support := by
    have hlaw : P.map (fun ω => Skorokhod.ofContinuousMap
        (hB.lastZeroMeanderPath hmeasurable ω)) =
        (hB.lastZeroMeanderPathLaw hmeasurable).map
          Skorokhod.ofContinuousMap := by
      rw [IsBrownianReal.lastZeroMeanderPathLaw]
      exact (Measure.map_map Skorokhod.measurable_ofContinuousMap
        (hB.measurable_lastZeroMeanderPath hmeasurable)).symm
    rw [hlaw]
    exact hB.linearPath_mem_lastZeroMeanderCadlagLaw_support
      hmeasurable (div_pos (by norm_num) hsigma)
  have hratio : Tendsto (fun n => width n / Real.sqrt (N n))
      atTop (𝓝 1) :=
    Asymptotics.tendsto_width_div_sqrt_floor_sq_sub_nat hwidth offset
  have hnonnegative (n : ℕ) :
      ∀ᵐ increment ∂survivalConditionedLaw ν (N n),
        ∀ t : unitInterval,
          0 ≤ normalizedLinearCadlagPathIcc
            (fun j => sigma * Real.sqrt j) (N n) increment t := by
    by_cases hn : 0 < N n
    · exact ae_nonnegative_normalizedLinearCadlagPathIcc ν hn
        (fun j => sigma * Real.sqrt j)
        (mul_pos hsigma (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)))
    · have hn0 : N n = 0 := Nat.eq_zero_of_not_pos hn
      filter_upwards [] with increment
      intro t
      simp [normalizedLinearCadlagPathIcc_apply, normalizedLinearPath, hn0]
  obtain ⟨q, hq, hevent⟩ :=
    exists_eventually_normalizedTransitionCorridorProbability_ge
      hsigma hrho hrhoSmall hdiff hsupport hratio hnonnegative
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  refine ⟨q, hq, ?_⟩
  filter_upwards [hevent, hwidthPos, hNpos] with n hn hw hNn
  have hmeas : MeasurableSet
      (normalizedTransitionCorridor sigma (width n / Real.sqrt (N n))) :=
    (Skorokhod.isClosed_rangeInClosedIntervalEndsIn _ _ _ _).measurableSet
  rw [Measure.map_apply_of_aemeasurable
    (hdiff.forall_aemeasurable n) hmeas] at hn
  have heventEq :
      {increment : ℕ → ℝ |
        normalizedLinearCadlagPathIcc
          (fun j => sigma * Real.sqrt j) (N n) increment ∈
        normalizedTransitionCorridor sigma (width n / Real.sqrt (N n))} =
      nonnegativeTransitionEvent (N n) (width n) := by
    ext increment
    exact (mem_nonnegativeTransitionEvent_iff_normalizedInterpolatedTransitionCorridor
      hNn hsigma hw.le increment).symm
  change q ≤ survivalConditionedLaw ν (N n)
    {increment : ℕ → ℝ |
      normalizedLinearCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (N n) increment ∈
      normalizedTransitionCorridor sigma (width n / Real.sqrt (N n))} at hn
  rw [heventEq] at hn
  exact hn

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
