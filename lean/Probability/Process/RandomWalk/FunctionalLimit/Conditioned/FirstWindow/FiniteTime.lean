/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Portmanteau
public import Probability.ConvergenceInDistribution.Mapping
public import Probability.Process.Brownian.AboveStart.FirstWindow.TimeFiniteHorizon
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.FiniteHorizon

/-!
# Convergence of finite first-window times

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_firstWindowTimeFiniteHorizon`:
  for each finite $s$, the first eligible-window time of the
  normalized polygonal walk on $[0,s]$ converges in distribution
  to the corresponding Brownian first-window time under $P^s$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendsto_measure_finiteFirstWindow`:
  the probability that a first eligible unit window starts by $s-1$
  converges to its Brownian counterpart.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendsto_measure_noFiniteFirstWindow`:
  the complementary finite-window probabilities also converge.

The second statement is equation (3.5) in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Theorem 3.2, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. It uses Donsker convergence and the
almost-sure continuity in Lemma 2.4.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Donsker convergence transfers through Bolthausen's finite-horizon
first-window time functional by Lemma 2.4. -/
theorem tendstoInDistribution_firstWindowTimeFiniteHorizon
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (s : ℝ≥0) (m : ℕ) (hm : 0 < m) (hsm : s ≤ m) :
    TendstoInDistribution
      (fun n increment => firstWindowTimeFiniteHorizon s
        (restrictPathTo s
          (normalizedLinearContinuousPathUnbounded
            (fun n => Real.sqrt n) n increment)))
      atTop
      (fun ω => firstWindowTimeFiniteHorizon s
        (restrictPathTo s
          (hB.continuousPathMap hmeasurable ω)))
      (fun _ => iidSequenceLaw ν) P := by
  have hDonsker :=
    RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon
      ν hcentered hsecondMoment hB hcontinuous hmeasurable s m hm hsm
  have hcont :
      ∀ᵐ f ∂P.map (fun ω => restrictPathTo s
        (hB.continuousPathMap hmeasurable ω)),
        ContinuousAt (firstWindowTimeFiniteHorizon s) f := by
    convert hB.ae_continuousAt_firstWindowTimeFiniteHorizon
      hmeasurable s using 1
    rw [finiteHorizonPathLaw, Measure.map_map]
    · rfl
    · exact (continuous_restrictPathTo s).measurable
    · exact hB.measurable_continuousPathMap hmeasurable
  simpa only [Function.comp_def] using
    hDonsker.measurable_comp_of_continuousAt_ae
      (measurable_firstWindowTimeFiniteHorizon s) hcont

/-- Bolthausen's equation (3.5): the finite-window existence event is a
continuity event under the projected Brownian law. Every finite value of
$T^s$ is at most $s-1$, so the cutoff $s$ has zero mass. -/
theorem tendsto_measure_finiteFirstWindow
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (s : ℝ≥0) (m : ℕ) (hm : 0 < m) (hsm : s ≤ m) :
    Tendsto (fun n => (iidSequenceLaw ν)
      {increment | firstNonnegativeWindowStartUpTo
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment) s ≠ ⊤})
      atTop
      (nhds (P {ω | firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hmeasurable ω) s ≠ ⊤})) := by
  let X (n : ℕ) (increment : ℕ → ℝ) : WithTop ℝ≥0 :=
    firstWindowTimeFiniteHorizon s
      (restrictPathTo s
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment))
  let Z (ω : Ω) : WithTop ℝ≥0 :=
    firstWindowTimeFiniteHorizon s
      (restrictPathTo s (hB.continuousPathMap hmeasurable ω))
  have hconv : TendstoInDistribution X atTop Z
      (fun _ => iidSequenceLaw ν) P :=
    tendstoInDistribution_firstWindowTimeFiniteHorizon
      ν hcentered hsecondMoment hB hcontinuous hmeasurable s m hm hsm
  have hsingleton : P.map Z ({(s : WithTop ℝ≥0)}) = 0 := by
    have hpre : Z ⁻¹' ({(s : WithTop ℝ≥0)}) = ∅ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      exact firstWindowTimeFiniteHorizon_ne_horizon s _
    rw [Measure.map_apply_of_aemeasurable hconv.aemeasurable_limit
      (measurableSet_singleton _), hpre, measure_empty]
  have hfrontier :
      frontier (Set.Iio (s : WithTop ℝ≥0)) ⊆
        {(s : WithTop ℝ≥0)} := by
    simpa only [Set.Iio, id_eq, Set.ofPred_eq_eq_singleton] using
      (frontier_lt_subset_eq
        (f := id) (g := fun _ : WithTop ℝ≥0 => (s : WithTop ℝ≥0))
        continuous_id continuous_const)
  have hboundary : P.map Z
      (frontier (Set.Iio (s : WithTop ℝ≥0))) = 0 :=
    measure_mono_null hfrontier hsingleton
  have hprob := hconv.tendsto_measure_map_of_null_frontier hboundary
  have hXpre (n : ℕ) :
      X n ⁻¹' Set.Iio (s : WithTop ℝ≥0) =
        {increment | firstNonnegativeWindowStartUpTo
          (normalizedLinearContinuousPathUnbounded
            (fun n => Real.sqrt n) n increment) s ≠ ⊤} := by
    ext increment
    change X n increment < (s : WithTop ℝ≥0) ↔ _
    rw [firstWindowTimeFiniteHorizon_lt_horizon_iff]
    simp only [firstWindowTimeFiniteHorizon_restrictPathTo,
      Set.mem_ofPred_eq]
  have hZpre : Z ⁻¹' Set.Iio (s : WithTop ℝ≥0) =
      {ω | firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hmeasurable ω) s ≠ ⊤} := by
    ext ω
    change Z ω < (s : WithTop ℝ≥0) ↔ _
    rw [firstWindowTimeFiniteHorizon_lt_horizon_iff]
    simp only [firstWindowTimeFiniteHorizon_restrictPathTo,
      Set.mem_ofPred_eq]
  convert hprob using 1
  · funext n
    rw [Measure.map_apply_of_aemeasurable (hconv.forall_aemeasurable n)
      isOpen_Iio.measurableSet, hXpre]
  · rw [Measure.map_apply_of_aemeasurable hconv.aemeasurable_limit
      isOpen_Iio.measurableSet, hZpre]

/-- The complementary form of Bolthausen's equation (3.5). -/
theorem tendsto_measure_noFiniteFirstWindow
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (s : ℝ≥0) (m : ℕ) (hm : 0 < m) (hsm : s ≤ m) :
    Tendsto (fun n => (iidSequenceLaw ν)
      {increment | firstNonnegativeWindowStartUpTo
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment) s = ⊤})
      atTop
      (nhds (P {ω | firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hmeasurable ω) s = ⊤})) := by
  have hgood := tendsto_measure_finiteFirstWindow ν hcentered
    hsecondMoment hB hcontinuous hmeasurable s m hm hsm
  have hbad := ENNReal.Tendsto.sub tendsto_const_nhds hgood
    (Or.inl ENNReal.one_ne_top)
  have hmeasWalk (n : ℕ) : MeasurableSet
      {increment | firstNonnegativeWindowStartUpTo
        (normalizedLinearContinuousPathUnbounded
          (fun n => Real.sqrt n) n increment) s ≠ ⊤} := by
    exact ((measurable_firstNonnegativeWindowStartUpTo s).comp
      (measurable_normalizedLinearContinuousPathUnbounded _ n)
      (measurableSet_singleton ⊤)).compl
  have hmeasBrownian : MeasurableSet
      {ω | firstNonnegativeWindowStartUpTo
        (hB.continuousPathMap hmeasurable ω) s ≠ ⊤} := by
    exact (((measurable_firstNonnegativeWindowStartUpTo s).comp
      (hB.measurable_continuousPathMap hmeasurable))
      (measurableSet_singleton ⊤)).compl
  convert hbad using 1
  · funext n
    rw [show {increment | firstNonnegativeWindowStartUpTo
          (normalizedLinearContinuousPathUnbounded
            (fun n => Real.sqrt n) n increment) s = ⊤} =
        {increment | firstNonnegativeWindowStartUpTo
          (normalizedLinearContinuousPathUnbounded
            (fun n => Real.sqrt n) n increment) s ≠ ⊤}ᶜ by ext; simp,
      measure_compl (hmeasWalk n), measure_univ]
    exact measure_ne_top _ _
  · rw [show {ω | firstNonnegativeWindowStartUpTo
          (hB.continuousPathMap hmeasurable ω) s = ⊤} =
        {ω | firstNonnegativeWindowStartUpTo
          (hB.continuousPathMap hmeasurable ω) s ≠ ⊤}ᶜ by ext; simp,
      measure_compl hmeasBrownian, measure_univ]
    exact measure_ne_top _ _

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
