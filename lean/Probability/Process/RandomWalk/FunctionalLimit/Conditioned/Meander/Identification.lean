/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.EscapingMixture
public import Probability.Process.RandomWalk.Rademacher.TerminalMixture
public import Probability.Process.RandomWalk.Rademacher.TerminalLengthLimit
public import Probability.Process.RandomWalk.Rademacher.TerminalPathLimit
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.Limit

/-!
# Identification of Bolthausen's conditioned limit with Brownian meander

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.law_centeredFirstWindowShift_eq_lastZeroMeanderPathLaw`:
  the Brownian first eligible window $\Phi(B)$ and Iglehart's
  normalized terminal excursion have the same path law.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_survivalConditionedPath_meander`:
  for a centered unit-variance walk,
  $\mathcal L(X_n\mid S_1,\ldots,S_n\ge0)$ converges to the
  Brownian-meander path law.

The first theorem follows the final paragraph of page 484 of Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. The terminal Brownian representation is
that of Donald L. Iglehart, *Functional Central Limit Theorems for Random
Walks Conditioned to Stay Positive*, Ann. Probab. 2(4) (1974),
608--619, Section 3, DOI 10.1214/aop/1176996607.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

/-- Bolthausen's Brownian first-window limit has Iglehart's
Brownian-meander law. The finite-mixture argument is the final
paragraph on page 484 of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*,
Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. -/
theorem law_centeredFirstWindowShift_eq_lastZeroMeanderPathLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    P.map (fun ω => restrictPathToUnitInterval
      (centeredFirstWindowShift (hB.continuousPathMap hmeasurable ω))) =
      hB.lastZeroMeanderPathLaw hmeasurable := by
  have hrademacher : IsCenteredUnitSecondMoment rademacherMeasure := by
    constructor <;> rw [integral_rademacherMeasure] <;> norm_num
  letI : ∀ k : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw rademacherMeasure (k + 1)) := fun k =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment
      rademacherMeasure hrademacher (k + 1)
  let Q (k : ℕ) : ProbabilityMeasure C(unitInterval, ℝ) :=
    ⟨(survivalConditionedLaw rademacherMeasure (k + 1)).map
      (normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) (k + 1)), inferInstance⟩
  let limit : ProbabilityMeasure C(unitInterval, ℝ) :=
    ⟨P.map (fun ω => restrictPathToUnitInterval
      (centeredFirstWindowShift (hB.continuousPathMap hmeasurable ω))),
      inferInstance⟩
  let meander : ProbabilityMeasure C(unitInterval, ℝ) :=
    ⟨hB.lastZeroMeanderPathLaw hmeasurable, inferInstance⟩
  let mix (n : ℕ) : ProbabilityMeasure C(unitInterval, ℝ) :=
    ⟨(iidSequenceLaw fairBoolMeasure).map
      (fun branch => rademacherTerminalAbsolutePath branch (n + 1)),
      inferInstance⟩
  let weight (n k : ℕ) : ℝ≥0∞ :=
    (iidSequenceLaw fairBoolMeasure)
      {branch : ℕ → Bool |
        terminalSignStableLength (n + 1)
          (rademacherIncrementPath branch) = k + 1}
  have hQ : Tendsto Q atTop (𝓝 limit) := by
    exact (tendstoInDistribution_survivalConditionedPath
      rademacherMeasure hrademacher hB hcontinuous hmeasurable).tendsto
  have hweight (n : ℕ) :
      ∑ k ∈ Finset.range (n + 1), weight n k = 1 := by
    have h := measure_rademacherTerminalAbsolutePath_eq_mixture
      (Nat.succ_pos n) Set.univ MeasurableSet.univ
    simpa only [weight, measure_univ, mul_one] using h.symm
  have hvanish (k : ℕ) : Tendsto (fun n => weight n k) atTop (𝓝 0) := by
    simpa only [weight, Function.comp_def] using
      (tendsto_terminalSignStableLength_cell_zero (k + 1)).comp
        (tendsto_add_atTop_nat 1)
  have hmix (n : ℕ) (A : Set C(unitInterval, ℝ))
      (hA : MeasurableSet A) :
      (mix n : Measure C(unitInterval, ℝ)) A =
        ∑ k ∈ Finset.range (n + 1),
          weight n k * (Q k : Measure C(unitInterval, ℝ)) A := by
    exact measure_rademacherTerminalAbsolutePath_eq_mixture
      (Nat.succ_pos n) A hA
  have hmixLimit : Tendsto mix atTop (𝓝 limit) :=
    ProbabilityMeasure.tendsto_finiteMixture_of_escape
      Q limit mix weight hQ hweight hvanish hmix
  have hterminal : Tendsto mix atTop (𝓝 meander) := by
    exact (tendstoInDistribution_rademacherTerminalAbsolutePath_lastZero
      hB hcontinuous hmeasurable).tendsto
  have hEq : limit = meander := tendsto_nhds_unique hmixLimit hterminal
  exact congrArg (fun q : ProbabilityMeasure C(unitInterval, ℝ) =>
    (q : Measure C(unitInterval, ℝ))) hEq

/-- The conditioned polygonal path converges to the Brownian meander
in the last-zero realization of Iglehart, *Functional Central Limit
Theorems for Random Walks Conditioned to Stay Positive*, Section 3,
Ann. Probab. 2(4) (1974), 608--619, DOI 10.1214/aop/1176996607.
The conditional invariance principle and limit-law identification
follow Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Theorem 3.2 and page 484,
Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. -/
theorem tendstoInDistribution_survivalConditionedPath_meander
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
        survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment
          ν hν (n + 1)
    TendstoInDistribution
      (fun (n : ℕ) increment => normalizedLinearContinuousPathIcc
        (fun m => Real.sqrt m) (n + 1) increment)
      atTop (hB.lastZeroMeanderPath hmeasurable)
      (fun n => survivalConditionedLaw ν (n + 1)) P := by
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment
      ν hν (n + 1)
  have hlimit := tendstoInDistribution_survivalConditionedPath
    ν hν hB hcontinuous hmeasurable
  exact hlimit.congr_limit
    (hB.measurable_lastZeroMeanderPath hmeasurable).aemeasurable
    (law_centeredFirstWindowShift_eq_lastZeroMeanderPathLaw
      hB hcontinuous hmeasurable)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
