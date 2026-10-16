/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Meander.Identification
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival.Scaling
public import Probability.Process.RandomWalk.Path.Interpolation.Scaling

/-!
# Brownian-meander limit for finite positive variance

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_survivalConditionedPath_meander_of_centeredSecondMoment`:
  if $\mathbb EX_1=0$ and $\mathbb EX_1^2=\sigma^2>0$, then the
  polygonal interpolation of $S$ divided by $\sigma\sqrt n$ conditioned
  on nonnegative survival converges to the Brownian meander.

This transports Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098, Theorem 3.2, through positive variance
normalization, with the limit law identified by Iglehart, *Functional Central Limit Theorems for
Random Walks Conditioned to Stay Positive*, Ann. Probab. 2(4) (1974),
608--619, DOI 10.1214/aop/1176996607, Section 3, theorem (3.4), p. 616. Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), uses this limit in Appendix A.2, Lemma A.7, and the proof
of Chapter 3, Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

/-- The conditioned polygonal-path limit with the original variance
normalization $\sigma\sqrt n$. This is Bolthausen's conditioned invariance
principle, Theorem 3.2, with variance normalization restored; the limit is
identified by Donald L. Iglehart, *Functional Central Limit Theorems for
Random Walks Conditioned to Stay Positive*, Section 3, theorem (3.4),
p. 616, DOI 10.1214/aop/1176996607. Bolthausen's article is *On a
Functional Central Limit Theorem for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. -/
theorem tendstoInDistribution_survivalConditionedPath_meander_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
        survivalConditionedLaw_isProbabilityMeasure_of_centeredSecondMoment
          ν hν hsigma (n + 1)
    TendstoInDistribution
      (fun (n : ℕ) increment => normalizedLinearContinuousPathIcc
        (fun m => sigma * Real.sqrt m) (n + 1) increment)
      atTop (hB.lastZeroMeanderPath hmeasurable)
      (fun n => survivalConditionedLaw ν (n + 1)) P := by
  let νunit := ν.map (fun x => x / sigma)
  have hνunit : IsCenteredUnitSecondMoment νunit := hν.map_div hsigma
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredSecondMoment
      ν hν hsigma (n + 1)
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw νunit (n + 1)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment
      νunit hνunit (n + 1)
  have hunit := tendstoInDistribution_survivalConditionedPath_meander
    νunit hνunit hB hcontinuous hmeasurable
  have hT : Measurable (fun x : ℕ → ℝ => fun j => x j / sigma) :=
    Measurable.of_eval fun j =>
      (measurable_id.div_const sigma).comp (measurable_pi_apply j)
  have hlaw (n : ℕ) :
      (survivalConditionedLaw ν (n + 1)).map
        (normalizedLinearContinuousPathIcc
          (fun m => sigma * Real.sqrt m) (n + 1)) =
      (survivalConditionedLaw νunit (n + 1)).map
        (normalizedLinearContinuousPathIcc
          (fun m => Real.sqrt m) (n + 1)) := by
    let pathUnit := normalizedLinearContinuousPathIcc
      (fun m => Real.sqrt m) (n + 1)
    let pathSigma := normalizedLinearContinuousPathIcc
      (fun m => sigma * Real.sqrt m) (n + 1)
    have hpath : pathUnit ∘ (fun x : ℕ → ℝ => fun j => x j / sigma) =
        pathSigma := by
      funext x
      exact normalizedLinearContinuousPathIcc_div_const_eq
        (Nat.succ_pos n) hsigma x
    calc
      (survivalConditionedLaw ν (n + 1)).map pathSigma =
          (survivalConditionedLaw ν (n + 1)).map
            (pathUnit ∘ (fun x : ℕ → ℝ => fun j => x j / sigma)) := by
          rw [hpath]
      _ = ((survivalConditionedLaw ν (n + 1)).map
            (fun x : ℕ → ℝ => fun j => x j / sigma)).map pathUnit :=
          (Measure.map_map
            (measurable_normalizedLinearContinuousPathIcc _ _)
            hT).symm
      _ = (survivalConditionedLaw νunit (n + 1)).map pathUnit := by
          rw [survivalConditionedLaw_map_div ν hsigma (n + 1)]
  refine ⟨fun n =>
    (measurable_normalizedLinearContinuousPathIcc _ _).aemeasurable,
    hunit.aemeasurable_limit, ?_⟩
  apply hunit.tendsto.congr'
  filter_upwards [] with n
  apply Subtype.ext
  exact (hlaw n).symm

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
