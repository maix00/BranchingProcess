/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Continuous
public import Probability.Process.Brownian.Meander.LastSignChange
public import Probability.ConvergenceInDistribution.Mapping

/-!
# Donsker convergence through the last-sign-change transform

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_signStableMeanderTransform`:
  for a centered unit-variance walk with polygonal path $X_n$ and
  Brownian motion $W$, Bolthausen's original
  $\Psi(X_n)\Rightarrow\Psi(W)$ in
  $C([0,1],\mathbb R)$.

This formalizes the continuous-mapping step in the final paragraph of
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098,
page 484. The almost-sure continuity of $\Psi$ is proved in
`Probability.Process.Brownian.Meander.LastSignChange`.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Donsker convergence transfers to Bolthausen's sign-stable terminal path by
continuous mapping at almost every Brownian sample path. -/
theorem tendstoInDistribution_signStableMeanderTransform
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    TendstoInDistribution
      (fun (n : ℕ) increment =>
        ContinuousMap.signStableMeanderTransform
          (normalizedLinearContinuousPathIcc
            (fun n => Real.sqrt n) n increment))
      atTop
      (fun ω => ContinuousMap.signStableMeanderTransform
        (continuousunitIntervalPath B hcontinuous ω))
      (fun _ => iidSequenceLaw ν) P := by
  have hDonsker :=
    tendstoInDistribution_normalizedLinearContinuousPath_brownian
      ν hcentered hsecondMoment hB.toIsPreBrownianReal
      hcontinuous hmeasurable
  have hcontSource : ∀ᵐ ω ∂P,
      ContinuousAt ContinuousMap.signStableMeanderTransform
        (continuousunitIntervalPath B hcontinuous ω) := by
    filter_upwards [hB.ae_continuousAt_signStableMeanderTransform hmeasurable,
      hB.continuousPathMap_ae_eq hmeasurable] with ω hcont heq
    have hpath : continuousunitIntervalPath B hcontinuous ω =
        restrictPathToUnitInterval (hB.continuousPathMap hmeasurable ω) := by
      ext t
      exact (heq (UnitInterval.toNNReal t)).symm
    simpa only [hpath] using hcont
  have hcontLaw : ∀ᵐ f ∂P.map (continuousunitIntervalPath B hcontinuous),
      ContinuousAt ContinuousMap.signStableMeanderTransform f := by
    have hf := measurable_continuousunitIntervalPath B hcontinuous hmeasurable
    exact (ae_map_iff hf.aemeasurable
      (measurableSet_of_continuousAt
        ContinuousMap.signStableMeanderTransform)).2 hcontSource
  simpa only [Function.comp_def] using
    hDonsker.measurable_comp_of_continuousAt_ae
      ContinuousMap.measurable_signStableMeanderTransform hcontLaw

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
