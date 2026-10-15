/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Mapping
public import Probability.Process.Brownian.AboveStart.FirstWindowFiniteHorizon
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.FiniteHorizon

/-!
# Donsker convergence after a finite first-window shift

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_firstWindowShiftFiniteHorizon`:
  for every finite $s$, the law of the first-window shift of the
  polygonal walk restricted to $[0,s]$ converges to
  $(P^s)\circ\Phi_s^{-1}$, represented by applying $\Phi_s$ to the
  projected Brownian path.

This is the continuous-mapping step (3.3) of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Theorem 3.2, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. It uses his Lemma 2.5 for almost-sure
continuity of the displayed, uncentered map $\Phi_m$.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The finite-horizon continuous-mapping step in Bolthausen's
Theorem 3.2, equation (3.3). The integer `m` covers the real horizon `s`. -/
theorem tendstoInDistribution_firstWindowShiftFiniteHorizon
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
      (fun n increment => firstWindowShiftFiniteHorizon s
        (restrictPathTo s
          (normalizedLinearContinuousPathUnbounded
            (fun n => Real.sqrt n) n increment)))
      atTop
      (fun ω => firstWindowShiftFiniteHorizon s
        (restrictPathTo s
          (hB.continuousPathMap hmeasurable ω)))
      (fun _ => iidSequenceLaw ν) P := by
  have hDonsker :=
    RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon
      ν hcentered hsecondMoment hB hcontinuous hmeasurable s m hm hsm
  have hcont :
      ∀ᵐ f ∂P.map (fun ω => restrictPathTo s
        (hB.continuousPathMap hmeasurable ω)),
        ContinuousAt (firstWindowShiftFiniteHorizon s) f := by
    convert hB.ae_continuousAt_firstWindowShiftFiniteHorizon
      hmeasurable s using 1
    rw [finiteHorizonPathLaw, Measure.map_map]
    · rfl
    · exact (continuous_restrictPathTo s).measurable
    · exact hB.measurable_continuousPathMap hmeasurable
  simpa only [Function.comp_def] using
    hDonsker.measurable_comp_of_continuousAt_ae
      (measurable_firstWindowShiftFiniteHorizon s) hcont

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
