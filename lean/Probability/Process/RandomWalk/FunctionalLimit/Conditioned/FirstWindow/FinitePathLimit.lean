/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Mapping
public import Probability.Process.Brownian.AboveStart.FirstWindow.CenteredFiniteHorizon
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.FiniteHorizon

/-!
# Donsker convergence after a finite first-window shift

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_centeredFirstWindowShiftFiniteHorizon`:
  for every finite $s$, the law of the centered first-window shift of the
  polygonal walk restricted to $[0,s]$ converges to
  the law of the centered shift of the projected Brownian path.

This is the centered continuous-mapping step corresponding to (3.3) of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Theorem 3.2, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. The centered map is required by the
random-walk block in equation (3.2) and by the limit described on
p. 484; the printed definition of $\Phi_s$ on p. 482 omits this
centering. The argument uses the continuity proof of Lemma 2.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The centered finite-horizon continuous-mapping step required by
Bolthausen's Theorem 3.2. The integer `m` covers the real horizon `s`. -/
theorem tendstoInDistribution_centeredFirstWindowShiftFiniteHorizon
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
      (fun n increment => centeredFirstWindowShiftFiniteHorizon s
        (restrictPathTo s
          (normalizedLinearContinuousPathUnbounded
            (fun n => Real.sqrt n) n increment)))
      atTop
      (fun ω => centeredFirstWindowShiftFiniteHorizon s
        (restrictPathTo s
          (hB.continuousPathMap hmeasurable ω)))
      (fun _ => iidSequenceLaw ν) P := by
  have hDonsker :=
    RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_finiteHorizon
      ν hcentered hsecondMoment hB hcontinuous hmeasurable s m hm hsm
  have hcont :
      ∀ᵐ f ∂P.map (fun ω => restrictPathTo s
        (hB.continuousPathMap hmeasurable ω)),
        ContinuousAt (centeredFirstWindowShiftFiniteHorizon s) f := by
    convert hB.ae_continuousAt_centeredFirstWindowShiftFiniteHorizon
      hmeasurable s using 1
    rw [finiteHorizonPathLaw, Measure.map_map]
    · rfl
    · exact (continuous_restrictPathTo s).measurable
    · exact hB.measurable_continuousPathMap hmeasurable
  simpa only [Function.comp_def] using
    hDonsker.measurable_comp_of_continuousAt_ae
      (measurable_centeredFirstWindowShiftFiniteHorizon s) hcont

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
