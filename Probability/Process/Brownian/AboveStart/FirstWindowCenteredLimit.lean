/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.AboveStart.FirstWindow
public import Probability.Process.Path.AboveStart.FirstWindowCentered
public import Probability.Process.Path.AboveStart.FirstWindowFiniteHorizon
public import Probability.ConvergenceInDistribution.Basic

/-!
# Removing a finite cutoff from Brownian first-window shifts

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.tendstoInDistribution_centeredFirstWindowShiftUpTo`:
  the laws of the centered Brownian paths shifted at $T^{n+1}$, restricted
  to $[0,1]$, converge to the law of the path shifted at $T$.

This is the Brownian cutoff removal in equations (3.6)--(3.8) of
Erwin Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Theorem 3.2, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098. Almost surely $T<\infty$,
and every sufficiently large cutoff gives the same shifted path.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The centered Brownian first-window paths stabilize almost surely as
the finite cutoff tends to infinity. -/
theorem IsBrownianReal.tendstoInDistribution_centeredFirstWindowShiftUpTo
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hmeasurable : ∀ t, Measurable (B t)) :
    TendstoInDistribution
      (fun (n : ℕ) ω => restrictPathTo 1
        (centeredFirstWindowShiftUpTo
          (hB.continuousPathMap hmeasurable ω) ((n : ℝ≥0) + 1)))
      atTop
      (fun ω => restrictPathTo 1
        (centeredFirstWindowShift (hB.continuousPathMap hmeasurable ω)))
      (fun _ => P) P := by
  let pathB := hB.continuousPathMap hmeasurable
  have hpath : Measurable pathB :=
    hB.measurable_continuousPathMap hmeasurable
  have hfiniteSet : MeasurableSet
      {ω | firstNonnegativeWindowStart (pathB ω) ≠ ⊤} :=
    (((measurable_firstNonnegativeWindowStart).comp hpath)
      (measurableSet_singleton ⊤)).compl
  have hfinite : ∀ᵐ ω ∂P,
      firstNonnegativeWindowStart (pathB ω) ≠ ⊤ :=
    (mem_ae_iff_prob_eq_one hfiniteSet).mpr
      (hB.measure_firstNonnegativeWindowStart_ne_top_eq_one hmeasurable)
  have hmeasFinite (n : ℕ) : Measurable (fun ω => restrictPathTo 1
      (centeredFirstWindowShiftUpTo (pathB ω) ((n : ℝ≥0) + 1))) :=
    (continuous_restrictPathTo 1).measurable.comp
      ((measurable_centeredFirstWindowShiftUpTo _).comp hpath)
  have hmeasLimit : Measurable (fun ω => restrictPathTo 1
      (centeredFirstWindowShift (pathB ω))) :=
    (continuous_restrictPathTo 1).measurable.comp
      (measurable_centeredFirstWindowShift.comp hpath)
  apply tendstoInDistribution_of_ae_tendsto
    (fun n => (hmeasFinite n).aemeasurable) hmeasLimit.aemeasurable
  filter_upwards [hfinite] with ω hω
  have hevent := eventually_centeredFirstWindowShiftUpTo_eq
    (pathB ω) hω
  have hevent' : ∀ᶠ n : ℕ in atTop,
      restrictPathTo 1
        (centeredFirstWindowShiftUpTo (pathB ω) ((n : ℝ≥0) + 1)) =
      restrictPathTo 1 (centeredFirstWindowShift (pathB ω)) :=
    hevent.mono fun _ hn => congrArg _ hn
  exact tendsto_const_nhds.congr' (hevent'.mono fun _ h => h.symm)

end ProbabilityTheory

end
