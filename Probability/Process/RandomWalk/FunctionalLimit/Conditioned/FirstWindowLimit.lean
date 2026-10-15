/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.FiniteApproximation
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FiniteWindowLimit
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FiniteWindowTime
public import Probability.Process.Brownian.AboveStart.FirstWindowCenteredLimit

/-!
# Functional limit after the first eligible window

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_centeredFirstWindowShift`:
  the centered normalized walk shifted at its first eligible unit window
  converges on $[0,1]$ to the similarly shifted Brownian path.

This proves the centered path comparison of Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Theorem 3.2, equations (3.3)--(3.8), Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098. For a fixed finite
cutoff, Donsker convergence and Lemma 2.5 give the shifted limit;
equation (3.5) controls the probability that the cutoff is reached;
the Brownian cutoff error tends to zero.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The centered version of Bolthausen's first-window path convergence. -/
theorem tendstoInDistribution_centeredFirstWindowShift
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    TendstoInDistribution
      (fun (n : ℕ) increment => restrictPathTo 1
        (centeredFirstWindowShift
          (normalizedLinearContinuousPathUnbounded
            (fun n => Real.sqrt n) n increment)))
      atTop
      (fun ω => restrictPathTo 1
        (centeredFirstWindowShift (hB.continuousPathMap hmeasurable ω)))
      (fun _ => iidSequenceLaw ν) P := by
  let walk (n : ℕ) (increment : ℕ → ℝ) : C(ℝ≥0, ℝ) :=
    normalizedLinearContinuousPathUnbounded
      (fun n => Real.sqrt n) n increment
  let pathB := hB.continuousPathMap hmeasurable
  let X (n : ℕ) (increment : ℕ → ℝ) : C(Set.Icc (0 : ℝ≥0) 1, ℝ) :=
    restrictPathTo 1 (centeredFirstWindowShift (walk n increment))
  let Y (k n : ℕ) (increment : ℕ → ℝ) :
      C(Set.Icc (0 : ℝ≥0) 1, ℝ) :=
    restrictPathTo 1
      (centeredFirstWindowShiftUpTo (walk n increment) ((k : ℝ≥0) + 1))
  let Z (ω : Ω) : C(Set.Icc (0 : ℝ≥0) 1, ℝ) :=
    restrictPathTo 1 (centeredFirstWindowShift (pathB ω))
  let W (k : ℕ) (ω : Ω) : C(Set.Icc (0 : ℝ≥0) 1, ℝ) :=
    restrictPathTo 1
      (centeredFirstWindowShiftUpTo (pathB ω) ((k : ℝ≥0) + 1))
  let b (k n : ℕ) : ℝ := ((iidSequenceLaw ν)
    {increment | firstNonnegativeWindowStartUpTo
      (walk n increment) ((k : ℝ≥0) + 1) = ⊤}).toReal
  let c (k : ℕ) : ℝ := (P
    {ω | firstNonnegativeWindowStartUpTo
      (pathB ω) ((k : ℝ≥0) + 1) = ⊤}).toReal
  have hwalk (n : ℕ) : Measurable (walk n) :=
    measurable_normalizedLinearContinuousPathUnbounded _ n
  have hpathB : Measurable pathB :=
    hB.measurable_continuousPathMap hmeasurable
  have hX (n : ℕ) : Measurable (X n) :=
    (continuous_restrictPathTo 1).measurable.comp
      (measurable_centeredFirstWindowShift.comp (hwalk n))
  have hY (k n : ℕ) : Measurable (Y k n) :=
    (continuous_restrictPathTo 1).measurable.comp
      ((measurable_centeredFirstWindowShiftUpTo _).comp (hwalk n))
  have hZ : Measurable Z :=
    (continuous_restrictPathTo 1).measurable.comp
      (measurable_centeredFirstWindowShift.comp hpathB)
  have hfinite (k : ℕ) :
      TendstoInDistribution (Y k) atTop (W k)
        (fun _ => iidSequenceLaw ν) P := by
    simpa only [Y, W, walk, pathB,
      centeredFirstWindowShiftFiniteHorizon_restrictPathTo] using
      tendstoInDistribution_centeredFirstWindowShiftFiniteHorizon
        ν hcentered hsecondMoment hB hcontinuous hmeasurable
        ((k : ℝ≥0) + 1) (k + 1) (Nat.succ_pos k) (by simp)
  have hlimit : TendstoInDistribution W atTop Z (fun _ => P) P :=
    hB.tendstoInDistribution_centeredFirstWindowShiftUpTo hmeasurable
  have hbound (k n : ℕ) :
      (iidSequenceLaw ν).real
        {increment | X n increment ≠ Y k n increment} ≤ b k n := by
    apply measureReal_mono
    · intro increment hneq
      by_contra hfinite
      have heq := centeredFirstWindowShiftUpTo_eq_of_finite
        (walk n increment) ((k : ℝ≥0) + 1) hfinite
      exact hneq (congrArg (restrictPathTo 1) heq).symm
    · exact measure_ne_top _ _
  have hb (k : ℕ) : Tendsto (b k) atTop (nhds (c k)) := by
    have hprob := tendsto_measure_noFiniteFirstWindow
      ν hcentered hsecondMoment hB hcontinuous hmeasurable
      ((k : ℝ≥0) + 1) (k + 1) (Nat.succ_pos k) (by simp)
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hprob
  have hc : Tendsto c atTop (nhds 0) := by
    have hprob := hB.tendsto_measure_firstNonnegativeWindowStartUpTo_eq_top
      hmeasurable
    simpa only [c, pathB, Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprob
  change TendstoInDistribution X atTop Z
    (fun _ => iidSequenceLaw ν) P
  exact tendstoInDistribution_of_finite_approximations
    (iidSequenceLaw ν) P X Y Z W hX hY hZ hfinite hlimit
    b c hbound hb hc

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
