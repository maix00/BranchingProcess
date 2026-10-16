/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.FiniteApproximation
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.FinitePathLimit
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.FiniteTime
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.FirstWindow.Selection
public import Probability.Process.Brownian.AboveStart.FirstWindow.CenteredLimit
public import Probability.Process.Path.FiniteHorizonScaling
public import Topology.Cadlag.Skorokhod.Maps.Continuous

/-!
# Functional limit after the first eligible window

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_centeredFirstWindowShift`:
  $\Phi(X_n)\Rightarrow\Phi(W)$ on $[0,1]$, where
  $\Phi(f)(t)=f(T(f)+t)-f(T(f))$ and $T$ is the first eligible
  unit-window time.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_centeredFirstWindowShift_unitInterval`:
  $\Phi(X_n)|_{[0,1]}\Rightarrow\Phi(W)|_{[0,1]}$ in
  $C([0,1],\mathbb R)$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_survivalConditionedPath`:
  $\mathcal L(X_n\mid S_1,\ldots,S_n\ge0)\Rightarrow
  \mathcal L(\Phi(W)|_{[0,1]})$ in $C([0,1],\mathbb R)$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.tendstoInDistribution_survivalConditionedInterpolatedCadlagPath`:
  $\mathcal L(\iota X_n\mid S_1,\ldots,S_n\ge0)\Rightarrow
  \mathcal L(\iota\Phi(W)|_{[0,1]})$ in Skorokhod $J_1$ space,
  where $\iota:C([0,1],\mathbb R)\to D([0,1],\mathbb R)$ is the
  canonical inclusion.

The first three statements formalize the centered path comparison of
Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Theorem 3.2, equations (3.3)--(3.8), Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098. For a fixed finite
cutoff, Donsker convergence and Lemma 2.5 give the shifted limit;
equation (3.5) controls the probability that the cutoff is reached;
the Brownian cutoff error tends to zero. The final weak-convergence
comparison is expressed with bounded Lipschitz observables in place
of the continuity-set formulation in Erwin Bolthausen, *On a functional
central limit theorem for random walks conditioned to stay positive*,
Theorem 3.2. The identification of
$\mathcal L(\Phi(W))$ with Brownian meander is a separate step on page
484 of Bolthausen. Donald L. Iglehart, *Functional Central Limit Theorems
for Random Walks Conditioned to Stay Positive*, Ann. Probab. 2(4)
(1974), 608--619, DOI 10.1214/aop/1176996607, Section 3, identifies
the meander law through the path after Brownian motion's last zero.
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

/-- Bolthausen's centered first-window limit on the real unit interval. -/
theorem tendstoInDistribution_centeredFirstWindowShift_unitInterval
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    TendstoInDistribution
      (fun (n : ℕ) increment => restrictPathToUnitInterval
        (centeredFirstWindowShift
          (normalizedLinearContinuousPathUnbounded
            (fun n => Real.sqrt n) n increment)))
      atTop
      (fun ω => restrictPathToUnitInterval
        (centeredFirstWindowShift (hB.continuousPathMap hmeasurable ω)))
      (fun _ => iidSequenceLaw ν) P := by
  have hlimit := (tendstoInDistribution_centeredFirstWindowShift
    ν hcentered hsecondMoment hB hcontinuous hmeasurable).continuous_comp
      continuous_unitIntervalPathOfNNReal
  simpa only [Function.comp_def, ← restrictPathToUnitInterval_eq] using hlimit

/-- Bolthausen's law identity transfers first-window convergence to the
walk conditioned to remain nonnegative for the next $n$ steps. -/
theorem tendstoInDistribution_survivalConditionedPath
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
      atTop
      (fun ω => restrictPathToUnitInterval
        (centeredFirstWindowShift (hB.continuousPathMap hmeasurable ω)))
      (fun n => survivalConditionedLaw ν (n + 1)) P := by
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment
      ν hν (n + 1)
  have hshift := (tendstoInDistribution_centeredFirstWindowShift_unitInterval
    ν hν.1 hν.2 hB hcontinuous hmeasurable).comp_tendsto
      (tendsto_add_atTop_nat 1)
  have hpositive := hν.measure_Ioi_zero_pos
  have hLaw (n : ℕ) :
      (iidSequenceLaw ν).map (fun increment => restrictPathToUnitInterval
        (centeredFirstWindowShift
          (normalizedLinearContinuousPathUnbounded
            (fun m => Real.sqrt m) (n + 1) increment))) =
      (survivalConditionedLaw ν (n + 1)).map
        (normalizedLinearContinuousPathIcc
          (fun m => Real.sqrt m) (n + 1)) :=
    measure_map_centeredFirstWindowShift_eq ν hpositive
      (fun m => Real.sqrt m) (Nat.succ_pos n)
      (Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos n))
  refine ⟨fun n => (measurable_normalizedLinearContinuousPathIcc _ _).aemeasurable,
    hshift.aemeasurable_limit, ?_⟩
  apply hshift.tendsto.congr'
  filter_upwards [] with n
  apply Subtype.ext
  exact hLaw n

/-- The survival-conditioned polygonal paths also converge in the
Skorokhod space used for the step-path formulation. -/
theorem tendstoInDistribution_survivalConditionedInterpolatedCadlagPath
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
      (fun (n : ℕ) increment => Skorokhod.ofContinuousMap
        (normalizedLinearContinuousPathIcc
          (fun m => Real.sqrt m) (n + 1) increment))
      atTop
      (fun ω => Skorokhod.ofContinuousMap
        (restrictPathToUnitInterval
          (centeredFirstWindowShift
            (hB.continuousPathMap hmeasurable ω))))
      (fun n => survivalConditionedLaw ν (n + 1)) P := by
  letI : ∀ n : ℕ, IsProbabilityMeasure
      (survivalConditionedLaw ν (n + 1)) := fun n =>
    survivalConditionedLaw_isProbabilityMeasure_of_centeredUnitSecondMoment
      ν hν (n + 1)
  exact (tendstoInDistribution_survivalConditionedPath
    ν hν hB hcontinuous hmeasurable).continuous_comp
      Skorokhod.continuous_ofContinuousMap

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
