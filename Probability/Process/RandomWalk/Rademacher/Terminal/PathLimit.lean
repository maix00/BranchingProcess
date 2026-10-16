/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.Terminal.Transform
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Meander.LastSignChange

/-!
# Weak limit of the terminal path of a simple symmetric walk

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.tendstoInDistribution_rademacherTerminalAbsolutePath`:
  the absolute polygonal segment after the last sign change satisfies
  $\widetilde Y_{n+1}\Rightarrow\Psi(B)$ in
  $C([0,1],\mathbb R)$ under fair-Boolean IID increments.
- `ProbabilityTheory.RandomWalk.tendstoInDistribution_rademacherTerminalAbsolutePath_lastZero`:
  the same convergence with Iglehart's normalized Brownian terminal
  excursion as the limit realization.

This is the continuous-mapping step on page 484 of Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098. The equality
$\Psi(X_n)=\widetilde Y_n$ is proved in `TerminalTransform`.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Bolthausen's terminal polygonal path converges to his Brownian
sign-stable transform under the fair simple symmetric walk law. -/
theorem tendstoInDistribution_rademacherTerminalAbsolutePath
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    TendstoInDistribution
      (fun (n : ℕ) branch => rademacherTerminalAbsolutePath branch (n + 1))
      atTop
      (fun ω => ContinuousMap.signStableMeanderTransform
        (continuousunitIntervalPath B hcontinuous ω))
      (fun _ => iidSequenceLaw fairBoolMeasure) P := by
  have hcentered : (∫ x : ℝ, x ∂rademacherMeasure) = 0 := by
    rw [integral_rademacherMeasure]
    norm_num
  have hsecond : (∫ x : ℝ, x ^ 2 ∂rademacherMeasure) = 1 := by
    rw [integral_rademacherMeasure]
    norm_num
  have hreal :=
    FunctionalLimit.Conditioned.tendstoInDistribution_signStableMeanderTransform
      rademacherMeasure hcentered hsecond hB hcontinuous hmeasurable
  have hshift := hreal.comp_tendsto (tendsto_add_atTop_nat 1)
  let X (n : ℕ) (branch : ℕ → Bool) :=
    ContinuousMap.signStableMeanderTransform
      (normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) (n + 1) (rademacherIncrementPath branch))
  have hX (n : ℕ) : Measurable (X n) :=
    ContinuousMap.measurable_signStableMeanderTransform.comp
      ((measurable_normalizedLinearContinuousPathIcc _ _).comp
        measurable_rademacherIncrementPath)
  have hmap (n : ℕ) :
      (iidSequenceLaw fairBoolMeasure).map (X n) =
        (iidSequenceLaw rademacherMeasure).map
          (fun increment => ContinuousMap.signStableMeanderTransform
            (normalizedLinearContinuousPathIcc
              (fun j => Real.sqrt j) (n + 1) increment)) := by
    rw [← map_iidSequenceLaw_rademacherIncrementPath]
    simpa only [Function.comp_def, X] using (Measure.map_map
      (ContinuousMap.measurable_signStableMeanderTransform.comp
        (measurable_normalizedLinearContinuousPathIcc _ _))
      measurable_rademacherIncrementPath).symm
  have hbool : TendstoInDistribution X atTop
      (fun ω => ContinuousMap.signStableMeanderTransform
        (continuousunitIntervalPath B hcontinuous ω))
      (fun _ => iidSequenceLaw fairBoolMeasure) P := {
    forall_aemeasurable n := (hX n).aemeasurable
    aemeasurable_limit := hshift.aemeasurable_limit
    tendsto := by
      have hEq : (fun n => (⟨(iidSequenceLaw fairBoolMeasure).map (X n),
          inferInstance⟩ : ProbabilityMeasure C(unitInterval, ℝ))) =
          (fun n => (⟨(iidSequenceLaw rademacherMeasure).map
            (fun increment => ContinuousMap.signStableMeanderTransform
              (normalizedLinearContinuousPathIcc
                (fun j => Real.sqrt j) (n + 1) increment)),
            inferInstance⟩ : ProbabilityMeasure C(unitInterval, ℝ))) := by
        funext n
        exact Subtype.ext (hmap n)
      rw [hEq]
      exact hshift.tendsto
  }
  apply hbool.congr_eventually
  · filter_upwards [] with n
    filter_upwards [] with branch
    exact (rademacher_signStableMeanderTransform_eq_terminalAbsolutePath
      branch (Nat.succ_pos n))
  · intro n
    have heq : (fun branch => rademacherTerminalAbsolutePath branch (n + 1)) =
        X n := by
      funext branch
      exact (rademacher_signStableMeanderTransform_eq_terminalAbsolutePath
        branch (Nat.succ_pos n)).symm
    rw [heq]
    exact (hX n).aemeasurable

/-- The same terminal-path limit with Iglehart's last-zero Brownian
path as the limit realization. -/
theorem tendstoInDistribution_rademacherTerminalAbsolutePath_lastZero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    TendstoInDistribution
      (fun (n : ℕ) branch => rademacherTerminalAbsolutePath branch (n + 1))
      atTop (hB.lastZeroMeanderPath hmeasurable)
      (fun _ => iidSequenceLaw fairBoolMeasure) P := by
  have hlimit := tendstoInDistribution_rademacherTerminalAbsolutePath
    hB hcontinuous hmeasurable
  have hpath : ∀ᵐ ω ∂P,
      continuousunitIntervalPath B hcontinuous ω =
        restrictPathToUnitInterval
          (hB.continuousPathMap hmeasurable ω) := by
    filter_upwards [hB.continuousPathMap_ae_eq hmeasurable] with ω heq
    ext t
    exact (heq (UnitInterval.toNNReal t)).symm
  have hLaw : P.map (fun ω => ContinuousMap.signStableMeanderTransform
        (continuousunitIntervalPath B hcontinuous ω)) =
      hB.lastZeroMeanderPathLaw hmeasurable := by
    calc
      P.map (fun ω => ContinuousMap.signStableMeanderTransform
          (continuousunitIntervalPath B hcontinuous ω)) =
        P.map (fun ω => ContinuousMap.signStableMeanderTransform
          (restrictPathToUnitInterval
            (hB.continuousPathMap hmeasurable ω))) := by
          apply Measure.map_congr
          filter_upwards [hpath] with ω hω
          rw [hω]
      _ = hB.lastZeroMeanderPathLaw hmeasurable :=
        hB.signStableMeanderPathLaw_eq_lastZeroMeanderPathLaw hmeasurable
  exact hlimit.congr_limit
    (hB.measurable_lastZeroMeanderPath hmeasurable).aemeasurable hLaw

end ProbabilityTheory.RandomWalk

end
