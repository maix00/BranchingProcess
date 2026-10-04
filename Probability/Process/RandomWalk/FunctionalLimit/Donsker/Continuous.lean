/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Rational
public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Tightness.Path
public import Probability.Process.Path.FiniteDimensional

/-!
# Continuous-path Donsker theorem

Tightness of the polygonal path laws and convergence on the dense family of
rational unit-interval times yield convergence in continuous-path space.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk


/-- Donsker's invariance principle for the canonical IID increment law,
with an arbitrary measurable everywhere-continuous realization of the
Brownian finite-dimensional distributions as limit. -/
theorem tendstoInDistribution_normalizedLinearContinuousPath_brownian
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hcentered : ∫ x, x ∂nu = 0)
    (hsecondMoment : ∫ x, x ^ 2 ∂nu = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    TendstoInDistribution
      (fun n => normalizedLinearContinuousPathIcc
        (fun n => Real.sqrt n) n)
      atTop (continuousunitIntervalPath B hcontinuous)
      (fun _ => independentIncrementLaw nu) P := by
  let pathLaw : ℕ → ProbabilityMeasure C(unitInterval, ℝ) :=
    fun n => ⟨normalizedLinearPathLaw nu (fun n => Real.sqrt n) n,
      inferInstance⟩
  let brownianLaw : ProbabilityMeasure C(unitInterval, ℝ) :=
    ⟨P.map (continuousunitIntervalPath B hcontinuous), inferInstance⟩
  have htight : IsTightMeasureSet
      {((pathLaw n : ProbabilityMeasure C(unitInterval, ℝ)) :
        Measure C(unitInterval, ℝ)) | n} := by
    simpa only [pathLaw, ProbabilityMeasure.coe_mk, Set.range] using
      isTightMeasureSet_normalizedLinearPathLaw nu
        ⟨hcentered, hsecondMoment⟩
  have hfinite (I : Finset RationalGrid.RationalUnitInterval) :
      Tendsto (fun n => (pathLaw n).map
          (Process.Path.finiteEvaluation
            (fun q : I => RationalGrid.unitCoe q))) atTop
        (nhds (brownianLaw.map
          (Process.Path.finiteEvaluation
            (fun q : I => RationalGrid.unitCoe q)))) := by
    have h :=
      (tendstoInDistribution_normalizedLinearPath_rationalFinite_continuousPath
        nu hcentered hsecondMoment hB hcontinuous I).tendsto
    have hsource :
        (fun n => (pathLaw n).map
          (Process.Path.finiteEvaluation
            (fun q : I => RationalGrid.unitCoe q))) =
        (fun n => ⟨Measure.map
          (fun increment q =>
            normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n
              increment (RationalGrid.unitCoe q))
          (independentIncrementLaw nu), inferInstance⟩) := by
      funext n
      apply Subtype.ext
      change Measure.map
          (Process.Path.finiteEvaluation
            (fun q : I => RationalGrid.unitCoe q))
          (normalizedLinearPathLaw nu (fun n => Real.sqrt n) n) = _
      rw [normalizedLinearPathLaw, Measure.map_map]
      · rfl
      · exact (Process.Path.continuous_finiteEvaluation
          (fun q : I => RationalGrid.unitCoe q)).measurable
      · exact measurable_normalizedLinearContinuousPathIcc _ _
    have htarget : brownianLaw.map
          (Process.Path.finiteEvaluation
            (fun q : I => RationalGrid.unitCoe q)) =
        ⟨Measure.map
          (Process.Path.finiteEvaluation
            (fun q : I => RationalGrid.unitCoe q) ∘
              continuousunitIntervalPath B hcontinuous) P,
          inferInstance⟩ := by
      apply Subtype.ext
      change Measure.map
          (Process.Path.finiteEvaluation
            (fun q : I => RationalGrid.unitCoe q))
          (P.map (continuousunitIntervalPath B hcontinuous)) = _
      rw [Measure.map_map]
      · exact (Process.Path.continuous_finiteEvaluation
          (fun q : I => RationalGrid.unitCoe q)).measurable
      · exact measurable_continuousunitIntervalPath B hcontinuous hmeasurable
    rw [hsource, htarget]
    exact h
  have hpathLaw : Tendsto pathLaw atTop (nhds brownianLaw) :=
    Process.Path.ProbabilityMeasure.tendsto_of_tight_of_finiteEvaluation
      RationalGrid.unitCoe
      RationalGrid.denseRange_unitCoe
      pathLaw brownianLaw htight hfinite
  refine ⟨fun n =>
      (measurable_normalizedLinearContinuousPathIcc
        (fun n => Real.sqrt n) n).aemeasurable,
    (measurable_continuousunitIntervalPath B hcontinuous hmeasurable).aemeasurable,
    ?_⟩
  simpa only [pathLaw, brownianLaw, normalizedLinearPathLaw,
    ProbabilityMeasure.coe_mk] using hpathLaw

end ProbabilityTheory.RandomWalk
