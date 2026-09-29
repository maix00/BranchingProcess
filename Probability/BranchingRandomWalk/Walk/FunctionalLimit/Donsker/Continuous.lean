import Mathlib.Topology.UnitInterval
import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Rational
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Tightness.Path
import Probability.Process.Path.FiniteDimensional

/-!
# Continuous-path Donsker theorem

Tightness of the polygonal path laws and convergence on the dense family of
rational unit-interval times yield convergence in continuous-path space.
-/

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

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
  have hfinite (I : Finset Skorokhod.RationalunitInterval) :
      Tendsto (fun n => (pathLaw n).map
          (Process.Path.finiteEvaluation
            (fun q : I => Skorokhod.rationalunitIntervalCoe q))) atTop
        (nhds (brownianLaw.map
          (Process.Path.finiteEvaluation
            (fun q : I => Skorokhod.rationalunitIntervalCoe q)))) := by
    have h :=
      (tendstoInDistribution_normalizedLinearPath_rationalFinite_continuousPath
        nu hcentered hsecondMoment hB hcontinuous I).tendsto
    have hsource :
        (fun n => (pathLaw n).map
          (Process.Path.finiteEvaluation
            (fun q : I => Skorokhod.rationalunitIntervalCoe q))) =
        (fun n => ⟨Measure.map
          (fun increment q =>
            normalizedLinearContinuousPathIcc (fun n => Real.sqrt n) n
              increment (Skorokhod.rationalunitIntervalCoe q))
          (independentIncrementLaw nu), inferInstance⟩) := by
      funext n
      apply Subtype.ext
      change Measure.map
          (Process.Path.finiteEvaluation
            (fun q : I => Skorokhod.rationalunitIntervalCoe q))
          (normalizedLinearPathLaw nu (fun n => Real.sqrt n) n) = _
      rw [normalizedLinearPathLaw, Measure.map_map]
      · rfl
      · exact (Process.Path.continuous_finiteEvaluation
          (fun q : I => Skorokhod.rationalunitIntervalCoe q)).measurable
      · exact measurable_normalizedLinearContinuousPathIcc _ _
    have htarget : brownianLaw.map
          (Process.Path.finiteEvaluation
            (fun q : I => Skorokhod.rationalunitIntervalCoe q)) =
        ⟨Measure.map
          (Process.Path.finiteEvaluation
            (fun q : I => Skorokhod.rationalunitIntervalCoe q) ∘
              continuousunitIntervalPath B hcontinuous) P,
          inferInstance⟩ := by
      apply Subtype.ext
      change Measure.map
          (Process.Path.finiteEvaluation
            (fun q : I => Skorokhod.rationalunitIntervalCoe q))
          (P.map (continuousunitIntervalPath B hcontinuous)) = _
      rw [Measure.map_map]
      · exact (Process.Path.continuous_finiteEvaluation
          (fun q : I => Skorokhod.rationalunitIntervalCoe q)).measurable
      · exact measurable_continuousunitIntervalPath B hcontinuous hmeasurable
    rw [hsource, htarget]
    exact h
  have hpathLaw : Tendsto pathLaw atTop (nhds brownianLaw) :=
    Process.Path.ProbabilityMeasure.tendsto_of_tight_of_finiteEvaluation
      Skorokhod.rationalunitIntervalCoe
      Skorokhod.denseRange_rationalunitIntervalCoe
      pathLaw brownianLaw htight hfinite
  refine ⟨fun n =>
      (measurable_normalizedLinearContinuousPathIcc
        (fun n => Real.sqrt n) n).aemeasurable,
    (measurable_continuousunitIntervalPath B hcontinuous hmeasurable).aemeasurable,
    ?_⟩
  simpa only [pathLaw, brownianLaw, normalizedLinearPathLaw,
    ProbabilityMeasure.coe_mk] using hpathLaw

end ProbabilityTheory.RandomWalk
