module

public import Probability.BranchingRandomWalk.Walk.FunctionalLimit.Donsker.Continuous
public import Probability.BranchingRandomWalk.Walk.Rademacher
public import Probability.Process.Brownian.Range
public import Probability.Process.Path.Oscillation

/-!
# Brownian range events through a fixed finite corridor cover

This is the corrected upper-bound interface: the finite cover is indexed by
the Brownian path's possible minimum locations, so its cardinality is fixed
before the discrete Donsker approximation is taken.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- Under the Rademacher Donsker limit, the Brownian range-oscillation mass
is bounded by the sum of the `liminf` masses of the fixed finite open
corridors in the minimum-location cover. -/
theorem brownianRangeOscillation_le_sum_liminf_fixedCorridors
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count) :
    P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
        (ProbabilityTheory.Process.Path.rangeOscillationSet width) ≤
      ∑ j : Fin count, atTop.liminf (fun n =>
        normalizedLinearPathLaw rademacherMeasure (fun n => Real.sqrt n) n
          (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j))) := by
  have hrademacher : IsCenteredUnitSecondMoment rademacherMeasure := by
    constructor <;> rw [integral_rademacherMeasure] <;> norm_num
  have hlimit :=
    tendstoInDistribution_normalizedLinearContinuousPath_brownian
      rademacherMeasure hrademacher.1 hrademacher.2 hB
      hcontinuous hmeasurable
  have hstart :=
    ProbabilityTheory.Process.Path.IsPreBrownianReal.ae_continuousunitIntervalPath_startsAtZero
      hB hcontinuous hmeasurable
  simpa only [normalizedLinearPathLaw] using
    ProbabilityTheory.Process.Path.TendstoInDistribution.measure_rangeOscillationSet_le_sum_liminf_finiteCorridorCover
      hlimit hwidth hcount hstart

end ProbabilityTheory.RandomWalk.Mogulskii

end
