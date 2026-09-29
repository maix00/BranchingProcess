module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Range.LogRate
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Range.Parameters

/-!
# Sharp horizontal upper rate from the fixed-cover block route

This file composes the fixed-parameter block estimate with the explicit
parameter selection. Positivity and lower coboundedness remain hypotheses
until the matching lower-rate proof supplies them.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- Once the horizontal tube probabilities are eventually positive and their
normalized logarithms are lower-cobounded, the finite-cover Donsker block
route gives the sharp Mogulskii upper rate. -/
theorem limsup_scaledLog_horizontalTubeProbability_le_sharp
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < horizontalTubeProbability (independentIncrementLaw ν)
        (1 / 2) (scale n) n)
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => scale n ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (independentIncrementLaw ν)
          (1 / 2) (scale n) n).toReal)) :
    atTop.limsup (fun n => scale n ^ 2 / (n : ℝ) * Real.log
      (horizontalTubeProbability (independentIncrementLaw ν)
        (1 / 2) (scale n) n).toReal) ≤ -(Real.pi ^ 2) / 2 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨count, hcount, enlargement, C, henlargement, hC,
      hspectral, hbound, hparameter⟩ :=
    exists_finiteCover_parameters_for_sharp_rate hε
  have hfixed := limsup_scaledLog_horizontalTubeProbability_le_of_fixedCover
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hscale
    hC henlargement hcount hspectral hbound hpositive hlowerCobounded
  exact le_trans hfixed hparameter.le

end ProbabilityTheory.RandomWalk.Mogulskii

end
