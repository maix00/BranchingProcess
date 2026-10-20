/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Blocks.Bound
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Rate.SmallWidth
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Rate.Lemmas.LogarithmicTransfer
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Rate.Lemmas.FiniteCoverParameters

/-!
# Sharp horizontal upper rate from the fixed-cover block route

This file composes the fixed-parameter block estimate with the explicit
parameter selection. Positivity and lower coboundedness remain hypotheses
until the matching lower-rate proof supplies them.  The public declaration
`limsup_scaledLog_horizontalTubeProbability_le_sharp` states that for
centered unit-variance increments with a continuous Brownian realization,
an `IsMogulskiiScale` $s_n$, eventually positive tube probabilities $p_n$,
and a lower-cobounded normalized logarithm,
\[
  \limsup_{n\to\infty}\frac{s_n^2}{n}\log p_n
  \le -\frac{\pi^2}{2},
  \qquad
  p_n=\texttt{horizontalTubeProbability}
    (\texttt{iidSequenceLaw}(\nu),1/2,s_n,n).
\]
The fixed-cover block step uses the continuous-path Donsker theorem
formalized as
`ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_brownian`,
corresponding to Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


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
      0 < horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n)
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => scale n ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) :
    atTop.limsup (fun n => scale n ^ 2 / (n : ℝ) * Real.log
      (horizontalTubeProbability (iidSequenceLaw ν)
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
