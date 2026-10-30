/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Scale.Basic
public import Probability.Sequence.IID.Basic
import Probability.Process.Brownian.SmallDeviation.Range.UpperRate
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Bounds.Lemmas.SharpUpper.LogarithmicTransfer
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Rate.Bounds.Lemmas.SharpUpper.FiniteCoverParameters

/-!
# Sharp horizontal-tube upper rate

This is the finite-variance horizontal-tube upper bound in A. A. Mogul'skii,
Theorem 3, Section 4, p. 764, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.

## Public declarations

The public declaration
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
Its proof uses the Brownian fixed-cover range estimate in
`Probability/Process/Brownian/SmallDeviation/Range/` and the block estimate
under this module’s `Lemmas/SharpUpper/` proof chain. The block step uses the continuous-path Donsker theorem
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
