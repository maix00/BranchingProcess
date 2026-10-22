/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Blocks.Bound
import Probability.MeasureTheory.Asymptotics.ProbabilityRate
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Proof lemma for the fixed-cover logarithmic transfer

The block estimate is converted to the Mogulskii normalization with the
complete-block count. A lower coboundedness hypothesis is kept explicit here;
the matching lower-bound argument is responsible for discharging it in the
two-sided theorem.
The proof-specific declaration `limsup_scaledLog_horizontalTubeProbability_le_of_fixedCover`
states the following.  If the increments are centered with second moment one
and admit the continuous Brownian realization in the theorem, the scale is
an `IsMogulskiiScale`, $c,\varepsilon>0$, the finite-cover
spectral and range factors at $u=(1+\varepsilon)/\sqrt c$ are both below
$1/2$, the tube probabilities $p_n$ are eventually positive, and
$\frac{s_n^2}{n}\log p_n$ is lower-cobounded, then
\[
  \limsup_{n\to\infty}\frac{s_n^2}{n}\log p_n
  \le \frac1c\log\!\left(2\,\texttt{finiteCoverRangeBound}
    \left(m,\frac{1+\varepsilon}{\sqrt c}\right)\right),
  \qquad
  p_n=\texttt{horizontalTubeProbability}
    (\texttt{iidSequenceLaw}(\nu),1/2,s_n,n).
\]
Its block estimate uses the continuous-path Donsker theorem formalized as
`ProbabilityTheory.RandomWalk.tendstoInDistribution_normalizedLinearContinuousPath_brownian`,
corresponding to Theorem 4.20 in I. Karatzas and S. E. Shreve,
*Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in
Mathematics 113, Springer (1991), DOI 10.1007/978-1-4612-0949-2.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii



/-- A fixed finite-cover block bound gives the corresponding normalized
logarithmic `limsup`, provided the tube probabilities are eventually
positive. The separate lower-bound route supplies the lower coboundedness
needed for a real-valued `limsup`. -/
lemma limsup_scaledLog_horizontalTubeProbability_le_of_fixedCover
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant enlargement : ℝ} {count : ℕ}
    (hconstant : 0 < constant) (henlargement : 0 < enlargement)
    (hcount : 0 < count)
    (hspectral : finiteCoverCorridorExponential count
      ((1 + enlargement) / Real.sqrt constant) < 1 / 2)
    (hbound : finiteCoverRangeBound count
      ((1 + enlargement) / Real.sqrt constant) < 1 / 2)
    (hpositive : ∀ᶠ n : ℕ in atTop,
      0 < horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n)
    (hlowerCobounded : Filter.IsCoboundedUnder (· ≤ ·) atTop
      (fun n => scale n ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν)
          (1 / 2) (scale n) n).toReal)) :
    atTop.limsup (fun n => scale n ^ 2 / (n : ℝ) * Real.log
      (horizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n).toReal) ≤
      (1 / constant) * Real.log
        (2 * finiteCoverRangeBound count
          ((1 + enlargement) / Real.sqrt constant)) := by
  let blockLength : ℕ → ℕ := diffusiveBlockLength constant scale
  let blockCount : ℕ → ℕ := fun n => n / blockLength n
  let q : ℝ := 2 * finiteCoverRangeBound count
    ((1 + enlargement) / Real.sqrt constant)
  let probability : ℕ → ENNReal := fun n =>
    horizontalTubeProbability (iidSequenceLaw ν) (1 / 2) (scale n) n
  let coefficient : ℕ → ℝ := fun n =>
    (blockCount n : ℝ) * scale n ^ 2 / (n : ℝ)
  have hqPos : 0 < q := by
    dsimp [q, finiteCoverRangeBound, finiteCoverCorridorExponential]
    positivity
  have hqOne : q < 1 := by
    dsimp [q]
    linarith [hbound]
  have hblock := eventually_horizontalTubeProbability_le_pow_fixedCover
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hscale
    hconstant henlargement hcount hspectral
  have hprobabilityOne : ∀ n, probability n ≤ 1 := by
    intro n
    change iidSequenceLaw ν
      {increment | InHorizontalTube (1 / 2) (scale n) n increment} ≤ 1
    calc
      iidSequenceLaw ν
          {increment | InHorizontalTube (1 / 2) (scale n) n increment} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hcoefficient : Tendsto coefficient atTop (nhds (1 / constant)) := by
    simpa [coefficient, blockCount, blockLength] using
      _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsMogulskiiScale.tendsto_completeBlockCount_mul_sq_div hscale hconstant
  have hrateCoefficient : Tendsto
      (fun n => scale n ^ 2 / (n : ℝ) * (blockCount n : ℝ))
      atTop (nhds (1 / constant)) := by
    have heq : (fun n => scale n ^ 2 / (n : ℝ) * (blockCount n : ℝ)) =
        coefficient := by
      funext n
      dsimp [coefficient]
      ring
    rw [heq]
    exact hcoefficient
  exact ProbabilityTheory.limsup_probabilityRate_le_of_eventually_le_pow
    hqPos hprobabilityOne (by simpa [probability, q, blockCount, blockLength] using hblock)
    (by simpa [probability] using hpositive)
    (Filter.Eventually.of_forall fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    hrateCoefficient (by simpa [probability] using hlowerCobounded)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
