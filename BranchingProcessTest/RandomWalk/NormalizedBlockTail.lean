/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.RandomWalk.Path.Truncation.Normalized

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk

example (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (sampleSize length : ℕ)
    {scale radiusMultiplier thresholdMultiplier δ tailBound momentBound : ℝ}
    (hsample : 0 < sampleSize) (hscale : 0 < scale) (hlength : 0 < length)
    (hthreshold : 0 < thresholdMultiplier)
    (hδ : 0 ≤ δ) (htailBound : 0 ≤ tailBound) (hmomentBound : 0 ≤ momentBound)
    (hlengthRatio : (length : ℝ) / sampleSize ≤ δ)
    (htail : (sampleSize : ℝ) *
      ν.real {x : ℝ | radiusMultiplier * scale < |x|} ≤ tailBound)
    (hmoment : (sampleSize : ℝ) *
      truncatedSecondMoment ν (radiusMultiplier * scale) / scale ^ 2 ≤ momentBound)
    (hbias : (length : ℝ) *
      |truncatedIncrementMean ν (radiusMultiplier * scale)| / scale ≤
        thresholdMultiplier / 2) :
    (iidSequenceLaw ν)
        (blockPrefixExceedance 0 length (thresholdMultiplier * scale)) ≤
      ENNReal.ofReal
        (δ * (tailBound + 4 * momentBound / thresholdMultiplier ^ 2)) :=
  measure_blockPrefixExceedance_le_of_normalizedTruncationBounds
    ν sampleSize length hsample hscale hlength hthreshold hδ
    htailBound hmomentBound hlengthRatio htail hmoment hbias

#print axioms
  ProbabilityTheory.RandomWalk.measure_blockPrefixExceedance_le_of_normalizedTruncationBounds
