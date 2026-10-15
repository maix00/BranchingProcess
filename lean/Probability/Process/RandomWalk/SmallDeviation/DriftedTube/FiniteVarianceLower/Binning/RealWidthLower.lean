/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Basic

/-!
# Real-width lower bound from the integer-width endpoint rate

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp`:
  fixed interior endpoint fractions $u<v$ and a positive margin inside
  a real-width endpoint window $[U,V]$ give the integer-width exponential
  lower bound at $\lfloor D\rfloor$ for the real-width tube at $D$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.realWidthTubeProbability_ge_exp_globalScale`:
  if $d\Delta^2\le d''\lfloor D\rfloor^2$, the resulting exponent
  is bounded below by $-d''n/\Delta^2$.

This is the integer-to-real width transfer required when Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5, applies Lemma 3.1(ii) to the narrowed
staircase tubes. The underlying rate is Mogul'skii,
"Small Deviations in a Space of Trajectories," Theorem 3, Section 4,
p. 764 (DOI 10.1137/1119081).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Uniform exponential lower bound for a real-width tube, with an
endpoint interval containing a fixed strict interior interval. -/
theorem exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d a u v : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ, ∀ width U V margin : ℝ,
      0 < width → 0 < margin →
      width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
      U + margin ≤ u → v + margin ≤ V →
      ∀ horizon : ℕ,
        ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
        ENNReal.ofReal (Real.exp
          (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
        horizontalTubeEndpointWindowProbability
          (iidSequenceLaw ν) a width horizon U V := by
  obtain ⟨width₀, ratio₀, hinteger⟩ :=
    exists_eventually_horizontalTubeEndpointWindowProbability_ge_exp_uniform
      hν hsigma ha haOne hu huv hv hd
  refine ⟨width₀, ratio₀, ?_⟩
  intro width U V margin hwidth hmargin hwidthFloor hwidthMargin
    hmarginLower hmarginUpper horizon hratio
  have hsource := hinteger ⌊width⌋₊ hwidthFloor horizon hratio
  have hsubset :=
    horizontalTubeEndpointWindowEvent_floor_subset_of_endpointMargins
      hwidth.le ha.le haOne.le hu.le huv.le hv.le
      hmargin hwidthMargin hmarginLower hmarginUpper
      (horizon := horizon)
  exact hsource.trans (measure_mono hsubset)

/-- Compare the narrowed tube's rounded-width exponent with the global
staircase width, as in Wang Yiyang, Chapter 3, proof of Lemma 3.5. -/
theorem realWidthTubeProbability_ge_exp_globalScale
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {a width U V globalWidth d target : ℝ} {horizon : ℕ}
    (hfloor : 0 < (⌊width⌋₊ : ℝ))
    (hglobalWidth : 0 < globalWidth)
    (hscale : d * globalWidth ^ 2 ≤
      target * (⌊width⌋₊ : ℝ) ^ 2)
    (hsource : ENNReal.ofReal (Real.exp
      (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
      horizontalTubeEndpointWindowProbability
        (iidSequenceLaw ν) a width horizon U V) :
    ENNReal.ofReal (Real.exp
      (-target * (horizon : ℝ) / globalWidth ^ 2)) ≤
      horizontalTubeEndpointWindowProbability
        (iidSequenceLaw ν) a width horizon U V := by
  have hrate : d / (⌊width⌋₊ : ℝ) ^ 2 ≤
      target / globalWidth ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hfloor)
      (sq_pos_of_pos hglobalWidth)).2
    nlinarith [hscale]
  have hmul := mul_le_mul_of_nonneg_right hrate
    (Nat.cast_nonneg horizon : 0 ≤ (horizon : ℝ))
  have hexponent :
      -target * (horizon : ℝ) / globalWidth ^ 2 ≤
      -d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2 := by
    calc
      -target * (horizon : ℝ) / globalWidth ^ 2 =
          -(target / globalWidth ^ 2 * (horizon : ℝ)) := by ring
      _ ≤ -(d / (⌊width⌋₊ : ℝ) ^ 2 * (horizon : ℝ)) :=
        neg_le_neg hmul
      _ = -d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2 := by ring
  exact (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)).trans
    hsource

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
