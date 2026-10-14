/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Binning.FiniteThreshold
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Binning.Parameters
/-!
# Uniform exponential bound for narrowed staircase bins

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_uniform_staircaseBinProbability_ge_exp`:
  after choosing finitely many narrowed tubes, fixed interior terminal
  fractions, and a common margin, one width and time-ratio threshold
  controls every bin. A quantitative comparison of the rounded narrowed
  width with the global width gives the exponential bound at the latter.

This is the fixed-spatial-bin application of Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, Lemma 3.1(ii), inside the proof of Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The finitely many narrowed horizontal tubes have a common real-width
threshold, and their probability bounds use the global width exponent. -/
theorem exists_uniform_staircaseBinProbability_ge_exp
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d u v : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (m : ℕ) (hm : 2 ≤ m)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ,
      ∀ width v₁ v₂ margin globalWidth target : ℝ,
        0 < width → 0 < margin → 0 < globalWidth →
        width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
        staircaseBinEndpointLowerFraction m v₁ + margin ≤ u →
        v + margin ≤ staircaseBinEndpointUpperFraction m v₂ →
        d * globalWidth ^ 2 ≤ target * (⌊width⌋₊ : ℝ) ^ 2 →
        ∀ horizon : ℕ,
          ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
          ∀ l : ℕ, l < m →
            ENNReal.ofReal (Real.exp
              (-target * (horizon : ℝ) / globalWidth ^ 2)) ≤
            horizontalTubeEndpointWindowProbability
              (iidSequenceLaw ν) (staircaseBinTubeParameter m l)
              width horizon
              (staircaseBinEndpointLowerFraction m v₁)
              (staircaseBinEndpointUpperFraction m v₂) := by
  let parameter : Fin m → ℝ := fun l => staircaseBinTubeParameter m l
  obtain ⟨width₀, ratio₀, huniform⟩ :=
    exists_uniform_finiteRealWidthTubeProbability_ge_exp
      hν hsigma parameter (fun _ => u) (fun _ => v)
        (fun l => staircaseBinTubeParameter_pos hm l.isLt)
        (fun _ => staircaseBinTubeParameter_lt_one hm)
        (fun _ => hu) (fun _ => huv) (fun _ => hv) hd
  refine ⟨max 1 width₀, ratio₀, ?_⟩
  intro width v₁ v₂ margin globalWidth target
    hwidth hmargin hglobalWidth hwidth₀ hwidthMargin
    hmarginLower hmarginUpper hscale horizon hratio l hl
  have hfloor : 0 < (⌊width⌋₊ : ℝ) := by
    have hfloorGe : 1 ≤ ⌊width⌋₊ := by
      exact (le_max_left _ _).trans hwidth₀
    exact_mod_cast hfloorGe
  have hwidth₀' : width₀ ≤ ⌊width⌋₊ :=
    (le_max_right _ _).trans hwidth₀
  have hsource := huniform ⟨l, hl⟩ width
    (staircaseBinEndpointLowerFraction m v₁)
    (staircaseBinEndpointUpperFraction m v₂)
    margin hwidth hmargin hwidth₀' hwidthMargin
    hmarginLower hmarginUpper horizon hratio
  exact realWidthTubeProbability_ge_exp_globalScale
    hfloor hglobalWidth hscale hsource

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
