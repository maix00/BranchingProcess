/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Normal.Tightness
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.ProcessExistence
public import Probability.Distributions.Stable.Attraction.Normal
public import Probability.Distributions.Stable.Gaussian
public import Probability.Distributions.Moments.Real
public import Probability.Distributions.Rademacher
public import Probability.Process.Stable.Brownian

/-!
# A pre-Brownian process from the Gaussian random-walk path limit

The public theorem in this file is:

- `exists_preBrownianReal_cadlag`: there is a probability space carrying a
  càdlàg process $B$ with independent increments
  $B_t-B_s\sim N(0,t-s)$ for $0\le s\le t$.

The construction takes a subsequential path-law limit of the centered
Rademacher walk through normal-domain tightness and the stable-process
existence theorem. This is the Gaussian functional limit used in the proof
of Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with
infinite offspring*, Chapter 3, Lemma 3.5. Path continuity is a separate
assertion from these finite-dimensional laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

/-- A probability space carrying Gaussian Brownian finite-dimensional laws
and a càdlàg stable-Lévy realization exists without a Brownian witness as an
input. -/
theorem exists_preBrownianReal_cadlag :
    ∃ (Q : ProbabilityMeasure (ℕ → CadlagPath unitInterval ℝ))
      (B : ℝ≥0 → (ℕ → CadlagPath unitInterval ℝ) → ℝ),
      IsPreBrownianReal B (Q : Measure _) ∧
      IsStableLevyProcess 2 (gaussianReal 0 (1 : ℝ≥0)) B
        (Q : Measure _) := by
  have hRademacher : IsCenteredUnitSecondMoment rademacherMeasure := by
    constructor <;> rw [integral_rademacherMeasure] <;> norm_num
  have hSquare : Integrable (fun x : ℝ => x ^ 2) rademacherMeasure := by
    exact (memLp_two_iff_integrable_sq
      stronglyMeasurable_id.aestronglyMeasurable).mp
        hRademacher.memLp_two
  have hSecondPositive : 0 < ∫ x : ℝ, x ^ 2 ∂rademacherMeasure := by
    rw [hRademacher.2]
    norm_num
  have hDOA : IsInDomainOfAttractionAlong rademacherMeasure
      (gaussianReal 0 1) (fun n => Real.sqrt n) (fun _ => 0) := by
    simpa [hRademacher.2] using
      isInDomainOfAttractionAlong_gaussianReal_zero_one_of_centered_integrable_sq
        rademacherMeasure hRademacher.1 hSquare hSecondPositive
  have hPositiveScale : ∀ n : ℕ, 0 < n → 0 < Real.sqrt n := by
    intro n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hTight :=
    RandomWalk.FunctionalLimit.Normal.isTightMeasureSet_range_normalizedStepPathLaw_of_gaussian
      hDOA hPositiveScale
  have hStable : IsStrictlyAlphaStable 2 (gaussianReal 0 1) :=
    isStrictlyAlphaStable_gaussianReal_zero (by norm_num)
  obtain ⟨Q, B, hB⟩ :=
    RandomWalk.FunctionalLimit.Stable.exists_stableLevyProcess_of_tightSource
      hDOA hStable hTight
  letI : IsProbabilityMeasure (Q : Measure (ℕ → CadlagPath unitInterval ℝ)) :=
    Q.property
  exact ⟨Q, B, hB.isPreBrownianReal_of_standardGaussian, hB⟩

end ProbabilityTheory

end
