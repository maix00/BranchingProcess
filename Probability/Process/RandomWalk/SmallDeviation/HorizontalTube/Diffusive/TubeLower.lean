/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Distributions.Moments.Real
public import Probability.Sequence.IID.Basic
import Mathlib.Probability.BrownianMotion.Basic
import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Corridor.Brownian.Basic
import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Basic

import Probability.Process.Brownian.PathLaw.ContinuousModification
import Probability.Process.Brownian.Construction.Existence
import Probability.Process.Brownian.SmallDeviation.Corridor.Bounds

/-!
# Donsker lower bounds for centered random-walk tubes

## Public declarations

The public declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.ofReal_exp_neg_pi_sq_div_two_rho_sq_innerWidth_sq_le_liminf_centeredStrictTube`:
  for centered unit-variance increments, $0<\rho<1$, and
  $0<w_{\mathrm{in}}<w$, the `liminf` probability of the strict tube of width
  $w\sqrt n$ is at least $\exp(-\pi^2/(2\rho^2w_{\mathrm{in}}^2))$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.ofReal_exp_neg_pi_sq_div_two_le_liminf_centeredStrictTube`:
  for every $w>1$, the same `liminf` probability is at least
  $\exp(-\pi^2/2)$.

These are general horizontal-tube estimates for centered unit-variance
increment laws. Their proof uses Brownian corridor bounds and the Donsker
corridor comparison; no Mogul'skii scale or article-specific hypothesis is
needed. The functional-limit input is Donsker's Theorem 4.20 in I. Karatzas
and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed.,
Graduate Texts in Mathematics 113, Springer (1991), DOI
10.1007/978-1-4612-0949-2. The quantitative Brownian corridor bound is
proved in `Probability.Process.Brownian.SmallDeviation.Corridor.Bounds`.
-/

open Filter MeasureTheory ProbabilityTheory Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- A closed Brownian corridor strictly inside the discrete tube gives a
lower bound for the `liminf` probability of the corresponding strict tubes.
The inner corridor is kept explicit because it is the source of the spectral
constant; taking it close to the outer width recovers the sharp rate. -/
theorem ofReal_exp_neg_pi_sq_div_two_rho_sq_innerWidth_sq_le_liminf_centeredStrictTube
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {rho innerWidth width : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1)
    (hinnerWidth : 0 < innerWidth) (hgap : innerWidth < width) :
    ENNReal.ofReal (Real.exp
      (-(Real.pi ^ 2) / (2 * rho ^ 2 * innerWidth ^ 2))) ≤
      atTop.liminf (fun n : ℕ =>
        iidSequenceLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (width * Real.sqrt n) n increment}) := by
  obtain ⟨Q, B, hB, _, _⟩ := exists_brownianReal
  let P : Measure (ℕ → CadlagPath unitInterval ℝ) := Q
  letI : IsProbabilityMeasure P := Q.property
  have hclosed :=
    IsBrownianReal.measure_closedCorridor_lowerBound_of_rho_width
      hrho hrho_one hinnerWidth hB
  have hwidth : 0 < width := hinnerWidth.trans hgap
  have hclosedOpen :
      ENNReal.ofReal (Real.exp
        (-(Real.pi ^ 2) / (2 * rho ^ 2 * innerWidth ^ 2))) ≤
        P.map (Skorokhod.ofContinuousMap ∘
          continuousunitIntervalPath
            (hB.toIsPreBrownianReal.continuousModification)
            (hB.toIsPreBrownianReal.continuous_continuousModification))
          (Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2)) := by
    refine hclosed.trans (measure_mono ?_)
    intro path hpath
    rw [Skorokhod.mem_rangeInOpenInterval_iff]
    refine ⟨(width - innerWidth) / 2, by linarith, fun t => ?_⟩
    have ht := (Skorokhod.mem_rangeInClosedInterval_iff.mp hpath) t
    constructor <;> nlinarith [ht.1, ht.2]
  exact hclosedOpen.trans
    (brownian_centeredSkorokhodCorridor_le_liminf_strictTube
      ν hν hB hwidth)

/-- For every centered unit-variance increment law, the sharp Brownian unit
corridor constant is a lower bound for the `liminf` probability of every
strictly wider diffusive tube. This lower bound applies to every centered
unit-variance increment law. -/
theorem ofReal_exp_neg_pi_sq_div_two_le_liminf_centeredStrictTube
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : IsCenteredUnitSecondMoment nu)
    {width : ℝ} (hwidth : 1 < width) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      atTop.liminf (fun n : ℕ =>
        iidSequenceLaw nu
          {increment | InOpenHorizontalTube (1 / 2)
            (width * Real.sqrt n) n increment}) := by
  obtain ⟨Q, B, hB, _, _⟩ := exists_brownianReal
  letI : IsProbabilityMeasure (Q : Measure (ℕ → CadlagPath unitInterval ℝ)) := Q.property
  exact (IsBrownianReal.measure_openCorridor_lowerBound
    hB hwidth).trans
      (brownian_centeredSkorokhodCorridor_le_liminf_strictTube
        nu hnu hB (by linarith))


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
