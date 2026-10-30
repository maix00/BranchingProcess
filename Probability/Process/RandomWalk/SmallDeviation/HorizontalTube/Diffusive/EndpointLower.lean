/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Endpoint
public import Probability.Distributions.Moments.Real
public import Probability.Sequence.IID.Basic

import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Topology.UnitInterval
import Probability.Process.Brownian.SmallDeviation.Corridor.Endpoint
import Probability.Process.Brownian.PathLaw.ContinuousModification
import Probability.Process.Brownian.Construction.Existence
import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Skorokhod
import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Corridor.Brownian.Endpoint

/-!
# Diffusive endpoint-constrained random-walk tube estimate

## Public declarations

For increments $\xi=(\xi_i)_{i\ge0}$, write
$S_j=\sum_{i=0}^{j-1}\xi_i$.

The public declaration is
`ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.ofReal_exp_neg_pi_sq_div_two_le_liminf_centeredStrictTubeEndsIn`.
For centered unit-variance increments, $w>1$, and
$\ell<-1/2<1/2<u$,
\[
 e^{-\pi^2/2}\le\liminf_{n\to\infty}\mathbb P_\nu\!\left(
  S_j\in\left(-\frac{w\sqrt n}{2},\frac{w\sqrt n}{2}\right)
  \ (1\le j\le n),\quad \frac{S_n}{\sqrt n}\in(\ell,u)
 \right).
\]
This is the Donsker transfer of the Brownian endpoint-constrained corridor
estimate. The functional-limit input is Donsker's Theorem 4.20 in I.
Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd
ed., Graduate Texts in Mathematics 113, Springer (1991), DOI
10.1007/978-1-4612-0949-2. The terminal-interval Brownian lower bound is
proved in `Probability.Process.Brownian.SmallDeviation.Corridor.Endpoint`.
-/

open Filter MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- For centered unit-variance increments and $w>1$, the principal Brownian
constant satisfies
\[
 e^{-\pi^2/2}\le\liminf_{n\to\infty}\mathbb P_\nu\!\left(
  S_j\in\left(-\frac{w\sqrt n}{2},\frac{w\sqrt n}{2}\right)
  \ (1\le j\le n),\quad \frac{S_n}{\sqrt n}\in(\ell,u)
 \right)
\]
whenever $\ell<-1/2<1/2<u$. -/
theorem ofReal_exp_neg_pi_sq_div_two_le_liminf_centeredStrictTubeEndsIn
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {width endpointLower endpointUpper : ℝ}
    (hwidth : 1 < width)
    (hendpointLower : endpointLower < -(1 / 2 : ℝ))
    (hendpointUpper : (1 / 2 : ℝ) < endpointUpper) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      atTop.liminf (fun n : ℕ =>
        iidSequenceLaw ν {increment |
          InOpenHorizontalTube (1 / 2) (width * Real.sqrt n) n increment ∧
            AdditivePath.displacement n increment / Real.sqrt n ∈
              Set.Ioo endpointLower endpointUpper}) := by
  obtain ⟨Q, B, hB, _, _⟩ := exists_brownianReal
  letI : IsProbabilityMeasure (Q : Measure (ℕ → CadlagPath unitInterval ℝ)) := Q.property
  exact (IsBrownianReal.measure_openCorridor_endsIn_lowerBound
    hB hwidth hendpointLower hendpointUpper).trans
      (RandomWalk.brownian_centeredSkorokhodCorridorEndsIn_le_liminf_strictTubeEndsIn
        ν hν hB (by linarith))


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
