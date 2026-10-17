/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Equal-partition parameters

The public definitions in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.partitionTubeParameter`:
  $\alpha_{m,k}=(1-k/m)/(1+1/m)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.partitionTubeWidth`:
  the widened width $(1+1/m)\Delta$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.smallDeviationBlockFactor`:
  $\lfloor un^v/(2d)\rfloor+1$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.smallDeviationBlockLength`:
  $n^2(\lfloor un^v/(2d)\rfloor+1)$.

The equal-partition parameters are the finite cover used in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.2 and its following remark.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open scoped NNReal

/-- Parameter of the `k`-th fixed corridor in an equal partition. -/
noncomputable def partitionTubeParameter (m : ℕ) (k : Fin m) : ℝ :=
  (1 - (k : ℝ) / m) / (1 + 1 / m)

/-- Width of the fixed corridor obtained by enlarging a tube by `1 + 1/m`. -/
noncomputable def partitionTubeWidth (m : ℕ) (width : ℝ) : ℝ :=
  (1 + 1 / m) * width

/-- Number of equal-length subblocks at width index `n` and remainder
coefficient `u`; the factor `1/2` leaves room for floor rounding. -/
noncomputable def smallDeviationBlockFactor (u v d : ℝ) (n : ℕ) : ℕ :=
  ⌊u * (n : ℝ) ^ v / (2 * d)⌋₊ + 1

/-- Length of an iterated equal-partition block at width index `n`. -/
noncomputable def smallDeviationBlockLength (u v d : ℝ) (n : ℕ) : ℕ :=
  n ^ 2 * smallDeviationBlockFactor u v d n

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
