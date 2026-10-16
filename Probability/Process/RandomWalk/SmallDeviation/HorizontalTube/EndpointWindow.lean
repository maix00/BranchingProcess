/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Constructions.Pi
public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Basic

/-!
# Horizontal tubes with endpoint windows

The public definitions in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.relativeHorizontalTubeEndpointWindowEvent`: for a lower edge $r$, width $\Delta$, horizon $L$, and endpoint fractions $u,v$, it describes paths satisfying $r\le Y_j\le r+\Delta$ for $1\le j\le L$ and $Y_L\in[r+u\Delta,r+v\Delta]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeEndpointWindowEvent`: for tube parameter $a$, width $\Delta$, and horizon $L$, it describes paths satisfying $-a\Delta\le Y_j\le(1-a)\Delta$ and $(u-a)\Delta\le Y_L\le(v-a)\Delta$. This is the event used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii).
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.horizontalTubeEndpointWindowProbability`: the probability of that normalized tube event under a law on increment sequences.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open ProbabilityTheory.RandomWalk
open MeasureTheory
open scoped ENNReal

/-- A horizontal tube with a specified lower edge and endpoint window. -/
def relativeHorizontalTubeEndpointWindowEvent (lower width : ℝ)
    (horizon : ℕ) (v₁ v₂ : ℝ) : Set (ℕ → ℝ) :=
  {increment | (∀ k : Fin horizon,
      lower ≤ AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤ lower + width) ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc (lower + v₁ * width) (lower + v₂ * width)}

/-- The closed tube with walls `-a * width` and `(1 - a) * width`, together
with a terminal interval from `(u - a) * width` to `(v - a) * width`.
This is the normalized endpoint-window form used in finite-variance tube
estimates, as in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (master's thesis, Fudan University, 2026), Chapter 3,
Lemma 3.1(ii). -/
def horizontalTubeEndpointWindowEvent (a width : ℝ) (horizon : ℕ)
    (u v : ℝ) : Set (ℕ → ℝ) :=
  {increment | InHorizontalTube a width horizon increment ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc ((u - a) * width) ((v - a) * width)}

/-- The probability, under a law on increment sequences, of remaining in a
closed horizontal tube and ending in the prescribed terminal interval. -/
def horizontalTubeEndpointWindowProbability (law : Measure (ℕ → ℝ))
    (a width : ℝ) (horizon : ℕ) (u v : ℝ) : ℝ≥0∞ :=
  law (horizontalTubeEndpointWindowEvent a width horizon u v)


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
