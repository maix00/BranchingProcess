/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Basic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core

/-!
# Horizontal-tube event with a terminal window

The public declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.horizontalTubeEndpointWindowEvent`:
  $T_{a,D,L}\cap\{(u-a)D\le S_L\le(v-a)D\}$, where
  $T_{a,D,L}=\{S_j\in[-aD,(1-a)D]:1\le j\le L\}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.horizontalTubeEndpointWindowProbability`:
  $\mu(T_{a,D,L}\cap\{(u-a)D\le S_L\le(v-a)D\})$ under the supplied
  increment-sequence law $\mu$.

These are the events in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Chapter 3, Lemma 3.1(ii).
-/

open MeasureTheory
open ProbabilityTheory.RandomWalk
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A closed horizontal tube together with a fixed terminal window, as in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 3,
Lemma 3.1(ii). -/
def horizontalTubeEndpointWindowEvent (a width : ℝ) (horizon : ℕ)
    (u v : ℝ) : Set (ℕ → ℝ) :=
  {increment | InHorizontalTube a width horizon increment ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc ((u - a) * width) ((v - a) * width)}

/-- The probability of a fixed endpoint window inside a closed horizontal
tube, as in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (master's thesis, Fudan University, 2026), Chapter 3,
Lemma 3.1(ii). -/
def horizontalTubeEndpointWindowProbability (law : Measure (ℕ → ℝ))
    (a width : ℝ) (horizon : ℕ) (u v : ℝ) : ℝ≥0∞ :=
  law (horizontalTubeEndpointWindowEvent a width horizon u v)

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
