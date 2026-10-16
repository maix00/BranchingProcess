/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Defs
public import Algebra.BigOperators.AdditivePath.Basic
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core

/-!
# Horizontal tubes with endpoint windows

The public definition in this file is
`ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.relativeHorizontalTubeEndpointWindowEvent`: for a lower edge $r$, width $\Delta$, horizon $L$, and endpoint fractions $u,v$, it describes paths satisfying $r\le Y_j\le r+\Delta$ for $1\le j\le L$ and $Y_L\in[r+u\Delta,r+v\Delta]$.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open ProbabilityTheory.RandomWalk

/-- A horizontal tube with a specified lower edge and endpoint window. -/
def relativeHorizontalTubeEndpointWindowEvent (lower width : ℝ)
    (horizon : ℕ) (v₁ v₂ : ℝ) : Set (ℕ → ℝ) :=
  {increment | (∀ k : Fin horizon,
      lower ≤ AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤ lower + width) ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc (lower + v₁ * width) (lower + v₂ * width)}


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
