/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic

/-!
# Horizontal staircase block tubes

The public definitions in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseLowerEdge`:
  $r_{t_{j+1}}=r+c t_{j+1}/\Delta^2$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseTubeWidth`:
  $\Delta(j)=\Delta-c|I_j|/\Delta^2$.

These are the horizontal sub-tubes $H_j=[r_{t_{j+1}},s_{t_j}]$ in the proof
of Lemma 3.5, Chapter 3 of Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring*.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Lower edge of the horizontal sub-tube in one staircase block. -/
noncomputable def staircaseLowerEdge (base drift width : ℝ)
    (start : ℕ → ℕ) (j : ℕ) : ℝ :=
  base + drift * (start (j + 1) : ℝ) / width ^ 2

/-- Width of the horizontal sub-tube during one block. -/
noncomputable def staircaseTubeWidth (width drift : ℝ)
    (length : ℕ → ℕ) (j : ℕ) : ℝ :=
  width - drift * (length j : ℝ) / width ^ 2

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
