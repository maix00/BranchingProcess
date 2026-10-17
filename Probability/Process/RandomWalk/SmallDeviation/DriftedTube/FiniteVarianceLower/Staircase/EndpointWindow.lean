/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.BlockTube

/-!
# Endpoint fractions for the staircase blocks

The public endpoint parameters are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseEndpointLowerFraction`
  and `staircaseEndpointUpperFraction`: the fractions locating the next
  central window, with the final interval $[r_L,r_L+v\Delta]$.
- `staircaseUpperEndpointLowerFraction` and
  `staircaseUpperEndpointUpperFraction`: the corresponding fractions when
  the final interval is adjacent to the upper edge of the tube.

These parameters encode the ordinary and final block windows in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- Fraction locating the lower endpoint of the next central window,
with zero as the lower fraction of the final endpoint window. -/
noncomputable def staircaseEndpointLowerFraction
    (q : ℕ) (width drift : ℝ) (length : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j + 1 < q then
    (width / 3 + (2 / 3 : ℝ) * drift * (length (j + 1) : ℝ) /
      width ^ 2) /
      staircaseTubeWidth width drift length j
  else 0

/-- Fraction locating the upper endpoint of the next central window,
or the final endpoint window on the last block. -/
noncomputable def staircaseEndpointUpperFraction
    (q : ℕ) (width drift endpointFraction : ℝ)
    (length : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j + 1 < q then
    (2 * width / 3 + (1 / 3 : ℝ) * drift *
      (length (j + 1) : ℝ) / width ^ 2) /
      staircaseTubeWidth width drift length j
  else endpointFraction * width /
    staircaseTubeWidth width drift length j

/-- Lower endpoint fraction for the same rising staircase when the final
window is adjacent to the upper edge of the target tube. -/
noncomputable def staircaseUpperEndpointLowerFraction
    (q : ℕ) (width drift endpointFraction : ℝ)
    (length : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j + 1 < q then
    staircaseEndpointLowerFraction q width drift length j
  else
    max (1 - endpointFraction) 0 * width /
      staircaseTubeWidth width drift length j

/-- Upper endpoint fraction for the same rising staircase. The final
horizontal block ends at its own upper edge. -/
noncomputable def staircaseUpperEndpointUpperFraction
    (q : ℕ) (width drift endpointFraction : ℝ)
    (length : ℕ → ℕ) (j : ℕ) : ℝ :=
  if j + 1 < q then
    staircaseEndpointUpperFraction q width drift endpointFraction length j
  else 1

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
