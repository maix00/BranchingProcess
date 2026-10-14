/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Staircase.Setup.Parameters
/-!
# Terminal windows of the horizontal staircase blocks

The public objects and theorems in this file are:

- `staircaseEndpointLowerFraction` and `staircaseEndpointUpperFraction`:
  the fractions $v_1(k),v_2(k)$ in Wang Yiyang's proof, using the next
  central window for nonfinal blocks and $[r_L,r_L+vD]$ for the last block.
- `staircaseEndpointWindow_interior`:
  an interior block's terminal interval equals the next central window.
- `staircaseEndpointWindow_last`:
  the last block's terminal interval equals $[r_L,r_L+vD]$.

These are the endpoint definitions and equalities in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
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

/-- A nonfinal block ends exactly in the central window of the following
horizontal tube. -/
theorem staircaseEndpointWindow_interior
    (base width drift endpointFraction : ℝ)
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (q j : ℕ) (hj : j + 1 < q)
    (hwidth : staircaseTubeWidth width drift length j ≠ 0) :
    Set.Icc
      (staircaseLowerEdge base drift width start j +
        staircaseEndpointLowerFraction q width drift length j *
          staircaseTubeWidth width drift length j)
      (staircaseLowerEdge base drift width start j +
        staircaseEndpointUpperFraction q width drift endpointFraction
          length j * staircaseTubeWidth width drift length j) =
    Set.Icc
      (staircaseLowerEdge base drift width start (j + 1) +
        staircaseTubeWidth width drift length (j + 1) / 3)
      (staircaseLowerEdge base drift width start (j + 1) +
        2 * staircaseTubeWidth width drift length (j + 1) / 3) := by
  have hlower :
      staircaseLowerEdge base drift width start j +
          staircaseEndpointLowerFraction q width drift length j *
            staircaseTubeWidth width drift length j =
        staircaseLowerEdge base drift width start (j + 1) +
          staircaseTubeWidth width drift length (j + 1) / 3 := by
    rw [staircaseEndpointLowerFraction, ite_eq_left hj,
      div_mul_cancel₀ _ hwidth]
    unfold staircaseLowerEdge staircaseTubeWidth
    rw [hnext (j + 1)]
    push_cast
    ring
  have hupper :
      staircaseLowerEdge base drift width start j +
          staircaseEndpointUpperFraction q width drift endpointFraction
            length j * staircaseTubeWidth width drift length j =
        staircaseLowerEdge base drift width start (j + 1) +
          2 * staircaseTubeWidth width drift length (j + 1) / 3 := by
    rw [staircaseEndpointUpperFraction, ite_eq_left hj,
      div_mul_cancel₀ _ hwidth]
    unfold staircaseLowerEdge staircaseTubeWidth
    rw [hnext (j + 1)]
    push_cast
    ring
  rw [hlower, hupper]

/-- The final block ends exactly in the specified final endpoint window. -/
theorem staircaseEndpointWindow_last
    (base width drift endpointFraction : ℝ)
    (start length : ℕ → ℕ)
    (q horizon : ℕ) (hq : 0 < q)
    (hfinish : start q = horizon)
    (hwidth : staircaseTubeWidth width drift length (q - 1) ≠ 0) :
    Set.Icc
      (staircaseLowerEdge base drift width start (q - 1) +
        staircaseEndpointLowerFraction q width drift length (q - 1) *
          staircaseTubeWidth width drift length (q - 1))
      (staircaseLowerEdge base drift width start (q - 1) +
        staircaseEndpointUpperFraction q width drift endpointFraction
          length (q - 1) *
          staircaseTubeWidth width drift length (q - 1)) =
    Set.Icc
      (base + drift * (horizon : ℝ) / width ^ 2)
      (base + drift * (horizon : ℝ) / width ^ 2 +
        endpointFraction * width) := by
  have hlast : ¬q - 1 + 1 < q := by omega
  have hlastEq : q - 1 + 1 = q := by omega
  rw [staircaseEndpointLowerFraction, ite_eq_right hlast,
    staircaseEndpointUpperFraction, ite_eq_right hlast,
    div_mul_cancel₀ _ hwidth]
  simp [staircaseLowerEdge, hlastEq, hfinish]

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
