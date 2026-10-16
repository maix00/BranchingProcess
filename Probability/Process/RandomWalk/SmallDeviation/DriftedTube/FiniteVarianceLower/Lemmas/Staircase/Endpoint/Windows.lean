/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Lemmas.Staircase.Setup.BlockTube
/-!
# Terminal windows of the horizontal staircase blocks

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseEndpointLowerFraction` and `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseEndpointUpperFraction`:
  the fractions $v_1(k),v_2(k)$ in Wang Yiyang's proof, using the next
  central window for nonfinal blocks and $[r_L,r_L+vD]$ for the last block.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseEndpointWindow_interior`:
  an interior block's terminal interval equals the next central window.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseEndpointWindow_last`:
  the last block's terminal interval equals $[r_L,r_L+vD]$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseUpperEndpointLowerFraction` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseUpperEndpointUpperFraction`:
  the same ordinary windows, with the final interval adjacent to the
  upper edge of the last horizontal block.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseUpperEndpointWindow_interior` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.staircaseUpperEndpointWindow_last_subset`:
  the ordinary windows still match the following central window, and
  the last window lies in both $[r_L,s_L]$ and $[s_L-vD,s_L]$.

These are the endpoint definitions and equalities in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
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
lemma staircaseEndpointWindow_interior
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
lemma staircaseEndpointWindow_last
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

/-- Ordinary endpoint windows of the upper-endpoint staircase agree with
those of the lower-endpoint staircase. -/
lemma staircaseUpperEndpointWindow_interior
    (base width drift endpointFraction : ℝ)
    (start length : ℕ → ℕ)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (q j : ℕ) (hj : j + 1 < q)
    (hwidth : staircaseTubeWidth width drift length j ≠ 0) :
    Set.Icc
      (staircaseLowerEdge base drift width start j +
        staircaseUpperEndpointLowerFraction q width drift
          endpointFraction length j *
          staircaseTubeWidth width drift length j)
      (staircaseLowerEdge base drift width start j +
        staircaseUpperEndpointUpperFraction q width drift
          endpointFraction length j *
          staircaseTubeWidth width drift length j) =
    Set.Icc
      (staircaseLowerEdge base drift width start (j + 1) +
        staircaseTubeWidth width drift length (j + 1) / 3)
      (staircaseLowerEdge base drift width start (j + 1) +
        2 * staircaseTubeWidth width drift length (j + 1) / 3) := by
  simp only [staircaseUpperEndpointLowerFraction,
    staircaseUpperEndpointUpperFraction, ite_eq_left hj]
  exact staircaseEndpointWindow_interior base width drift
    endpointFraction start length hnext q j hj hwidth

/-- The last horizontal upper-endpoint window lies inside both the full
terminal tube and its upper terminal window. -/
lemma staircaseUpperEndpointWindow_last_subset
    (base width drift endpointFraction : ℝ)
    (start length : ℕ → ℕ)
    (q horizon : ℕ) (hq : 0 < q)
    (hnext : ∀ j, start (j + 1) = start j + length j)
    (hfinish : start q = horizon)
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hblockWidth : staircaseTubeWidth width drift length (q - 1) ≠ 0) :
    Set.Icc
      (staircaseLowerEdge base drift width start (q - 1) +
        staircaseUpperEndpointLowerFraction q width drift
          endpointFraction length (q - 1) *
          staircaseTubeWidth width drift length (q - 1))
      (staircaseLowerEdge base drift width start (q - 1) +
        staircaseUpperEndpointUpperFraction q width drift
          endpointFraction length (q - 1) *
          staircaseTubeWidth width drift length (q - 1)) ⊆
    Set.Icc (base + drift * (horizon : ℝ) / width ^ 2)
        (base + drift * (horizon : ℝ) / width ^ 2 + width) ∩
      Set.Icc
        (base + drift * (horizon : ℝ) / width ^ 2 + width -
          endpointFraction * width)
        (base + drift * (horizon : ℝ) / width ^ 2 + width) := by
  have hlast : ¬q - 1 + 1 < q := by omega
  have hlastEq : q - 1 + 1 = q := by omega
  have hstartEnd : start (q - 1) + length (q - 1) = horizon := by
    rw [← hnext (q - 1), hlastEq, hfinish]
  have hstartLe : start (q - 1) ≤ horizon := by omega
  have hstartLeReal : (start (q - 1) : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hstartLe
  have hshift : drift * (start (q - 1) : ℝ) / width ^ 2 ≤
      drift * (horizon : ℝ) / width ^ 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstartLeReal hdrift)
      (sq_nonneg width)
  have hmax : 1 - endpointFraction ≤
      max (1 - endpointFraction) 0 := le_max_left _ _
  have hmaxNonneg : 0 ≤ max (1 - endpointFraction) 0 :=
    le_max_right _ _
  intro y hy
  have hlower :
      base + drift * (horizon : ℝ) / width ^ 2 +
          max (1 - endpointFraction) 0 * width ≤ y := by
    convert hy.1 using 1
    rw [staircaseUpperEndpointLowerFraction, ite_eq_right hlast,
      div_mul_cancel₀ _ hblockWidth]
    simp only [staircaseLowerEdge, hlastEq, hfinish]
  have hupper : y ≤
      base + drift * (start (q - 1) : ℝ) / width ^ 2 + width := by
    convert hy.2 using 1
    rw [staircaseUpperEndpointUpperFraction, ite_eq_right hlast]
    simp only [one_mul]
    rw [staircaseLowerEdge_add_staircaseTubeWidth_eq_startUpperBoundary
      base drift width start length hnext (q - 1)]
  constructor
  · constructor
    · nlinarith [mul_nonneg hmaxNonneg hwidth.le]
    · linarith
  · constructor
    · nlinarith [mul_le_mul_of_nonneg_right hmax hwidth.le]
    · linarith

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
