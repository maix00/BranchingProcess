/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.Blocks.EventBridge
/-!
# Horizontal staircase blocks inside a tilted tube

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.tubeBlockEvent_mem_driftedTube_at_time_of_extremeBounds`:
  a horizontal block bounded by the extreme boundary values at its
  two ends lies inside the tilted tube for either sign of the drift.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.tubeBlockEvent_mem_driftedTube_at_time`:
  a successful horizontal block on
  $[r_{t+n},s_t]$ lies inside the tilted tube
  $[r_j,s_j]$ at every $t\le j\le t+n$ when $r_j$ is increasing.

This is the deterministic inclusion of each horizontal staircase step in
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open ProbabilityTheory.RandomWalk.SmallDeviation

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

/-- A horizontal block between the maximal lower boundary and minimal
upper boundary of a linear tube lies inside the tube throughout the block.
The same statement applies to rising and falling tubes. -/
theorem tubeBlockEvent_mem_driftedTube_at_time_of_extremeBounds
    {start length j : ℕ} {width drift lower v₁ v₂ : ℝ}
    (hstart : start ≤ j) (hend : j ≤ start + length)
    {increment : ℕ → ℝ}
    (hblock : increment ∈ tubeBlockEvent start length
      (lower + max (drift * (start : ℝ) / width ^ 2)
        (drift * ((start + length : ℕ) : ℝ) / width ^ 2))
      ((lower + min (drift * (start : ℝ) / width ^ 2)
        (drift * ((start + length : ℕ) : ℝ) / width ^ 2) + width) -
        (lower + max (drift * (start : ℝ) / width ^ 2)
          (drift * ((start + length : ℕ) : ℝ) / width ^ 2)))
      v₁ v₂) :
    lower + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        lower + drift * (j : ℝ) / width ^ 2 + width := by
  have hblockTime : j - start ≤ length := by omega
  have hstartAdd : start + (j - start) = j := Nat.add_sub_of_le hstart
  have hposition := tubeBlockEvent_path_mem hblock hblockTime
  rw [hstartAdd] at hposition
  have hdenom : 0 ≤ width ^ 2 := sq_nonneg width
  have hstartReal : (start : ℝ) ≤ (j : ℝ) := by exact_mod_cast hstart
  have hendReal : (j : ℝ) ≤ ((start + length : ℕ) : ℝ) := by
    exact_mod_cast hend
  have hbetween :
      drift * (j : ℝ) / width ^ 2 ≤
          max (drift * (start : ℝ) / width ^ 2)
            (drift * ((start + length : ℕ) : ℝ) / width ^ 2) ∧
        min (drift * (start : ℝ) / width ^ 2)
            (drift * ((start + length : ℕ) : ℝ) / width ^ 2) ≤
          drift * (j : ℝ) / width ^ 2 := by
    by_cases hdrift : 0 ≤ drift
    · have hright : drift * (j : ℝ) / width ^ 2 ≤
          drift * ((start + length : ℕ) : ℝ) / width ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hendReal hdrift) hdenom
      have hleft : drift * (start : ℝ) / width ^ 2 ≤
          drift * (j : ℝ) / width ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hstartReal hdrift) hdenom
      exact ⟨hright.trans (le_max_right _ _),
        (min_le_left _ _).trans hleft⟩
    · have hdrift' : drift ≤ 0 := le_of_lt (lt_of_not_ge hdrift)
      have hright : drift * (j : ℝ) / width ^ 2 ≤
          drift * (start : ℝ) / width ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonpos_left hstartReal hdrift') hdenom
      have hleft : drift * ((start + length : ℕ) : ℝ) / width ^ 2 ≤
          drift * (j : ℝ) / width ^ 2 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonpos_left hendReal hdrift') hdenom
      exact ⟨hright.trans (le_max_left _ _),
        (min_le_right _ _).trans hleft⟩
  exact ⟨by linarith [hposition.1, hbetween.1],
    by linarith [hposition.2, hbetween.2]⟩

/-- The horizontal tube with lower edge at the block end and upper edge
at the block start is contained in the linearly rising tube on that block. -/
theorem tubeBlockEvent_mem_driftedTube_at_time
    {start length j : ℕ} {width drift lower v₁ v₂ : ℝ}
    (hdrift : 0 ≤ drift)
    (hstart : start ≤ j) (hend : j ≤ start + length)
    {increment : ℕ → ℝ}
    (hblock : increment ∈ tubeBlockEvent start length
      (lower + drift * ((start + length : ℕ) : ℝ) / width ^ 2)
      ((lower + drift * (start : ℝ) / width ^ 2 + width) -
        (lower + drift * ((start + length : ℕ) : ℝ) / width ^ 2))
      v₁ v₂) :
    lower + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        lower + drift * (j : ℝ) / width ^ 2 + width := by
  have htime : (start : ℝ) ≤ ((start + length : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_add_right start length)
  have hmono : drift * (start : ℝ) / width ^ 2 ≤
      drift * ((start + length : ℕ) : ℝ) / width ^ 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htime hdrift) (sq_nonneg width)
  have hblock' : increment ∈ tubeBlockEvent start length
      (lower + max (drift * (start : ℝ) / width ^ 2)
        (drift * ((start + length : ℕ) : ℝ) / width ^ 2))
      ((lower + min (drift * (start : ℝ) / width ^ 2)
        (drift * ((start + length : ℕ) : ℝ) / width ^ 2) + width) -
        (lower + max (drift * (start : ℝ) / width ^ 2)
          (drift * ((start + length : ℕ) : ℝ) / width ^ 2)))
      v₁ v₂ := by
    simpa only [max_eq_right hmono, min_eq_left hmono] using hblock
  exact tubeBlockEvent_mem_driftedTube_at_time_of_extremeBounds
    hstart hend hblock'

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
