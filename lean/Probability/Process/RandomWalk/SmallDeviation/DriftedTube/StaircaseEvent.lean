/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.BlockEventBridge

/-!
# Horizontal staircase blocks inside a tilted tube

The public theorem in this file is:

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
  have hblockTime : j - start ≤ length := by omega
  have hstartAdd : start + (j - start) = j := Nat.add_sub_of_le hstart
  have hposition := tubeBlockEvent_path_mem hblock hblockTime
  rw [hstartAdd] at hposition
  have hdenom : 0 ≤ width ^ 2 := sq_nonneg width
  have hstartReal : (start : ℝ) ≤ (j : ℝ) := by exact_mod_cast hstart
  have hendReal : (j : ℝ) ≤ ((start + length : ℕ) : ℝ) := by
    exact_mod_cast hend
  have hleft : drift * (j : ℝ) / width ^ 2 ≤
      drift * ((start + length : ℕ) : ℝ) / width ^ 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hendReal hdrift) hdenom
  have hright : drift * (start : ℝ) / width ^ 2 ≤
      drift * (j : ℝ) / width ^ 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstartReal hdrift) hdenom
  exact ⟨by linarith [hposition.1, hleft],
    by linarith [hposition.2, hright]⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
