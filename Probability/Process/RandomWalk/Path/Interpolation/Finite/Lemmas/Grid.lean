/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Path.Interpolation.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.UnitInterval

/-!
# Internal uniform-grid estimates for polygonal random-walk paths

## Internal proof declarations

- `natFloor_mul_uniformGrid` evaluates $\lfloor n(j/m)\rfloor$ as $nj/m$ for natural indices.
- `mul_div_le_natFloor_mul_uniformGrid` and
  `natFloor_mul_uniformGrid_lt_mul_div_add` bound the floor index relative to the equal-block
  endpoint $j\lfloor n/m\rfloor$.
- `abs_partialSum_sub_le_sub_mul_maxAbsUpTo` bounds the difference between two partial sums by
  their index distance times $\max_{k\le n}|\xi_k|$.

These estimates are used only in
`Probability.Process.RandomWalk.Path.Interpolation.Finite.Grid` to prove its uniform-grid
endpoint error bound.
-/

open Set

namespace ProbabilityTheory.RandomWalk

/-- The discrete index selected by polygonal interpolation at the uniform
time `j / blocks`. -/
lemma natFloor_mul_uniformGrid (n j blocks : ℕ) :
    ⌊(n : ℝ) * ((j : ℝ) / blocks)⌋₊ = n * j / blocks := by
  rw [show (n : ℝ) * ((j : ℝ) / blocks) = ((n * j : ℕ) : ℝ) / blocks by
    push_cast
    ring]
  exact Nat.floor_div_eq_div _ _

/-- The left endpoint obtained by dividing `n` into equal integer blocks is
no later than the interpolation index at the matching uniform-grid time. -/
lemma mul_div_le_natFloor_mul_uniformGrid
    {n j blocks : ℕ} :
    j * (n / blocks) ≤ ⌊(n : ℝ) * ((j : ℝ) / blocks)⌋₊ := by
  rw [natFloor_mul_uniformGrid, Nat.mul_comm n j]
  exact Nat.mul_div_le_mul_div_assoc j n blocks

/-- The two integer indices used by uniform-grid interpolation differ by
fewer than `blocks` steps. -/
lemma natFloor_mul_uniformGrid_lt_mul_div_add
    {n j blocks : ℕ} (hblocks : 0 < blocks) (hj : j ≤ blocks) :
    ⌊(n : ℝ) * ((j : ℝ) / blocks)⌋₊ <
      j * (n / blocks) + blocks := by
  rw [natFloor_mul_uniformGrid]
  have hdecomp :
      n * j / blocks = (n / blocks) * j + (n % blocks) * j / blocks := by
    conv_lhs =>
      rw [← Nat.div_add_mod n blocks]
    rw [add_mul]
    conv_lhs =>
      congr
      · rw [show blocks * (n / blocks) * j =
          blocks * ((n / blocks) * j) by simp [Nat.mul_assoc]]
    exact Nat.mul_add_div hblocks ((n / blocks) * j) ((n % blocks) * j)
  rw [hdecomp, Nat.mul_comm (n / blocks) j]
  exact Nat.add_lt_add_left
    ((Nat.div_lt_iff_lt_mul hblocks).2
      (Nat.mul_lt_mul_of_lt_of_le (Nat.mod_lt n hblocks) hj hblocks)) _

end ProbabilityTheory.RandomWalk
