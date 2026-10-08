/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Basic
public import Algebra.BigOperators.PartialSum

/-!
# Corridor control inside an increment block

Deterministic lemmas transferring an endpoint margin and a bound on relative
block displacements to control of every position inside the block.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Every partial sum of a finite increment block, including the initial
zero, lies strictly inside a fixed open interval. -/
def InOpenPartialSumCorridor {length : ℕ} (lower upper : ℝ)
    (block : Fin length → ℝ) : Prop :=
  ∀ k : Fin (length + 1),
    lower < Fin.partialSum block k ∧ Fin.partialSum block k < upper

/-- If the interval contains the initial position, a strict partial-sum
corridor is equivalent to checking its positive-time positions. -/
theorem inOpenPartialSumCorridor_iff_succ
    {length : ℕ} {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper)
    (block : Fin length → ℝ) :
    InOpenPartialSumCorridor lower upper block ↔
      ∀ k : Fin length,
        lower < Fin.partialSum block k.succ ∧
          Fin.partialSum block k.succ < upper := by
  constructor
  · intro h k
    exact h k.succ
  · intro h k
    refine Fin.induction ?_ ?_ k
    · simp [hlower, hupper]
    · intro k ih
      exact h k

/-- A finite increment block stays in an open corridor and ends in a given
open interval. -/
def InOpenPartialSumCorridorEndsIn {length : ℕ}
    (lower upper endLower endUpper : ℝ) (block : Fin length → ℝ) : Prop :=
  InOpenPartialSumCorridor lower upper block ∧
    Fin.partialSum block (Fin.last length) ∈ Set.Ioo endLower endUpper

/-- Uniform displacement bounds from one block start control the distance
between any two positions inside that block. -/
theorem abs_partialSum_add_sub_partialSum_add_le_two_mul
    {radius : ℝ} {start length left right : ℕ} {increment : ℕ → ℝ}
    (hleft : left ≤ length) (hright : right ≤ length)
    (hdeviation : ∀ k ≤ length,
      |AdditivePath.blockSum start k increment| ≤ radius) :
    |AdditivePath.displacement (start + right) increment -
        AdditivePath.displacement (start + left) increment| ≤ 2 * radius := by
  rw [AdditivePath.displacement_add_eq_add_blockSum, AdditivePath.displacement_add_eq_add_blockSum]
  calc
    |_ - _| =
        |AdditivePath.blockSum start right increment - AdditivePath.blockSum start left increment| := by
      congr 1
      ring
    _ ≤ |AdditivePath.blockSum start right increment| +
        |AdditivePath.blockSum start left increment| := abs_sub _ _
    _ ≤ radius + radius :=
      add_le_add (hdeviation right hright) (hdeviation left hleft)
    _ = 2 * radius := by ring

/-- Uniform displacement bounds in two consecutive blocks control the
distance between a position in the first block and one in the second. -/
theorem abs_partialSum_nextBlock_add_sub_partialSum_add_le_three_mul
    {radius : ℝ} {start length left right : ℕ} {increment : ℕ → ℝ}
    (hleft : left ≤ length) (hright : right ≤ length)
    (hfirst : ∀ k ≤ length,
      |AdditivePath.blockSum start k increment| ≤ radius)
    (hnext : ∀ k ≤ length,
      |AdditivePath.blockSum (start + length) k increment| ≤ radius) :
    |AdditivePath.displacement (start + length + right) increment -
        AdditivePath.displacement (start + left) increment| ≤ 3 * radius := by
  rw [AdditivePath.displacement_add_eq_add_blockSum, AdditivePath.displacement_add_eq_add_blockSum,
    AdditivePath.displacement_add_eq_add_blockSum]
  calc
    |_ - _| = |AdditivePath.blockSum start length increment +
          AdditivePath.blockSum (start + length) right increment -
          AdditivePath.blockSum start left increment| := by
      congr 1
      ring
    _ ≤ |AdditivePath.blockSum start length increment +
          AdditivePath.blockSum (start + length) right increment| +
          |AdditivePath.blockSum start left increment| := abs_sub _ _
    _ ≤ (|AdditivePath.blockSum start length increment| +
          |AdditivePath.blockSum (start + length) right increment|) +
          |AdditivePath.blockSum start left increment| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |AdditivePath.blockSum start length increment| +
          |AdditivePath.blockSum (start + length) right increment| +
          |AdditivePath.blockSum start left increment| := rfl
    _ ≤
        |AdditivePath.blockSum start length increment| +
          |AdditivePath.blockSum (start + length) right increment| +
          |AdditivePath.blockSum start left increment| := le_rfl
    _ ≤ radius + radius + radius :=
      add_le_add
        (add_le_add (hfirst length le_rfl) (hnext right hright))
        (hfirst left hleft)
    _ = 3 * radius := by ring

/-- If the position at a block start lies in an interval shrunk by `radius`
and every relative block displacement has absolute value at most `radius`,
then every position in that block lies in the original interval. -/
theorem displacement_mem_Icc_of_start_mem_shrunken
    {lower upper radius : ℝ}
    {start length : ℕ} {increment : ℕ → ℝ}
    (hstart : lower + radius ≤ AdditivePath.displacement start increment ∧
      AdditivePath.displacement start increment ≤ upper - radius)
    (hdeviation : ∀ k ≤ length,
      |AdditivePath.blockSum start k increment| ≤ radius) :
    ∀ k ≤ length,
      AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper := by
  intro k hk
  rw [AdditivePath.displacement_add_eq_add_blockSum]
  have hbound := abs_le.mp (hdeviation k hk)
  constructor <;> linarith

/-- The same block argument with strict endpoint margins and strict
oscillation control gives membership in the open interval. -/
theorem displacement_mem_Ioo_of_start_mem_shrunken
    {lower upper radius : ℝ}
    {start length : ℕ} {increment : ℕ → ℝ}
    (hstart : lower + radius < AdditivePath.displacement start increment ∧
      AdditivePath.displacement start increment < upper - radius)
    (hdeviation : ∀ k ≤ length,
      |AdditivePath.blockSum start k increment| ≤ radius) :
    ∀ k ≤ length,
      AdditivePath.displacement (start + k) increment ∈ Set.Ioo lower upper := by
  intro k hk
  rw [AdditivePath.displacement_add_eq_add_blockSum]
  have hbound := abs_le.mp (hdeviation k hk)
  constructor <;> linarith

/-- A path whose block-start position has the required margin either stays in
the target interval throughout the block or has a large relative displacement
inside the slightly enlarged finite maximum. -/
theorem startMargin_subset_blockCorridor_union_largeDeviation
    {lower upper radius : ℝ} (hradius : 0 ≤ radius)
    (start length : ℕ) :
    {increment : ℕ → ℝ |
        lower + radius ≤ AdditivePath.displacement start increment ∧
          AdditivePath.displacement start increment ≤ upper - radius} ⊆
      {increment | ∀ k ≤ length,
          AdditivePath.displacement (start + k) increment ∈ Set.Icc lower upper} ∪
      {increment | ∃ k ∈ Finset.range (length + 1),
          radius ≤ |AdditivePath.blockSum start (k + 1) increment|} := by
  intro increment hmargin
  by_cases hlarge : ∃ k ∈ Finset.range (length + 1),
      radius ≤ |AdditivePath.blockSum start (k + 1) increment|
  · exact Or.inr hlarge
  · left
    apply displacement_mem_Icc_of_start_mem_shrunken hmargin
    intro k hk
    cases k with
    | zero => simpa using hradius
    | succ j =>
        have hj : j ∈ Finset.range (length + 1) := by
          simp
          omega
        have hnot : ¬radius ≤ |AdditivePath.blockSum start (j + 1) increment| :=
          fun h => hlarge ⟨j, hj, h⟩
        exact le_of_lt (lt_of_not_ge hnot)

end ProbabilityTheory.RandomWalk
