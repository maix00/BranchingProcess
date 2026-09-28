import Combinatorics.BranchingWalk.Walk.Path.Block.Basic

/-!
# Corridor control inside an increment block

Deterministic lemmas transferring an endpoint margin and a bound on relative
block displacements to control of every position inside the block.
-/

namespace Combinatorics.Branching.Walk

/-- Uniform displacement bounds from one block start control the distance
between any two positions inside that block. -/
theorem abs_partialSum_add_sub_partialSum_add_le_two_mul
    {radius : ℝ} {start length left right : ℕ} {increment : ℕ → ℝ}
    (hleft : left ≤ length) (hright : right ≤ length)
    (hdeviation : ∀ k ≤ length,
      |blockSum start k increment| ≤ radius) :
    |partialSum (start + right) increment -
        partialSum (start + left) increment| ≤ 2 * radius := by
  rw [partialSum_add_eq_add_blockSum, partialSum_add_eq_add_blockSum]
  calc
    |_ - _| =
        |blockSum start right increment - blockSum start left increment| := by
      congr 1
      ring
    _ ≤ |blockSum start right increment| +
        |blockSum start left increment| := abs_sub _ _
    _ ≤ radius + radius :=
      add_le_add (hdeviation right hright) (hdeviation left hleft)
    _ = 2 * radius := by ring

/-- Uniform displacement bounds in two consecutive blocks control the
distance between a position in the first block and one in the second. -/
theorem abs_partialSum_nextBlock_add_sub_partialSum_add_le_three_mul
    {radius : ℝ} {start length left right : ℕ} {increment : ℕ → ℝ}
    (hleft : left ≤ length) (hright : right ≤ length)
    (hfirst : ∀ k ≤ length,
      |blockSum start k increment| ≤ radius)
    (hnext : ∀ k ≤ length,
      |blockSum (start + length) k increment| ≤ radius) :
    |partialSum (start + length + right) increment -
        partialSum (start + left) increment| ≤ 3 * radius := by
  rw [partialSum_add_eq_add_blockSum, partialSum_add_eq_add_blockSum,
    partialSum_add_eq_add_blockSum]
  calc
    |_ - _| = |blockSum start length increment +
          blockSum (start + length) right increment -
          blockSum start left increment| := by
      congr 1
      ring
    _ ≤ |blockSum start length increment +
          blockSum (start + length) right increment| +
          |blockSum start left increment| := abs_sub _ _
    _ ≤ (|blockSum start length increment| +
          |blockSum (start + length) right increment|) +
          |blockSum start left increment| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = |blockSum start length increment| +
          |blockSum (start + length) right increment| +
          |blockSum start left increment| := rfl
    _ ≤
        |blockSum start length increment| +
          |blockSum (start + length) right increment| +
          |blockSum start left increment| := le_rfl
    _ ≤ radius + radius + radius :=
      add_le_add
        (add_le_add (hfirst length le_rfl) (hnext right hright))
        (hfirst left hleft)
    _ = 3 * radius := by ring

/-- If the position at a block start lies in an interval shrunk by `radius`
and every relative block displacement has absolute value at most `radius`,
then every position in that block lies in the original interval. -/
theorem partialSum_mem_Icc_of_start_mem_shrunken
    {lower upper radius : ℝ}
    {start length : ℕ} {increment : ℕ → ℝ}
    (hstart : lower + radius ≤ partialSum start increment ∧
      partialSum start increment ≤ upper - radius)
    (hdeviation : ∀ k ≤ length,
      |blockSum start k increment| ≤ radius) :
    ∀ k ≤ length,
      partialSum (start + k) increment ∈ Set.Icc lower upper := by
  intro k hk
  rw [partialSum_add_eq_add_blockSum]
  have hbound := abs_le.mp (hdeviation k hk)
  constructor <;> linarith

/-- The same block argument with strict endpoint margins and strict
oscillation control gives membership in the open interval. -/
theorem partialSum_mem_Ioo_of_start_mem_shrunken
    {lower upper radius : ℝ}
    {start length : ℕ} {increment : ℕ → ℝ}
    (hstart : lower + radius < partialSum start increment ∧
      partialSum start increment < upper - radius)
    (hdeviation : ∀ k ≤ length,
      |blockSum start k increment| ≤ radius) :
    ∀ k ≤ length,
      partialSum (start + k) increment ∈ Set.Ioo lower upper := by
  intro k hk
  rw [partialSum_add_eq_add_blockSum]
  have hbound := abs_le.mp (hdeviation k hk)
  constructor <;> linarith

/-- A path whose block-start position has the required margin either stays in
the target interval throughout the block or has a large relative displacement
inside the slightly enlarged finite maximum. -/
theorem startMargin_subset_blockCorridor_union_largeDeviation
    {lower upper radius : ℝ} (hradius : 0 ≤ radius)
    (start length : ℕ) :
    {increment : ℕ → ℝ |
        lower + radius ≤ partialSum start increment ∧
          partialSum start increment ≤ upper - radius} ⊆
      {increment | ∀ k ≤ length,
          partialSum (start + k) increment ∈ Set.Icc lower upper} ∪
      {increment | ∃ k ∈ Finset.range (length + 1),
          radius ≤ |blockSum start (k + 1) increment|} := by
  intro increment hmargin
  by_cases hlarge : ∃ k ∈ Finset.range (length + 1),
      radius ≤ |blockSum start (k + 1) increment|
  · exact Or.inr hlarge
  · left
    apply partialSum_mem_Icc_of_start_mem_shrunken hmargin
    intro k hk
    cases k with
    | zero => simpa using hradius
    | succ j =>
        have hj : j ∈ Finset.range (length + 1) := by
          simp
          omega
        have hnot : ¬radius ≤ |blockSum start (j + 1) increment| :=
          fun h => hlarge ⟨j, hj, h⟩
        exact le_of_lt (lt_of_not_ge hnot)

end Combinatorics.Branching.Walk
