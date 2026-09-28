import Combinatorics.BranchingWalk.Walk.Path.Block.Basic

/-!
# Corridor control inside an increment block

Deterministic lemmas transferring an endpoint margin and a bound on relative
block displacements to control of every position inside the block.
-/

namespace Combinatorics.Branching.Walk

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
