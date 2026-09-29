module

public import Combinatorics.BranchingWalk.Walk.Path.Interpolation
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Topology.UnitInterval

/-!
# Uniform-grid interpolation bounds

Deterministic estimates comparing polygonal random-walk paths at fixed
uniform-grid times with partial sums at equal integer block endpoints.
-/

open Set

@[expose] public section

namespace Combinatorics.Branching.Walk

/-- The discrete index selected by polygonal interpolation at the uniform
time `j / blocks`. -/
theorem natFloor_mul_uniformGrid (n j blocks : ℕ) :
    ⌊(n : ℝ) * ((j : ℝ) / blocks)⌋₊ = n * j / blocks := by
  rw [show (n : ℝ) * ((j : ℝ) / blocks) = ((n * j : ℕ) : ℝ) / blocks by
    push_cast
    ring]
  exact Nat.floor_div_eq_div _ _

/-- The left endpoint obtained by dividing `n` into equal integer blocks is
no later than the interpolation index at the matching uniform-grid time. -/
theorem mul_div_le_natFloor_mul_uniformGrid
    {n j blocks : ℕ} :
    j * (n / blocks) ≤ ⌊(n : ℝ) * ((j : ℝ) / blocks)⌋₊ := by
  rw [natFloor_mul_uniformGrid, Nat.mul_comm n j]
  exact Nat.mul_div_le_mul_div_assoc j n blocks

/-- The two integer indices used by uniform-grid interpolation differ by
fewer than `blocks` steps. -/
theorem natFloor_mul_uniformGrid_lt_mul_div_add
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

/-- A partial-sum difference over indices bounded by `n` is controlled by
the number of intervening increments times their maximal absolute value. -/
theorem abs_partialSum_sub_le_sub_mul_maxAbsUpTo
    {left right n : ℕ} (hleft : left ≤ right) (hright : right ≤ n)
    (increment : ℕ → ℝ) :
    |partialSum right increment - partialSum left increment| ≤
      ((right - left : ℕ) : ℝ) * maxAbsUpTo n increment := by
  have hrightEq : right = left + (right - left) := by omega
  conv_lhs =>
    rw [hrightEq, partialSum_add_eq_add_blockSum, add_sub_cancel_left]
  unfold blockSum
  calc
    |∑ k ∈ Finset.Ico left (left + (right - left)), increment k| ≤
        ∑ k ∈ Finset.Ico left (left + (right - left)), |increment k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Ico left (left + (right - left)),
          maxAbsUpTo n increment := by
      apply Finset.sum_le_sum
      intro k hk
      apply abs_increment_le_maxAbsUpTo increment
      have hklt : k < right := by
        rw [hrightEq]
        exact (Finset.mem_Ico.mp hk).2
      exact hklt.le.trans hright
    _ = ((right - left : ℕ) : ℝ) * maxAbsUpTo n increment := by
      simp only [Finset.sum_const, Nat.card_Ico,
        Nat.add_sub_cancel_left, nsmul_eq_mul]

/-- At a fixed uniform-grid time, polygonal interpolation is within
`blocks + 1` maximal jumps of the corresponding equal-block endpoint. -/
theorem abs_normalizedLinearPath_uniformGrid_sub_endpoint_le
    {n j blocks : ℕ} (hblocks : 0 < blocks) (hj : j ≤ blocks)
    (increment : ℕ → ℝ) :
    |normalizedLinearPath (fun n => Real.sqrt n) n increment
          ((j : ℝ) / blocks) -
        partialSum (j * (n / blocks)) increment / Real.sqrt n| ≤
      (blocks + 1) * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by
  let t : unitInterval :=
    ⟨(j : ℝ) / blocks, by
      constructor
      · positivity
      · rw [div_le_one (by exact_mod_cast hblocks)]
        exact_mod_cast hj⟩
  let middle := ⌊(n : ℝ) * ((j : ℝ) / blocks)⌋₊
  let left := j * (n / blocks)
  have hleft : left ≤ middle :=
    mul_div_le_natFloor_mul_uniformGrid
  have hmiddle : middle ≤ n := by
    dsimp only [middle]
    apply Nat.floor_le_of_le
    have hjR : (j : ℝ) ≤ blocks := by exact_mod_cast hj
    have hbR : (0 : ℝ) < blocks := by exact_mod_cast hblocks
    calc
      (n : ℝ) * ((j : ℝ) / blocks) ≤ (n : ℝ) * 1 := by
        gcongr
        exact (div_le_one hbR).2 hjR
      _ = n := by ring
  have hgap : middle - left ≤ blocks := by
    have := natFloor_mul_uniformGrid_lt_mul_div_add (n := n) hblocks hj
    dsimp only [middle, left]
    omega
  have hlinear := abs_normalizedLinearPath_sub_normalizedStepPath_le
    (n := n) (fun n => Real.sqrt n) increment t
  have hsum := abs_partialSum_sub_le_sub_mul_maxAbsUpTo
    hleft hmiddle increment
  have hsqrt : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hmax : 0 ≤ maxAbsUpTo n increment := maxAbsUpTo_nonneg n increment
  change |normalizedLinearPath (fun n => Real.sqrt n) n increment
      ((j : ℝ) / blocks) - partialSum left increment / Real.sqrt n| ≤ _
  have hstep :
      |normalizedStepPath (fun n => Real.sqrt n) n increment t -
          partialSum left increment / Real.sqrt n| ≤
        blocks * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by
    change |(Real.sqrt n)⁻¹ * partialSum middle increment -
        partialSum left increment / Real.sqrt n| ≤ _
    rw [div_eq_mul_inv, mul_comm (partialSum left increment), ← mul_sub,
      abs_mul, abs_of_nonneg hsqrt]
    calc
      (Real.sqrt n)⁻¹ * |partialSum middle increment -
          partialSum left increment| ≤
          (Real.sqrt n)⁻¹ * (((middle - left : ℕ) : ℝ) *
            maxAbsUpTo n increment) :=
        mul_le_mul_of_nonneg_left hsum hsqrt
      _ ≤ (Real.sqrt n)⁻¹ * (blocks * maxAbsUpTo n increment) := by
        gcongr
      _ = blocks * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by ring
  calc
    |normalizedLinearPath (fun n => Real.sqrt n) n increment
          ((j : ℝ) / blocks) -
        partialSum left increment / Real.sqrt n| ≤
        |normalizedLinearPath (fun n => Real.sqrt n) n increment
            ((j : ℝ) / blocks) -
          normalizedStepPath (fun n => Real.sqrt n) n increment t| +
        |normalizedStepPath (fun n => Real.sqrt n) n increment t -
          partialSum left increment / Real.sqrt n| := abs_sub_le _ _ _
    _ ≤ (Real.sqrt n)⁻¹ * maxAbsUpTo n increment +
        blocks * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by
      gcongr
      · simpa [t, abs_of_nonneg hsqrt] using
          hlinear.trans (mul_le_mul_of_nonneg_left
            (abs_increment_le_maxAbsUpTo increment (by
              simpa [middle, t] using hmiddle)) (abs_nonneg _))
    _ = (blocks + 1) * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by ring

end Combinatorics.Branching.Walk
