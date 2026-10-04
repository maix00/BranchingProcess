/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Partition.Basic

/-!
# Normalized endpoints of block partitions

Deterministic estimates that transfer normalized endpoint control to
unnormalized block-start margins and corridor events.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Coordinatewise approximation of consecutive normalized block sums gives
a linear error bound at every earlier partition endpoint. -/
theorem abs_normalized_partialSum_mul_sub_sum_le
    {blocks length : ℕ} {scale radius : ℝ}
    {increment : ℕ → ℝ} {target : ℕ → ℝ}
    (hblock : ∀ j < blocks,
      |AdditivePath.blockSum (j * length) length increment / scale - target j| ≤ radius)
    {k : ℕ} (hk : k ≤ blocks) :
    |AdditivePath.displacement (k * length) increment / scale -
        ∑ j ∈ Finset.range k, target j| ≤ (k : ℝ) * radius := by
  rw [displacement_mul_eq_sum_blockSum, div_eq_mul_inv, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  simp only [← div_eq_mul_inv]
  calc
    |∑ j ∈ Finset.range k,
        (AdditivePath.blockSum (j * length) length increment / scale - target j)| ≤
        ∑ j ∈ Finset.range k,
          |AdditivePath.blockSum (j * length) length increment / scale - target j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, radius := by
      apply Finset.sum_le_sum
      intro j hj
      exact hblock j (lt_of_lt_of_le (Finset.mem_range.1 hj) hk)
    _ = (k : ℝ) * radius := by simp

/-- If the reference partition endpoints lie inside intervals with a uniform
margin, coordinatewise block approximation keeps every endpoint in the
closed intervals. -/
theorem normalized_partitionEndpoints_mem_Icc_of_blockApproximation
    {blocks length : ℕ} {scale radius : ℝ}
    {increment : ℕ → ℝ} {target lower upper : ℕ → ℝ}
    (hradius : 0 ≤ radius)
    (hblock : ∀ j < blocks,
      |AdditivePath.blockSum (j * length) length increment / scale - target j| ≤ radius)
    (hmargin : ∀ k ≤ blocks,
      lower k + (blocks : ℝ) * radius ≤
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j ≤
          upper k - (blocks : ℝ) * radius) :
    ∀ k ≤ blocks,
      AdditivePath.displacement (k * length) increment / scale ∈
        Set.Icc (lower k) (upper k) := by
  intro k hk
  have herror := abs_normalized_partialSum_mul_sub_sum_le
    hblock hk
  have hkRadius : (k : ℝ) * radius ≤ (blocks : ℝ) * radius :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hradius
  have habs := abs_le.1 herror
  have hm := hmargin k hk
  constructor <;> linarith

/-- Strict reference margins and weak block-error bounds keep every
partition endpoint in the corresponding open interval. -/
theorem normalized_partitionEndpoints_mem_Ioo_of_blockApproximation
    {blocks length : ℕ} {scale radius : ℝ}
    {increment : ℕ → ℝ} {target lower upper : ℕ → ℝ}
    (hradius : 0 ≤ radius)
    (hblock : ∀ j < blocks,
      |AdditivePath.blockSum (j * length) length increment / scale - target j| ≤ radius)
    (hmargin : ∀ k ≤ blocks,
      lower k + (blocks : ℝ) * radius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          upper k - (blocks : ℝ) * radius) :
    ∀ k ≤ blocks,
      AdditivePath.displacement (k * length) increment / scale ∈
        Set.Ioo (lower k) (upper k) := by
  intro k hk
  have herror := abs_normalized_partialSum_mul_sub_sum_le
    hblock hk
  have hkRadius : (k : ℝ) * radius ≤ (blocks : ℝ) * radius :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hradius
  have habs := abs_le.1 herror
  have hm := hmargin k hk
  constructor <;> linarith

/-- Strict normalized endpoint containment in uniformly shrunken intervals
gives the corresponding weak, unnormalized start margins. -/
theorem partitionStartMargins_of_normalizedEndpoints
    {blocks length : ℕ} {scale radius : ℝ}
    {increment : ℕ → ℝ} {lower upper : ℕ → ℝ}
    (hscale : 0 < scale)
    (hendpoints : ∀ j < blocks,
      AdditivePath.displacement (j * length) increment / scale ∈
        Set.Ioo (lower j + radius) (upper j - radius)) :
    ∀ j < blocks,
      scale * lower j + scale * radius ≤
          AdditivePath.displacement (j * length) increment ∧
        AdditivePath.displacement (j * length) increment ≤
          scale * upper j - scale * radius := by
  intro j hj
  have h := hendpoints j hj
  constructor
  · have := ((lt_div_iff₀ hscale).mp h.1).le
    nlinarith
  · have := ((div_lt_iff₀ hscale).mp h.2).le
    nlinarith

/-- Simultaneous margins at all block starts control every block corridor,
unless at least one block has a large relative displacement. -/
theorem partitionStartMargins_subset_corridors_union_largeDeviation
    {blocks length : ℕ} {radius : ℝ} (hradius : 0 ≤ radius)
    (lower upper : ℕ → ℝ) :
    {increment : ℕ → ℝ | ∀ j < blocks,
        lower j + radius ≤ AdditivePath.displacement (j * length) increment ∧
          AdditivePath.displacement (j * length) increment ≤ upper j - radius} ⊆
      {increment | ∀ j < blocks, ∀ k ≤ length,
          AdditivePath.displacement (j * length + k) increment ∈
            Set.Icc (lower j) (upper j)} ∪
      {increment | ∃ j < blocks,
          ∃ k ∈ Finset.range (length + 1),
            radius ≤ |AdditivePath.blockSum (j * length) (k + 1) increment|} := by
  intro increment hmargin
  by_cases hlarge : ∃ j < blocks,
      ∃ k ∈ Finset.range (length + 1),
        radius ≤ |AdditivePath.blockSum (j * length) (k + 1) increment|
  · exact Or.inr hlarge
  · left
    intro j hj
    apply displacement_mem_Icc_of_start_mem_shrunken (hmargin j hj)
    intro k hk
    cases k with
    | zero => simpa using hradius
    | succ k =>
        have hkRange : k ∈ Finset.range (length + 1) := by
          simp
          omega
        have hnot : ¬radius ≤
            |AdditivePath.blockSum (j * length) (k + 1) increment| :=
          fun h => hlarge ⟨j, hj, k, hkRange, h⟩
        exact le_of_lt (lt_of_not_ge hnot)

end ProbabilityTheory.RandomWalk

