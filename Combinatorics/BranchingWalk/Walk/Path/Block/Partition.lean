import Combinatorics.BranchingWalk.Walk.Path.Block.Corridor
import Combinatorics.BranchingWalk.Walk.Path.Window

/-!
# Finite partitions of walk paths

Deterministic identities and error bounds for reconstructing partition
endpoints from consecutive block sums.
-/

open scoped BigOperators

namespace Combinatorics.Branching.Walk

variable {E : Type*} [AddCommMonoid E]

/-- The partial sum at the end of `blocks` equal-length blocks is the sum of
their consecutive block sums. -/
theorem partialSum_mul_eq_sum_blockSum (blocks length : ℕ)
    (increment : ℕ → E) :
    partialSum (blocks * length) increment =
      ∑ j ∈ Finset.range blocks, blockSum (j * length) length increment := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
      rw [Nat.succ_mul, partialSum_add_eq_add_blockSum, ih,
        Finset.sum_range_succ]

/-- A closed-interval path of total length `blocks * length` is equivalently
checked on every coordinate of each equal block.  Adjacent blocks overlap at
their common endpoint. -/
theorem inClosedInterval_mul_iff_forall_block
    {blocks length : ℕ} (hblocks : 0 < blocks) (hlength : 0 < length)
    (lower upper initial : ℝ) (increment : ℕ → ℝ) :
    InClosedInterval lower upper (blocks * length) initial increment ↔
      ∀ j < blocks, ∀ k ≤ length,
        initial + partialSum (j * length + k) increment ∈
          Set.Icc lower upper := by
  constructor
  · intro h j hj k hk
    have hindex : j * length + k < blocks * length + 1 :=
      Nat.lt_succ_of_le <| calc
        j * length + k ≤ j * length + length := Nat.add_le_add_left hk _
        _ = (j + 1) * length := by rw [Nat.add_mul]; simp
        _ ≤ blocks * length :=
          Nat.mul_le_mul_right length (Nat.succ_le_iff.2 hj)
    simpa [InClosedInterval, InWindows, history] using
      h ⟨j * length + k, hindex⟩
  · intro h q
    change initial + partialSum (q : ℕ) increment ∈ Set.Icc lower upper
    by_cases hlast : (q : ℕ) = blocks * length
    · have hj : blocks - 1 < blocks := Nat.sub_lt (by omega) (by omega)
      have heq : (blocks - 1) * length + length = blocks * length := by
        calc
          (blocks - 1) * length + length = ((blocks - 1) + 1) * length := by
            rw [Nat.add_mul, one_mul]
          _ = blocks * length := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ blocks)]
      simpa [hlast, heq] using h (blocks - 1) hj length le_rfl
    · have hq : (q : ℕ) < blocks * length := by
        exact lt_of_le_of_ne (Nat.le_of_lt_succ q.isLt) hlast
      have hj : (q : ℕ) / length < blocks :=
        (Nat.div_lt_iff_lt_mul hlength).2 (by simpa [mul_comm] using hq)
      have hk : (q : ℕ) % length ≤ length :=
        (Nat.mod_lt (q : ℕ) hlength).le
      have heq : (q : ℕ) / length * length + (q : ℕ) % length = q := by
        simpa [mul_comm] using Nat.div_add_mod (q : ℕ) length
      simpa [heq] using h ((q : ℕ) / length) hj ((q : ℕ) % length) hk

end Combinatorics.Branching.Walk

namespace Combinatorics.Branching.Walk

/-- Coordinatewise approximation of consecutive normalized block sums gives
a linear error bound at every earlier partition endpoint. -/
theorem abs_normalized_partialSum_mul_sub_sum_le
    {blocks length : ℕ} {scale radius : ℝ}
    {increment : ℕ → ℝ} {target : ℕ → ℝ}
    (hblock : ∀ j < blocks,
      |blockSum (j * length) length increment / scale - target j| ≤ radius)
    {k : ℕ} (hk : k ≤ blocks) :
    |partialSum (k * length) increment / scale -
        ∑ j ∈ Finset.range k, target j| ≤ (k : ℝ) * radius := by
  rw [partialSum_mul_eq_sum_blockSum, div_eq_mul_inv, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  simp only [← div_eq_mul_inv]
  calc
    |∑ j ∈ Finset.range k,
        (blockSum (j * length) length increment / scale - target j)| ≤
        ∑ j ∈ Finset.range k,
          |blockSum (j * length) length increment / scale - target j| :=
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
      |blockSum (j * length) length increment / scale - target j| ≤ radius)
    (hmargin : ∀ k ≤ blocks,
      lower k + (blocks : ℝ) * radius ≤
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j ≤
          upper k - (blocks : ℝ) * radius) :
    ∀ k ≤ blocks,
      partialSum (k * length) increment / scale ∈
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
      |blockSum (j * length) length increment / scale - target j| ≤ radius)
    (hmargin : ∀ k ≤ blocks,
      lower k + (blocks : ℝ) * radius <
          ∑ j ∈ Finset.range k, target j ∧
        ∑ j ∈ Finset.range k, target j <
          upper k - (blocks : ℝ) * radius) :
    ∀ k ≤ blocks,
      partialSum (k * length) increment / scale ∈
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
      partialSum (j * length) increment / scale ∈
        Set.Ioo (lower j + radius) (upper j - radius)) :
    ∀ j < blocks,
      scale * lower j + scale * radius ≤
          partialSum (j * length) increment ∧
        partialSum (j * length) increment ≤
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
        lower j + radius ≤ partialSum (j * length) increment ∧
          partialSum (j * length) increment ≤ upper j - radius} ⊆
      {increment | ∀ j < blocks, ∀ k ≤ length,
          partialSum (j * length + k) increment ∈
            Set.Icc (lower j) (upper j)} ∪
      {increment | ∃ j < blocks,
          ∃ k ∈ Finset.range (length + 1),
            radius ≤ |blockSum (j * length) (k + 1) increment|} := by
  intro increment hmargin
  by_cases hlarge : ∃ j < blocks,
      ∃ k ∈ Finset.range (length + 1),
        radius ≤ |blockSum (j * length) (k + 1) increment|
  · exact Or.inr hlarge
  · left
    intro j hj
    apply partialSum_mem_Icc_of_start_mem_shrunken (hmargin j hj)
    intro k hk
    cases k with
    | zero => simpa using hradius
    | succ k =>
        have hkRange : k ∈ Finset.range (length + 1) := by
          simp
          omega
        have hnot : ¬radius ≤
            |blockSum (j * length) (k + 1) increment| :=
          fun h => hlarge ⟨j, hj, k, hkRange, h⟩
        exact le_of_lt (lt_of_not_ge hnot)

end Combinatorics.Branching.Walk
