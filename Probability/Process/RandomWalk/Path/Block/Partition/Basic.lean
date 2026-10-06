/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Probability.Process.RandomWalk.Path.Block.Corridor.Basic
public import Probability.Process.RandomWalk.Path.Window.Basic

/-!
# Finite partitions of walk paths

Deterministic identities and error bounds for reconstructing partition
endpoints from consecutive block sums.
-/

open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory.RandomWalk

variable {E : Type*} [AddCommMonoid E]

/-- The partial sums of one increment block are the positions of the
corresponding segment of the original walk, translated to start at zero. -/
theorem partialSum_blockCoordinates {length : ℕ}
    (start : ℕ) (increment : ℕ → E)
    (j : Fin (length + 1)) :
    Fin.partialSum (Combinatorics.Sequence.blockCoordinates start length increment) j =
      AdditivePath.blockSum start j increment := by
  induction j using Fin.induction with
  | zero => simp [AdditivePath.blockSum]
  | succ j ih =>
    rw [Fin.partialSum_succ, ih]
    simp only [Fin.val_castSucc, Fin.val_succ, Combinatorics.Sequence.blockCoordinates]
    rw [AdditivePath.blockSum_add start (j : ℕ) 1]
    simp [AdditivePath.blockSum]

/-- Every index before a covered horizon has a unique quotient-remainder
location in one of the equal-length blocks. -/
theorem exists_eq_blockStart_add_of_lt_of_le_mul
    {horizon blocks length index : ℕ} (hlength : 0 < length)
    (hindex : index < horizon) (hcover : horizon ≤ blocks * length) :
    ∃ block < blocks, ∃ offset < length,
      index = block * length + offset := by
  refine ⟨index / length, ?_, index % length, Nat.mod_lt _ hlength, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hlength).2
      (lt_of_lt_of_le hindex hcover)
  · simpa [mul_comm] using (Nat.div_add_mod index length).symm

/-- Two ordered indices separated by at most one block length have block
quotients differing by at most one. -/
theorem div_le_div_add_one_of_sub_le
    {length left right : ℕ} (hlength : 0 < length)
    (hle : left ≤ right) (hdistance : right - left ≤ length) :
    right / length ≤ left / length + 1 := by
  have hright : right ≤ left + length := by omega
  calc
    right / length ≤ (left + length) / length :=
      Nat.div_le_div_right hright
    _ = left / length + 1 := Nat.add_div_right left hlength

/-- If every equal-length block has displacement at most `radius` from its
own start, then two covered partial sums whose indices differ by at most one
block length differ by at most three radii. -/
theorem abs_displacement_sub_le_three_mul_of_blockBounds
    {horizon blocks length left right : ℕ} {radius : ℝ}
    {increment : ℕ → ℝ} (hlength : 0 < length) (hradius : 0 ≤ radius)
    (hcover : horizon ≤ blocks * length)
    (hleft : left < horizon) (hright : right < horizon)
    (hle : left ≤ right) (hdistance : right - left ≤ length)
    (hblocks : ∀ block < blocks, ∀ offset ≤ length,
      |AdditivePath.blockSum (block * length) offset increment| ≤ radius) :
    |AdditivePath.displacement right increment - AdditivePath.displacement left increment| ≤ 3 * radius := by
  let leftBlock := left / length
  let rightBlock := right / length
  let leftOffset := left % length
  let rightOffset := right % length
  have hleftBlock : leftBlock < blocks := by
    exact (Nat.div_lt_iff_lt_mul hlength).2
      (lt_of_lt_of_le hleft hcover)
  have hrightBlock : rightBlock < blocks := by
    exact (Nat.div_lt_iff_lt_mul hlength).2
      (lt_of_lt_of_le hright hcover)
  have hleftOffset : leftOffset ≤ length :=
    (Nat.mod_lt left hlength).le
  have hrightOffset : rightOffset ≤ length :=
    (Nat.mod_lt right hlength).le
  have hleftEq : left = leftBlock * length + leftOffset := by
    simpa [leftBlock, leftOffset, mul_comm] using
      (Nat.div_add_mod left length).symm
  have hrightEq : right = rightBlock * length + rightOffset := by
    simpa [rightBlock, rightOffset, mul_comm] using
      (Nat.div_add_mod right length).symm
  have hblockLe : leftBlock ≤ rightBlock := by
    exact Nat.div_le_div_right hle
  have hblockSucc : rightBlock ≤ leftBlock + 1 := by
    exact div_le_div_add_one_of_sub_le hlength hle hdistance
  rcases hblockLe.eq_or_lt with hsame | hlt
  · have hrightBlockEq : rightBlock = leftBlock := hsame.symm
    rw [hleftEq, hrightEq, hrightBlockEq]
    calc
      |_ - _| ≤ 2 * radius :=
        abs_partialSum_add_sub_partialSum_add_le_two_mul
          hleftOffset hrightOffset (hblocks leftBlock hleftBlock)
      _ ≤ 3 * radius := by nlinarith
  · have hnext : rightBlock = leftBlock + 1 := by omega
    have hnextLt : leftBlock + 1 < blocks := by
      rw [← hnext]
      exact hrightBlock
    have hnextBounds : ∀ k ≤ length,
        |AdditivePath.blockSum (leftBlock * length + length) k increment| ≤ radius := by
      simpa [Nat.add_mul] using hblocks (leftBlock + 1) hnextLt
    simpa [hleftEq, hrightEq, hnext, Nat.add_mul, Nat.add_assoc] using
      (abs_partialSum_nextBlock_add_sub_partialSum_add_le_three_mul
        hleftOffset hrightOffset
          (hblocks leftBlock hleftBlock) hnextBounds)

/-- The partial sum at the end of `blocks` equal-length blocks is the sum of
their consecutive block sums. -/
theorem displacement_mul_eq_sum_blockSum (blocks length : ℕ)
    (increment : ℕ → E) :
    AdditivePath.displacement (blocks * length) increment =
      ∑ j ∈ Finset.range blocks, AdditivePath.blockSum (j * length) length increment := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
      rw [Nat.succ_mul, AdditivePath.displacement_add_eq_add_blockSum, ih,
        Finset.sum_range_succ]

/-- Equal consecutive block sums reconstruct the partial sum at every block
endpoint. -/
theorem partialSum_blockSum {blocks length : ℕ}
    (increment : ℕ → E) (j : Fin (blocks + 1)) :
    Fin.partialSum
        (fun k : Fin blocks => AdditivePath.blockSum (k * length) length increment) j =
      AdditivePath.displacement (j * length) increment := by
  induction j using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [Fin.partialSum_succ, ih]
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [show ((j : ℕ) + 1) * length = (j : ℕ) * length + length by
      simp [Nat.add_mul]]
    rw [← AdditivePath.displacement_add_eq_add_blockSum]

/-- A closed-interval path of total length `blocks * length` is equivalently
checked on every coordinate of each equal block.  Adjacent blocks overlap at
their common endpoint. -/
theorem inClosedInterval_mul_iff_forall_block
    {blocks length : ℕ} (hblocks : 0 < blocks) (hlength : 0 < length)
    (lower upper initial : ℝ) (increment : ℕ → ℝ) :
    InClosedInterval lower upper (blocks * length) initial increment ↔
      ∀ j < blocks, ∀ k ≤ length,
        initial + AdditivePath.displacement (j * length + k) increment ∈
          Set.Icc lower upper := by
  constructor
  · intro h j hj k hk
    have hindex : j * length + k < blocks * length + 1 :=
      Nat.lt_succ_of_le <| calc
        j * length + k ≤ j * length + length := Nat.add_le_add_left hk _
        _ = (j + 1) * length := by rw [Nat.add_mul]; simp
        _ ≤ blocks * length :=
          Nat.mul_le_mul_right length (Nat.succ_le_iff.2 hj)
    simpa [InClosedInterval, InWindows, history_eq_fromIncrements,
      AdditivePath.fromIncrements] using
      h ⟨j * length + k, hindex⟩
  · intro h q
    rw [history_eq_fromIncrements]
    change initial + AdditivePath.displacement (q : ℕ) increment ∈ Set.Icc lower upper
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

end ProbabilityTheory.RandomWalk
