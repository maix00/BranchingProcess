module

public import Combinatorics.BranchingWalk.Walk.Path.Block.Corridor
public import Combinatorics.BranchingWalk.Walk.Path.Window

/-!
# Finite partitions of walk paths

Deterministic identities and error bounds for reconstructing partition
endpoints from consecutive block sums.
-/

open scoped BigOperators

@[expose] public section

namespace Combinatorics.Branching.Walk

variable {E : Type*} [AddCommMonoid E]

/-- Reconstruct the successive endpoints of a finite block vector.  The
zeroth endpoint is `0`; endpoint `j` is the sum of blocks with index below
`j`. -/
def blockPartialSums {blocks : ℕ} (x : Fin blocks → E) :
    Fin (blocks + 1) → E :=
  fun j => ∑ k ∈ (Finset.univ.filter
    (fun k : Fin blocks => (k : ℕ) < (j : ℕ))), x k

@[simp]
theorem blockPartialSums_zero {blocks : ℕ} (x : Fin blocks → E) :
    blockPartialSums x 0 = 0 := by
  simp [blockPartialSums]

/-- `blockPartialSums` is the usual sum over the corresponding natural-number
range. -/
theorem blockPartialSums_eq_sum_range {blocks : ℕ}
    (x : Fin blocks → E) (j : Fin (blocks + 1)) :
    blockPartialSums x j =
      ∑ k : Fin (j : ℕ),
        x ⟨k, lt_of_lt_of_le k.isLt (Nat.lt_succ_iff.mp j.isLt)⟩ := by
  simp only [blockPartialSums]
  apply Finset.sum_bij
    (s := Finset.univ.filter
      (fun k : Fin blocks => (k : ℕ) < (j : ℕ)))
    (t := Finset.univ) (fun k hk =>
      ⟨k, (Finset.mem_filter.mp hk).2⟩)
  · intro k hk
    exact Finset.mem_univ _
  · intro a ha b hb hab
    exact Fin.ext (show (a : ℕ) = (b : ℕ) from
      congrArg (fun z : Fin (j : ℕ) => (z : ℕ)) hab)
  · intro k hk
    have hklt : (k : ℕ) < blocks :=
      lt_of_lt_of_le k.isLt (Nat.lt_succ_iff.mp j.isLt)
    refine ⟨⟨k, hklt⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, k.isLt⟩, ?_⟩
    rfl
  · intro k hk
    rfl

/-- The partial sums of one increment block are the positions of the
corresponding segment of the original walk, translated to start at zero. -/
theorem blockPartialSums_blockCoordinates {length : ℕ}
    (start : ℕ) (increment : ℕ → E)
    (j : Fin (length + 1)) :
    blockPartialSums (blockCoordinates start length increment) j =
      blockSum start j increment := by
  rw [blockPartialSums_eq_sum_range, blockSum_eq_partialSum_natAdd]
  simpa [partialSum, blockCoordinates] using
    (Fin.sum_univ_eq_sum_range
      (fun k => increment (start + k)) (j : ℕ))

/-- Cumulative consecutive differences telescope to the displacement from
the zeroth endpoint. -/
theorem blockPartialSums_consecutiveDifferences
    {G : Type*} [AddCommGroup G] {blocks : ℕ}
    (f : Fin (blocks + 1) → G) (j : Fin (blocks + 1)) :
    blockPartialSums (fun k : Fin blocks => f k.succ - f k.castSucc) j =
      f j - f 0 := by
  let g : ℕ → G := fun k => if hk : k < blocks + 1 then f ⟨k, hk⟩ else 0
  let embed : Fin (j : ℕ) → Fin blocks := fun k =>
    ⟨k, lt_of_lt_of_le k.isLt (Nat.lt_succ_iff.mp j.isLt)⟩
  have hgj : g (j : ℕ) = f j := by
    dsimp only [g]
    rw [dite_eq_left j.isLt]
  have hg0 : g 0 = f 0 := by
    dsimp only [g]
    rw [dite_eq_left (by omega : 0 < blocks + 1)]
    congr 1
  rw [blockPartialSums_eq_sum_range]
  change (∑ k : Fin (j : ℕ),
    (f (embed k).succ - f (embed k).castSucc)) = _
  calc
    ∑ k : Fin (j : ℕ), (f (embed k).succ - f (embed k).castSucc) =
        ∑ k : Fin (j : ℕ), (g (k + 1) - g k) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk0 : (k : ℕ) < blocks + 1 :=
            lt_trans k.isLt j.isLt
          have hk1 : (k : ℕ) + 1 < blocks + 1 := by
            omega
          simp only [g]
          rw [dite_eq_left hk1, dite_eq_left hk0]
          rfl
    _ = ∑ k ∈ Finset.range (j : ℕ), (g (k + 1) - g k) :=
      Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k) (j : ℕ)
    _ = g j - g 0 := Finset.sum_range_sub g (j : ℕ)
    _ = f j - f 0 := by rw [hgj, hg0]

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
theorem abs_partialSum_sub_le_three_mul_of_blockBounds
    {horizon blocks length left right : ℕ} {radius : ℝ}
    {increment : ℕ → ℝ} (hlength : 0 < length) (hradius : 0 ≤ radius)
    (hcover : horizon ≤ blocks * length)
    (hleft : left < horizon) (hright : right < horizon)
    (hle : left ≤ right) (hdistance : right - left ≤ length)
    (hblocks : ∀ block < blocks, ∀ offset ≤ length,
      |blockSum (block * length) offset increment| ≤ radius) :
    |partialSum right increment - partialSum left increment| ≤ 3 * radius := by
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
        |blockSum (leftBlock * length + length) k increment| ≤ radius := by
      simpa [Nat.add_mul] using hblocks (leftBlock + 1) hnextLt
    simpa [hleftEq, hrightEq, hnext, Nat.add_mul, Nat.add_assoc] using
      (abs_partialSum_nextBlock_add_sub_partialSum_add_le_three_mul
        hleftOffset hrightOffset
          (hblocks leftBlock hleftBlock) hnextBounds)

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

/-- Equal consecutive block sums reconstruct the partial sum at every block
endpoint. -/
theorem blockPartialSums_blockSum {blocks length : ℕ}
    (increment : ℕ → E) (j : Fin (blocks + 1)) :
    blockPartialSums
        (fun k : Fin blocks => blockSum (k * length) length increment) j =
      partialSum (j * length) increment := by
  rw [partialSum_mul_eq_sum_blockSum]
  simp only [blockPartialSums]
  apply Finset.sum_bij
    (s := Finset.univ.filter
      (fun k : Fin blocks => (k : ℕ) < (j : ℕ)))
    (t := Finset.range (j : ℕ)) (fun k _ => (k : ℕ))
  · intro k hk
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro k hk
    have hjle : (j : ℕ) ≤ blocks := Nat.lt_succ_iff.mp j.isLt
    have hklt : k < blocks :=
      lt_of_lt_of_le (Finset.mem_range.mp hk) hjle
    refine ⟨⟨k, hklt⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp hk⟩
  · intro k hk
    rfl

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


