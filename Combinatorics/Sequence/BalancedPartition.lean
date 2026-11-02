/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Balanced partitions of finite horizons

## Public declarations

When $m>0$ and $q=\lfloor N/m\rfloor>0$, put
$s=m+\lfloor (N\bmod m)/q\rfloor$ and
$r=(N\bmod m)\bmod q$. Writing its entries as $(b_i)_{i<q}$, the list
$b$ of balanced block lengths satisfies $|b|=q$,
$\sum_{i<q}b_i=N$, exactly $r$ entries equal $s+1$, and every other
entry equals $s$.

- `Combinatorics.Sequence.balancedBlockCount N m` defines $q=\lfloor N/m\rfloor$.
- `Combinatorics.Sequence.balancedBlockShortLength N m` defines
  $s=m+\lfloor(N\bmod m)/q\rfloor$.
- `Combinatorics.Sequence.balancedBlockLengths N m` is the concatenation of
  $q-r$ copies of $s$ and $r$ copies of $s+1$, where
  $r=(N\bmod m)\bmod q$.
- Given $q>0$, `Combinatorics.Sequence.balancedBlockLengths_length` and
  `Combinatorics.Sequence.balancedBlockLengths_sum` state
  $|b|=q$ and $\sum_{i<q}b_i=N$. For each entry,
  `Combinatorics.Sequence.mem_balancedBlockLengths` gives $b_i=s$ or
  $b_i=s+1$.

The quotient/remainder construction is independent of probability and
asymptotic assumptions. Its limiting scale results belong to
`Analysis.Asymptotics.Scale.Block.Partition`.
-/

@[expose] public section

namespace Combinatorics.Sequence

/-- The number of blocks in the balanced partition of `total` relative to a
reference length. -/
def balancedBlockCount (total referenceLength : ℕ) : ℕ :=
  total / referenceLength

/-- The shorter of the two block lengths in a balanced partition. -/
def balancedBlockShortLength (total referenceLength : ℕ) : ℕ :=
  referenceLength +
    (total % referenceLength) / balancedBlockCount total referenceLength

/-- Split `total` into blocks of two consecutive lengths, distributing the
remainder evenly. When the reference block count is positive, the list has
exactly `total / referenceLength` entries and its lengths sum to `total`. -/
def balancedBlockLengths (total referenceLength : ℕ) : List ℕ :=
  List.replicate
      (balancedBlockCount total referenceLength -
        (total % referenceLength % balancedBlockCount total referenceLength))
      (balancedBlockShortLength total referenceLength) ++
    List.replicate
      (total % referenceLength % balancedBlockCount total referenceLength)
      (balancedBlockShortLength total referenceLength + 1)

/-- The balanced partition has exactly the reference quotient many blocks. -/
theorem balancedBlockLengths_length {total referenceLength : ℕ}
    (hcount : 0 < balancedBlockCount total referenceLength) :
    (balancedBlockLengths total referenceLength).length =
      balancedBlockCount total referenceLength := by
  have hrem : total % referenceLength % balancedBlockCount total referenceLength <
      balancedBlockCount total referenceLength := by
    dsimp [balancedBlockCount]
    exact Nat.mod_lt _ hcount
  simp [balancedBlockLengths, List.length_replicate,
    Nat.sub_add_cancel (Nat.le_of_lt hrem)]

/-- The balanced partition covers the horizon exactly, with no discarded
remainder. -/
theorem balancedBlockLengths_sum {total referenceLength : ℕ}
    (hcount : 0 < balancedBlockCount total referenceLength) :
    (balancedBlockLengths total referenceLength).sum = total := by
  let q := balancedBlockCount total referenceLength
  let r := total % referenceLength % q
  let s := balancedBlockShortLength total referenceLength
  have hr : r < q := by
    dsimp [r, q, balancedBlockCount]
    exact Nat.mod_lt (total % referenceLength) hcount
  have hrem :
      q * ((total % referenceLength) / q) + r = total % referenceLength := by
    dsimp [q, r, balancedBlockCount]
    exact Nat.div_add_mod (total % referenceLength) _
  have hdiv : q * referenceLength + total % referenceLength = total := by
    dsimp [q, balancedBlockCount]
    simpa [Nat.mul_comm] using Nat.div_add_mod total referenceLength
  change (List.replicate (q - r) s ++ List.replicate r (s + 1)).sum = total
  rw [List.sum_append, List.sum_replicate, List.sum_replicate]
  calc
    (q - r) * s + r * (s + 1) = q * s + r := by
      rw [Nat.mul_add]
      simp only [Nat.mul_one]
      calc
        (q - r) * s + (r * s + r) =
            ((q - r) + r) * s + r := by
          calc
            (q - r) * s + (r * s + r) =
                ((q - r) * s + r * s) + r := by ac_rfl
            _ = ((q - r) + r) * s + r := by rw [← Nat.add_mul]
        _ = q * s + r := by rw [Nat.sub_add_cancel (Nat.le_of_lt hr)]
    _ = total := by
      calc
        q * s + r =
            q * referenceLength +
              (q * ((total % referenceLength) / q) + r) := by
          change q * (referenceLength + (total % referenceLength) / q) + r = _
          rw [Nat.mul_add]
          ac_rfl
        _ = q * referenceLength + total % referenceLength := by rw [hrem]
        _ = total := hdiv

/-- Every balanced block is one of the two adjacent integer lengths around
the average. -/
theorem mem_balancedBlockLengths {total referenceLength length : ℕ}
    (hmem : length ∈ balancedBlockLengths total referenceLength) :
    length = balancedBlockShortLength total referenceLength ∨
      length = balancedBlockShortLength total referenceLength + 1 := by
  simp only [balancedBlockLengths, List.mem_append, List.mem_replicate] at hmem
  rcases hmem with ⟨_, hlen⟩ | ⟨_, hlen⟩
  · exact Or.inl hlen
  · exact Or.inr hlen

end Combinatorics.Sequence

end
