/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange.LogDistortion

/-!
# Sequences of Skorokhod time changes

Finite compositions of increasing time changes and their logarithmic
distortion bounds.
-/

@[expose] public section

open Finset

namespace Skorokhod

namespace TimeChange

/-- Compose the first `n` time changes in a sequence, in application order. -/
def cumulative (clock : ℕ → TimeChange) : ℕ → TimeChange
  | 0 => refl
  | n + 1 => (cumulative clock n).trans (clock n)

@[simp]
theorem cumulative_zero (clock : ℕ → TimeChange) : cumulative clock 0 = refl := rfl

@[simp]
theorem cumulative_succ (clock : ℕ → TimeChange) (n : ℕ) :
    cumulative clock n.succ = (cumulative clock n).trans (clock n) := rfl

/-- The logarithmic distortion of a finite composition is bounded by the sum
of the distortions of its factors. -/
theorem logDistortion_cumulative_le_sum (clock : ℕ → TimeChange) (n : ℕ) :
    (cumulative clock n).logDistortion ≤ ∑ i ∈ range n, (clock i).logDistortion := by
  induction n with
  | zero => simp [cumulative]
  | succ n ih =>
      rw [cumulative_succ]
      calc
        ((cumulative clock n).trans (clock n)).logDistortion ≤
            (cumulative clock n).logDistortion + (clock n).logDistortion :=
          logDistortion_trans_le _ _
        _ ≤ (∑ i ∈ range n, (clock i).logDistortion) + (clock n).logDistortion :=
          add_le_add ih le_rfl
        _ = ∑ i ∈ range n.succ, (clock i).logDistortion := by
          rw [sum_range_succ]

end TimeChange

end Skorokhod
