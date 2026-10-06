/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange.LogDistortion
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Sequences of Skorokhod time changes

Finite compositions of increasing time changes and their logarithmic
distortion bounds.
-/

@[expose] public section

open Finset
open scoped NNReal

namespace Skorokhod

namespace TimeChange

/-- Compose the first `n` time changes in a sequence, in application order. -/
def cumulative (clock : ℕ → TimeChange) : ℕ → TimeChange
  | 0 => refl
  | n + 1 => (cumulative clock n).trans (clock n)

/-- Compose the `length` time changes beginning at `start`. -/
def segment (clock : ℕ → TimeChange) (start length : ℕ) : TimeChange :=
  cumulative (fun k => clock (start + k)) length

@[simp]
theorem cumulative_zero (clock : ℕ → TimeChange) : cumulative clock 0 = refl := rfl

@[simp]
theorem cumulative_succ (clock : ℕ → TimeChange) (n : ℕ) :
    cumulative clock n.succ = (cumulative clock n).trans (clock n) := rfl

/-- A cumulative composition splits into a prefix followed by its suffix. -/
theorem cumulative_add_eq_trans_segment (clock : ℕ → TimeChange) (start length : ℕ) :
    cumulative clock (start + length) =
      (cumulative clock start).trans (segment clock start length) := by
  induction length with
  | zero => simp [segment]
  | succ length ih =>
      rw [Nat.add_succ, cumulative_succ, ih]
      change ((cumulative clock start).trans
          (cumulative (fun k => clock (start + k)) length)).trans
          (clock (start + length)) =
        (cumulative clock start).trans
          (cumulative (fun k => clock (start + k)) (length + 1))
      rw [Nat.add_one, cumulative_succ, ← trans_assoc]

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

/-- The logarithmic distortion of a finite segment is bounded by the sum of
the distortions of its component time changes. -/
theorem logDistortion_segment_le_sum (clock : ℕ → TimeChange) (start length : ℕ) :
    (segment clock start length).logDistortion ≤
      ∑ k ∈ range length, (clock (start + k)).logDistortion := by
  exact logDistortion_cumulative_le_sum (fun k => clock (start + k)) length

/-- The logarithmic distortion of a finite segment is bounded by the total
nonnegative error available on its infinite tail. -/
theorem logDistortion_segment_le_tsum
    (clocks : ℕ → TimeChange) (error : ℕ → ℝ≥0)
    (hstep : ∀ n, (clocks n).logDistortion ≤ error n)
    (start length : ℕ) :
    (segment clocks start length).logDistortion ≤
      ∑' k, (error (start + k) : ENNReal) := by
  calc
    (segment clocks start length).logDistortion ≤
        ∑ k ∈ range length, (clocks (start + k)).logDistortion :=
      logDistortion_segment_le_sum clocks start length
    _ ≤ ∑ k ∈ range length, (error (start + k) : ENNReal) :=
      Finset.sum_le_sum fun k hk => hstep (start + k)
    _ ≤ ∑' k, (error (start + k) : ENNReal) :=
      ENNReal.sum_le_tsum (range length)

/-- The logarithmic distortion of any cumulative prefix is bounded by the
total summable error budget. -/
theorem logDistortion_cumulative_le_tsum
    (clocks : ℕ → TimeChange) (error : ℕ → ℝ≥0)
    (hstep : ∀ n, (clocks n).logDistortion ≤ error n)
    (herror : Summable error) (n : ℕ) :
    (cumulative clocks n).logDistortion ≤
      ENNReal.ofReal ((∑' i, error i : ℝ≥0) : ℝ) := by
  calc
    (cumulative clocks n).logDistortion ≤
        ∑ i ∈ range n, (clocks i).logDistortion :=
      logDistortion_cumulative_le_sum clocks n
    _ ≤ ∑ i ∈ range n, (error i : ENNReal) :=
      Finset.sum_le_sum fun i hi => hstep i
    _ ≤ ∑' i, (error i : ENNReal) := ENNReal.sum_le_tsum (range n)
    _ = ENNReal.ofReal ((∑' i, error i : ℝ≥0) : ℝ) := by
      rw [← ENNReal.coe_tsum herror, ENNReal.ofReal_coe_nnreal]

end TimeChange

end Skorokhod
