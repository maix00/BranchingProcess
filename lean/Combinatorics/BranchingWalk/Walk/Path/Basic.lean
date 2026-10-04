/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Basic

/-!
# Paths of walks

Finite histories and partial sums depend only on an increment path. They are
kept in the deterministic layer. Probability laws on increment paths are
introduced separately.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace Combinatorics.Branching.Walk

variable {E : Type*} [AddCommMonoid E]

/-- Sum of the first `n` increments. -/
def partialSum (n : ℕ) (increment : ℕ → E) : E :=
  ∑ k ∈ Finset.range n, increment k

@[simp] theorem partialSum_zero (increment : ℕ → E) :
    partialSum 0 increment = 0 := by
  simp [partialSum]

theorem partialSum_succ (n : ℕ) (increment : ℕ → E) :
    partialSum (n + 1) increment = partialSum n increment + increment n := by
  simp [partialSum, Finset.sum_range_succ]

section AddCommGroup

variable {G : Type*} [AddCommGroup G]

/-- Negating every increment negates every partial sum. -/
@[simp] theorem partialSum_neg (n : ℕ) (increment : ℕ → G) :
    partialSum n (fun k => -increment k) = -partialSum n increment := by
  simp [partialSum]

end AddCommGroup

/-- Partial sums split at any deterministic time. -/
theorem partialSum_add (m n : ℕ) (increment : ℕ → E) :
    partialSum (m + n) increment =
      partialSum m increment +
        partialSum n (fun k => increment (m + k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, partialSum_succ, ih, partialSum_succ]
      ac_rfl

theorem partialSum_measurable [MeasurableSpace E] [MeasurableAdd₂ E]
    (n : ℕ) : Measurable (partialSum (E := E) n) := by
  unfold partialSum
  exact Finset.measurable_sum (Finset.range n)
    (fun k _ => measurable_pi_apply k)

omit [AddCommMonoid E] in
/-- Removing a deterministic prefix from an increment path is measurable. -/
theorem measurable_natAdd [MeasurableSpace E] (offset : ℕ) :
    Measurable (fun increment : ℕ → E =>
      fun n => increment (offset + n)) := by
  rw [measurable_pi_iff]
  exact fun n => measurable_pi_apply (offset + n)

/-- The position process associated with an increment path and an initial
position. Its argument order is the standard process convention
`Time → Sample → State`. -/
def positionProcess (initial : E) : ℕ → (ℕ → E) → E :=
  fun n increment => initial + partialSum n increment

@[simp] theorem positionProcess_zero (initial : E) (increment : ℕ → E) :
    positionProcess initial 0 increment = initial := by
  simp [positionProcess]

theorem positionProcess_succ (initial : E) (increment : ℕ → E) (n : ℕ) :
    positionProcess initial (n + 1) increment =
      positionProcess initial n increment + increment n := by
  simp only [positionProcess, partialSum_succ]
  ac_rfl

/-- Each time coordinate of the position process is measurable. -/
theorem positionProcess_measurable [MeasurableSpace E] [MeasurableAdd₂ E]
    (initial : E) (n : ℕ) : Measurable (positionProcess initial n) :=
  measurable_const.add (partialSum_measurable n)

/-- The entire increment-path to position-path map is measurable for the
product measurable structures. -/
theorem positionProcess_path_measurable
    [MeasurableSpace E] [MeasurableAdd₂ E] (initial : E) :
    Measurable (fun increment : ℕ → E =>
      fun n => positionProcess initial n increment) := by
  rw [measurable_pi_iff]
  exact positionProcess_measurable initial

/-- Positions at times `0, ..., n`, starting from `initial`. -/
def history (n : ℕ) (initial : E) (increment : ℕ → E) :
    Fin (n + 1) → E :=
  fun k => initial + partialSum k increment

/-- A finite history is the restriction of the full position process to its
first `n + 1` time coordinates. -/
theorem history_eq_positionProcess_restrict (n : ℕ) (initial : E)
    (increment : ℕ → E) :
    history n initial increment =
      fun k : Fin (n + 1) => positionProcess initial k increment := rfl

@[simp] theorem history_zero (n : ℕ) (initial : E)
    (increment : ℕ → E) :
    history n initial increment ⟨0, Nat.zero_lt_succ n⟩ = initial := by
  simp [history]

theorem history_last (n : ℕ) (initial : E) (increment : ℕ → E) :
    history n initial increment ⟨n, Nat.lt_succ_self n⟩ =
      initial + partialSum n increment := rfl

/-- A history restarted at time `m` agrees with the corresponding segment of
the original history. -/
theorem history_restart (m n : ℕ) (initial : E) (increment : ℕ → E)
    (k : Fin (n + 1)) :
    history n (initial + partialSum m increment)
        (fun j => increment (m + j)) k =
      history (m + n) initial increment
        ⟨m + k, Nat.add_lt_add_left k.isLt m⟩ := by
  simp only [history]
  rw [partialSum_add]
  ac_rfl

theorem history_measurable [MeasurableSpace E] [MeasurableAdd₂ E]
    (n : ℕ) (initial : E) : Measurable (history n initial) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_const.add (partialSum_measurable k)

theorem history_joint_measurable [MeasurableSpace E] [MeasurableAdd₂ E]
    (n : ℕ) :
    Measurable (fun p : E × (ℕ → E) => history n p.1 p.2) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_fst.add ((partialSum_measurable k).comp measurable_snd)

/-- Add a time-zero position in front of a nonempty finite history. -/
def prependHistory {n : ℕ} (initial : E) (tail : Fin (n + 1) → E) :
    Fin (n + 2) → E :=
  Fin.cases initial tail

/-- Remove the first coordinate of an increment path. -/
def incrementTail (increment : ℕ → E) : ℕ → E :=
  fun k => increment (k + 1)

omit [AddCommMonoid E] in
@[simp] theorem prependHistory_zero {n : ℕ} (initial : E)
    (tail : Fin (n + 1) → E) :
    prependHistory initial tail 0 = initial := rfl

omit [AddCommMonoid E] in
@[simp] theorem prependHistory_succ {n : ℕ} (initial : E)
    (tail : Fin (n + 1) → E) (k : Fin (n + 1)) :
    prependHistory initial tail k.succ = tail k := rfl

omit [AddCommMonoid E] in
theorem prependHistory_joint_measurable [MeasurableSpace E] (n : ℕ) :
    Measurable (fun p : E × (Fin (n + 1) → E) =>
      prependHistory p.1 p.2) := by
  rw [measurable_pi_iff]
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact measurable_fst
  · exact measurable_pi_apply j |>.comp measurable_snd

omit [AddCommMonoid E] in
theorem incrementTail_measurable [MeasurableSpace E] :
    Measurable (incrementTail (E := E)) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_pi_apply (k + 1)

/-- Partial sums split into the first increment and the partial sums of the
remaining path. -/
theorem partialSum_succ_eq_head_add_tail (n : ℕ)
    (increment : ℕ → E) :
    partialSum (n + 1) increment =
      increment 0 + partialSum n (incrementTail increment) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [partialSum_succ, ih, partialSum_succ]
      simp only [incrementTail]
      ac_rfl

/-- A finite history has the expected first-step decomposition. -/
theorem history_succ (n : ℕ) (initial : E) (increment : ℕ → E) :
    history (n + 1) initial increment =
      prependHistory initial
        (history n (initial + increment 0) (incrementTail increment)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [history]
  · simp only [history, prependHistory_succ]
    change initial + partialSum (j.val + 1) increment =
      initial + increment 0 + partialSum j.val (incrementTail increment)
    rw [partialSum_succ_eq_head_add_tail]
    ac_rfl

end Combinatorics.Branching.Walk

end
