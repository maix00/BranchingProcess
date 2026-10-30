/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Restart.Basic
public import Probability.Process.RandomWalk.Path.Window.Basic

/-!
# Restarted windows for deterministic walk paths

A restarted window compares a path with its time-zero value up to a cutoff
and with its value at the cutoff afterwards.  This file contains only the
deterministic path construction; measurability and laws belong to the
probability layer.

## Public declarations

* `ProbabilityTheory.RandomWalk.inRestartedWindows_history_iff` shows the
  event is independent of the absolute initial position.
* `ProbabilityTheory.RandomWalk.inRestartedWindows_Icc_of_le_iff` identifies
  the pre-cutoff constant-window event with `InClosedInterval`.
* `ProbabilityTheory.RandomWalk.inRestartedWindows_Icc_add_iff` identifies a
  constant-window event through `cutoff + tail` with the intersection of the
  prefix and shifted-tail `InClosedInterval` events.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory.Process.Path

/-- Restarted-window membership depends only on increments, not on the
absolute initial position. -/
theorem inRestartedWindows_history_iff {n : ℕ}
    (cutoff : ℕ) (window : ℕ → Set ℝ)
    (initial : ℝ) (increment : ℕ → ℝ) :
    InRestartedWindows cutoff window
        (history n initial increment) ↔
      InRestartedWindows cutoff window
        (history n 0 increment) := by
  constructor <;> intro h k
  · have hk := h k
    simpa [history_eq_fromIncrements, AdditivePath.fromIncrements,
      add_sub_add_left_eq_sub] using hk
  · have hk := h k
    simpa [history_eq_fromIncrements, AdditivePath.fromIncrements,
      add_sub_add_left_eq_sub] using hk

/-- Before the cutoff, a constant restarted window is one zero-started
closed-interval event. -/
theorem inRestartedWindows_Icc_of_le_iff
    (lower upper : ℝ) {cutoff n : ℕ} (hn : n ≤ cutoff)
    (initial : ℝ) (increment : ℕ → ℝ) :
    InRestartedWindows cutoff (fun _ => Set.Icc lower upper)
        (history n initial increment) ↔
      InClosedInterval lower upper n 0 increment := by
  constructor <;> intro h k
  · have hk := h k
    have hkle : (k : ℕ) ≤ cutoff := (Nat.le_of_lt_succ k.2).trans hn
    simpa [restartAnchor_eq_zero hkle, history_eq_fromIncrements,
      AdditivePath.fromIncrements, add_sub_add_left_eq_sub] using hk
  · have hk := h k
    have hkle : (k : ℕ) ≤ cutoff := (Nat.le_of_lt_succ k.2).trans hn
    simpa [restartAnchor_eq_zero hkle, history_eq_fromIncrements,
      AdditivePath.fromIncrements, add_sub_add_left_eq_sub] using hk

/-- A constant restarted window through `cutoff + tail` is exactly the
intersection of two zero-started closed-interval path events, one for the
prefix and one for the shifted tail. -/
theorem inRestartedWindows_Icc_add_iff
    (lower upper : ℝ) (cutoff tail : ℕ) (initial : ℝ)
    (increment : ℕ → ℝ) :
    InRestartedWindows cutoff (fun _ => Set.Icc lower upper)
        (history (cutoff + tail) initial increment) ↔
      InClosedInterval lower upper cutoff 0 increment ∧
        InClosedInterval lower upper tail 0
          (fun k => increment (cutoff + k)) := by
  constructor
  · intro h
    constructor
    · intro k
      have hk := h ⟨k, by omega⟩
      have hkle : (k : ℕ) ≤ cutoff := by omega
      simp only [restartAnchor_eq_zero hkle, history_eq_fromIncrements,
        AdditivePath.fromIncrements, AdditivePath.displacement_zero,
        add_sub_add_left_eq_sub] at hk
      simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hk
    · intro k
      by_cases hk0 : (k : ℕ) = 0
      · have hzero := h ⟨0, by omega⟩
        have hkEq : k = 0 := Fin.ext hk0
        subst k
        simpa [history_eq_fromIncrements, AdditivePath.fromIncrements,
          restartAnchor_eq_zero (Nat.zero_le cutoff)] using hzero
      · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hk0
        have hck : cutoff < cutoff + (k : ℕ) := by omega
        have hk := h ⟨cutoff + k, by omega⟩
        simp only [restartAnchor_eq_cutoff hck, history_eq_fromIncrements,
          AdditivePath.fromIncrements, add_sub_add_left_eq_sub] at hk
        rw [AdditivePath.displacement_add cutoff k] at hk
        simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hk
  · rintro ⟨hprefix, htail⟩ k
    by_cases hk : (k : ℕ) ≤ cutoff
    · have hp := hprefix ⟨k, by omega⟩
      simpa [restartAnchor_eq_zero hk, history_eq_fromIncrements,
        AdditivePath.fromIncrements, add_sub_add_left_eq_sub] using hp
    · have hck : cutoff < (k : ℕ) := Nat.lt_of_not_ge hk
      let j : Fin (tail + 1) := ⟨(k : ℕ) - cutoff, by omega⟩
      have ht := htail j
      have hle : cutoff ≤ (k : ℕ) := hck.le
      simp only [history_eq_fromIncrements, AdditivePath.fromIncrements] at ht
      simp only [restartAnchor_eq_cutoff hck, history_eq_fromIncrements,
        AdditivePath.fromIncrements, add_sub_add_left_eq_sub]
      rw [show (k : ℕ) = cutoff + ((k : ℕ) - cutoff) by omega,
        AdditivePath.displacement_add]
      simpa only [j, add_sub_cancel_left, zero_add] using ht

end ProbabilityTheory.RandomWalk
