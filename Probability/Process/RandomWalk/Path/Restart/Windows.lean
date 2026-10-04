/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Window.Basic

/-!
# Restarted windows for deterministic walk paths

A restarted window compares a path with its time-zero value up to a cutoff
and with its value at the cutoff afterwards.  This file contains only the
deterministic path construction; measurability and laws belong to the
probability layer.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Use time zero as reference through `cutoff`, then use time `cutoff` as
reference. -/
def restartAnchor (cutoff n : ℕ) : ℕ :=
  if n ≤ cutoff then 0 else cutoff

theorem restartAnchor_le (cutoff n : ℕ) : restartAnchor cutoff n ≤ n := by
  by_cases h : n ≤ cutoff
  · simp [restartAnchor, h]
  · simp only [restartAnchor, h, ↓reduceIte]
    omega

theorem restartAnchor_succ_le_parent (cutoff n : ℕ) :
    restartAnchor cutoff (n + 1) ≤ n := by
  by_cases h : n + 1 ≤ cutoff
  · simp [restartAnchor, h]
  · simp only [restartAnchor, h, ↓reduceIte]
    omega

@[simp] theorem restartAnchor_eq_zero {cutoff n : ℕ} (h : n ≤ cutoff) :
    restartAnchor cutoff n = 0 := by
  simp [restartAnchor, h]

@[simp] theorem restartAnchor_eq_cutoff {cutoff n : ℕ} (h : cutoff < n) :
    restartAnchor cutoff n = cutoff := by
  simp [restartAnchor, Nat.not_le_of_lt h]

/-- A finite path remains in the prescribed windows after subtracting the
path value at the deterministic restart anchor. -/
def InRestartedWindows {n : ℕ} (cutoff : ℕ) (window : ℕ → Set ℝ)
    (path : Fin (n + 1) → ℝ) : Prop :=
  ∀ k : Fin (n + 1), path k - path
    ⟨restartAnchor cutoff k, (restartAnchor_le cutoff k).trans_lt k.2⟩ ∈ window k

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
