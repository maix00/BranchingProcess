/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Fin.Basic

/-!
# Finite paths relative to a restart schedule

## Public declarations

- `ProbabilityTheory.Process.Path.restartAnchor`: the deterministic schedule
  that uses time zero through a cutoff and the cutoff thereafter.
- `ProbabilityTheory.Process.Path.restartAnchor_le`,
  `ProbabilityTheory.Process.Path.restartAnchor_succ_le_parent`,
  `ProbabilityTheory.Process.Path.restartAnchor_eq_zero`, and
  `ProbabilityTheory.Process.Path.restartAnchor_eq_cutoff`: bounds and value
  formulas for this schedule.
- `ProbabilityTheory.Process.Path.InRestartedWindows`: for a finite path
  `x : Fin (n + 1) → E`, the relation
  `x k - x (restartAnchor cutoff k) ∈ window k` for every `k`.

The schedule and finite-path predicate use only discrete time and subtraction;
they do not impose a probability law or a real-valued state space.
-/

@[expose] public section

namespace ProbabilityTheory.Process.Path

/-- Use time zero as reference through `cutoff`, then use `cutoff` as the
reference time. -/
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

/-- A finite path stays in the prescribed windows after subtracting its value
at the deterministic restart anchor. -/
def InRestartedWindows {E : Type*} [Sub E] {n : ℕ} (cutoff : ℕ)
    (window : ℕ → Set E) (path : Fin (n + 1) → E) : Prop :=
  ∀ k : Fin (n + 1), path k - path
    ⟨restartAnchor cutoff k, by have h := restartAnchor_le cutoff k; omega⟩ ∈
      window k

end ProbabilityTheory.Process.Path
