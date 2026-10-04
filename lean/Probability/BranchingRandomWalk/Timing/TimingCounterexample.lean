/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Process.Stopping

/-!
# A one-generation look-ahead is not a stopping time

This two-outcome example checks the exact defect in the thesis's original
claim about `τₖ`: deciding at generation zero from a generation-one outcome
does not give a stopping time for the generation filtration.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory


/-- At time zero no outcome is observed; at all later times it is observed. -/
def lookaheadFiltration : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq n := if n = 0 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i = 0
    · simp [hi]
    · have hj : j ≠ 0 := by
        intro hj
        exact hi (Nat.eq_zero_of_le_zero (by simpa [hj] using hij))
      simp [hi, hj]
  le' := by intro n; exact le_top

/-- A time defined using the next generation can fail the stopping-time test. -/
theorem lookahead_time_not_stopping :
    ¬ IsStoppingTime lookaheadFiltration
      (fun ω : Bool => if ω then (0 : WithTop ℕ) else ⊤) := by
  intro h
  have h₀ := h 0
  have hevent :
      {ω : Bool | (if ω then (0 : WithTop ℕ) else ⊤) ≤ (0 : ℕ)} = {true} := by
    ext ω
    cases ω <;> simp
  change MeasurableSet[⊥]
    {ω : Bool | (if ω then (0 : WithTop ℕ) else ⊤) ≤ (0 : ℕ)} at h₀
  rw [hevent, MeasurableSpace.measurableSet_bot_iff] at h₀
  rcases h₀ with h₀ | h₀
  · have hmem := congrArg (fun s : Set Bool => (true : Bool) ∈ s) h₀
    simp at hmem
  · have hmem := congrArg (fun s : Set Bool => (false : Bool) ∈ s) h₀
    simp at hmem

/-- A trial outcome is observed at generation two; generation one still has
the trivial σ-algebra. This models choosing the generation-one reserve
population only after seeing whether a later trial failed. -/
def delayedTrialFiltration : Filtration ℕ (⊤ : MeasurableSpace Bool) where
  seq n := if n < 2 then ⊥ else ⊤
  mono' := by
    intro i j hij
    by_cases hi : i < 2
    · simp [hi]
    · have hj : ¬ j < 2 := by omega
      simp [hi, hj]
  le' := by intro n; exact le_top

/-- Retrospective generation-one selection can violate the adaptedness
required by a generationwise coupling lemma. -/
theorem retrospective_state_not_adapted :
    ¬ Adapted delayedTrialFiltration
      (fun n (ω : Bool) => if n = 1 then ω else false) := by
  intro h
  have hmeas := h 1
  have hevent :
      {ω : Bool | (if (1 : ℕ) = 1 then ω else false) = true} = {true} := by
    ext ω
    cases ω <;> simp
  have hset : MeasurableSet[delayedTrialFiltration 1]
      {ω : Bool | (if (1 : ℕ) = 1 then ω else false) = true} :=
    hmeas (measurableSet_singleton true)
  change MeasurableSet[⊥]
    {ω : Bool | (if (1 : ℕ) = 1 then ω else false) = true} at hset
  rw [hevent, MeasurableSpace.measurableSet_bot_iff] at hset
  rcases hset with hset | hset
  · have hmem := congrArg (fun s : Set Bool => (true : Bool) ∈ s) hset
    simp at hmem
  · have hmem := congrArg (fun s : Set Bool => (false : Bool) ∈ s) hset
    simp at hmem

/-- Knowing the population size at each generation does not make the identity
of the retained particle observable. A generationwise coupling needs the
latter in order to match child marks. -/
theorem adapted_count_does_not_imply_adapted_identity :
    Adapted delayedTrialFiltration
        (fun _ (_ : Bool) => (1 : ℕ)) ∧
      ¬ Adapted delayedTrialFiltration
        (fun n (ω : Bool) => if n = 1 then ω else false) := by
  constructor
  · intro n
    exact measurable_const
  · exact retrospective_state_not_adapted

end ProbabilityTheory.BranchingRandomWalk
