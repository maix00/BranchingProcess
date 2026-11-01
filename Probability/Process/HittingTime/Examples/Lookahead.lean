/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Process.Stopping

/-!
# Finite-filtration counterexamples for stopping times

## Public declarations

- `lookaheadFiltration` has $\mathcal F_0=\bot$ and
  $\mathcal F_n=\top$ for $n>0$; `lookaheadRawTime` is $0$ on `true` and
  $\top$ on `false`; `lookaheadCompletionTime` is $\tau+1$.
- `lookahead_time_not_stopping` gives a raw time that observes the next
  generation and violates $\{\tau\leq n\}\in\mathcal F_n$.
- `lookahead_completion_isStoppingTime` shows that a one-step completion is
  stopping when the filtration reveals its outcome at that completion time.
- `delayed_lookahead_completion_not_stopping` shows that shifting an
  anticipative time by one does not suffice when the outcome is revealed
  later.
- `retrospective_state_not_adapted` and
  `adapted_count_does_not_imply_adapted_identity` separate adapted population
  counts from adapted particle identities.

`delayedTrialFiltration` keeps $\mathcal F_0=\mathcal F_1=\bot$ and reveals
the outcome from generation two onward. These finite examples isolate the
measurability requirement in the stopping-time definition.

These two-outcome examples check the timing convention for a raw candidate
time `τ` and its completion `τ + 1`. A raw time that reads the next generation
can fail the stopping-time test; its successor is stopping when that next
generation reveals the event, but a one-step shift does not repair arbitrary
anticipation when the filtration reveals the outcome later.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.Process.HittingTime.Examples

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

/-- A raw candidate time which reads the next generation's outcome. -/
def lookaheadRawTime (ω : Bool) : WithTop ℕ :=
  if ω then 0 else ⊤

/-- The corresponding observable completion time, one generation later. -/
def lookaheadCompletionTime (ω : Bool) : WithTop ℕ :=
  lookaheadRawTime ω + 1

/-- A time defined using the next generation can fail the stopping-time test. -/
theorem lookahead_time_not_stopping :
    ¬ IsStoppingTime lookaheadFiltration
      lookaheadRawTime := by
  intro h
  have h₀ := h 0
  have hevent :
      {ω : Bool | lookaheadRawTime ω ≤ (0 : ℕ)} = {true} := by
    ext ω
    cases ω <;> simp [lookaheadRawTime]
  change MeasurableSet[⊥] {ω : Bool | lookaheadRawTime ω ≤ (0 : ℕ)} at h₀
  rw [hevent, MeasurableSpace.measurableSet_bot_iff] at h₀
  rcases h₀ with h₀ | h₀
  · have hmem := congrArg (fun s : Set Bool => (true : Bool) ∈ s) h₀
    simp at hmem
  · have hmem := congrArg (fun s : Set Bool => (false : Bool) ∈ s) h₀
    simp at hmem

/-- In the look-ahead model the completion time is a stopping time because
the filtration reveals the raw event by generation one. -/
theorem lookahead_completion_isStoppingTime :
    IsStoppingTime lookaheadFiltration lookaheadCompletionTime := by
  intro n
  change MeasurableSet[lookaheadFiltration n]
    {ω | lookaheadCompletionTime ω ≤ n}
  by_cases hn : n = 0
  · subst n
    have hevent :
        {ω : Bool | lookaheadCompletionTime ω ≤ (0 : ℕ)} = ∅ := by
      ext ω
      cases ω <;> simp [lookaheadCompletionTime, lookaheadRawTime]
    rw [hevent]
    exact (lookaheadFiltration 0).measurableSet_empty
  · rw [show lookaheadFiltration n = ⊤ by simp [lookaheadFiltration, hn]]
    exact MeasurableSpace.measurableSet_top

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

/-- A one-generation shift does not turn an arbitrary anticipative time into
a stopping time: here the outcome is first revealed only at generation two. -/
theorem delayed_lookahead_completion_not_stopping :
    ¬ IsStoppingTime delayedTrialFiltration lookaheadCompletionTime := by
  intro h
  have h₁ := h 1
  have hevent :
      {ω : Bool | lookaheadCompletionTime ω ≤ (1 : ℕ)} = {true} := by
    ext ω
    cases ω <;> simp [lookaheadCompletionTime, lookaheadRawTime]
  change MeasurableSet[⊥] {ω : Bool | lookaheadCompletionTime ω ≤ (1 : ℕ)} at h₁
  rw [hevent, MeasurableSpace.measurableSet_bot_iff] at h₁
  rcases h₁ with h₁ | h₁
  · have hmem := congrArg (fun s : Set Bool => (true : Bool) ∈ s) h₁
    simp at hmem
  · have hmem := congrArg (fun s : Set Bool => (false : Bool) ∈ s) h₁
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

end ProbabilityTheory.Process.HittingTime.Examples
