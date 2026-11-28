/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Step.Endpoint

/-!
# Restricting the noise of a partial random step

## Public declarations

In `ProbabilityTheory.Kernel`:

* `restrictNoise step accepted` kills a step whenever its noise lies outside
  `accepted`, retaining the original transition on accepted observations.
* `measurable_restrictNoise` preserves joint measurability.
* `runPartialSteps_restrictNoise` identifies the finite execution with the
  original execution when every noise is accepted, and with `none` otherwise.
* `endsInPrefix_restrictNoise_iff` and `survivesPrefix_restrictNoise_iff`
  identify the constrained path event with the original event intersected
  with `{ω | ∀ j < n, ωⱼ ∈ accepted}`.

The state and noise spaces are arbitrary; the restriction need not be
independent of the state update. All path execution and kernel laws use the
existing partial-step interfaces, rather than a second process definition.
-/

@[expose] public section
namespace ProbabilityTheory.Kernel
open MeasureTheory
open scoped Classical

/-- Retain the original partial transition only for accepted noise values. -/
noncomputable def restrictNoise {S E : Type*} (step : S → E → Option S)
    (accepted : Set E) (x : S) (z : E) : Option S :=
  if z ∈ accepted then step x z else none

theorem measurable_restrictNoise {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
    (step : S → E → Option S) (hs : Measurable (Function.uncurry step))
    {accepted : Set E} (ha : MeasurableSet accepted) :
    Measurable (Function.uncurry (restrictNoise step accepted)) :=
  hs.ite (ha.preimage measurable_snd) measurable_const

theorem runPartialSteps_restrictNoise {S E : Type*}
    (step : S → E → Option S) (accepted : Set E) (n : ℕ)
    (x : S) (history : Fin n → E) :
    runPartialSteps (restrictNoise step accepted) n x history =
      if ∀ j, history j ∈ accepted then runPartialSteps step n x history else none := by
  induction n generalizing x with
  | zero => simp [runPartialSteps]
  | succ n ih =>
    rw [runPartialSteps, runPartialSteps]
    simp only [restrictNoise]
    by_cases hh : history 0 ∈ accepted
    · simp only [hh, ↓reduceIte]
      have hall : (∀ j, history j ∈ accepted) ↔ ∀ j, Fin.tail history j ∈ accepted := by
        rw [Fin.forall_fin_succ]
        simp [hh, Fin.tail]
      simp only [hall]
      cases h : step x (history 0) with
      | none => simp
      | some y => simpa only [h, Option.bind_some] using ih y (Fin.tail history)
    · have hall : ¬∀ j, history j ∈ accepted := fun h => hh (h 0)
      simp [hh, hall]

private lemma forall_prefix_iff {E : Type*} (accepted : Set E) (n : ℕ) (ω : ℕ → E) :
    (∀ j : Fin n, Combinatorics.Sequence.blockCoordinates 0 n ω j ∈ accepted) ↔
      ∀ j < n, ω j ∈ accepted := by
  constructor
  · intro h j hj
    simpa only [Combinatorics.Sequence.blockCoordinates, zero_add] using h ⟨j, hj⟩
  · intro h j
    simpa only [Combinatorics.Sequence.blockCoordinates, zero_add] using h j j.isLt

theorem endsInPrefix_restrictNoise_iff {S E : Type*}
    (step : S → E → Option S) (accepted : Set E) (target : Set S)
    (n : ℕ) (x : S) (ω : ℕ → E) :
    EndsInPrefix (restrictNoise step accepted) target n x ω ↔
      EndsInPrefix step target n x ω ∧ ∀ j < n, ω j ∈ accepted := by
  simp only [EndsInPrefix, EndsIn, runPartialSteps_restrictNoise]
  simp only [forall_prefix_iff]
  split_ifs <;> simp_all

theorem survivesPrefix_restrictNoise_iff {S E : Type*}
    (step : S → E → Option S) (accepted : Set E)
    (n : ℕ) (x : S) (ω : ℕ → E) :
    SurvivesPrefix (restrictNoise step accepted) n x ω ↔
      SurvivesPrefix step n x ω ∧ ∀ j < n, ω j ∈ accepted := by
  simp only [SurvivesPrefix, Survives, runPartialSteps_restrictNoise]
  simp only [forall_prefix_iff]
  split_ifs <;> simp_all

end ProbabilityTheory.Kernel
