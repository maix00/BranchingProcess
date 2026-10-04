/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Concurrent
import Probability.BranchingRandomWalk.Timing.CausalSchedule

/-!
# Causally scheduled selected branching populations

This file instantiates the concurrent root-indexed population with the
recursive stopping-time schedule.  Trial indices and pre-sampled root labels
remain separate; `root : ℕ → Root` assigns a tree to each trial.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace Concurrent

open Combinatorics.UlamHarris Combinatorics.Branching

theorem scheduledComponent_adapted
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (ready : ℕ → ℕ → Set (RootIndexed.StepField Root α X))
    (hready : ∀ i n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] (ready i n)) :
    ∀ i n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (component (CausalSchedule.time initial ready) R root i n) := by
  apply component_adapted R hR root
  exact CausalSchedule.time_isStoppingTime
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    initial hinitial ready hready

theorem scheduledPopulation_adapted
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root)
    (initial : RootIndexed.StepField Root α X → WithTop ℕ)
    (hinitial : IsStoppingTime
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) initial)
    (ready : ℕ → ℕ → Set (RootIndexed.StepField Root α X))
    (hready : ∀ i n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] (ready i n))
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset ℕ)
    (henabled : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (population enabled (CausalSchedule.time initial ready) R root n) := by
  apply population_adapted R hR root enabled
    (CausalSchedule.time initial ready) henabled henabledRange
  exact CausalSchedule.time_isStoppingTime
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    initial hinitial ready hready

end Concurrent
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
