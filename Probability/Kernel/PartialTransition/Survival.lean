import Probability.Kernel.FiniteState

/-!
# Survival of finite partial transitions

A finite partial transition chooses one of finitely many weighted branches.
A branch returning `none` is killed.  This file identifies the total mass of
the iterated sub-Markov kernel with the recursively accumulated weight of all
surviving branch histories.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α ξ : Type*} [Countable α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Fintype ξ]

/-- Total weight of the branch histories that survive for `n` transitions. -/
noncomputable def partialTransitionSurvivalWeight
    (weight : ξ → ENNReal) (next : α → ξ → Option α) : ℕ → α → ENNReal
  | 0, _ => 1
  | n + 1, a =>
      ∑ k, weight k * (next a k).elim 0
        (partialTransitionSurvivalWeight weight next n)

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
@[simp]
theorem partialTransitionSurvivalWeight_zero
    (weight : ξ → ENNReal) (next : α → ξ → Option α) (a : α) :
    partialTransitionSurvivalWeight weight next 0 a = 1 := rfl

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
@[simp]
theorem partialTransitionSurvivalWeight_succ
    (weight : ξ → ENNReal) (next : α → ξ → Option α) (n : ℕ) (a : α) :
    partialTransitionSurvivalWeight weight next (n + 1) a =
      ∑ k, weight k * (next a k).elim 0
        (partialTransitionSurvivalWeight weight next n) := rfl

/-- The mass remaining after `n` kernel transitions is exactly the total
weight of all branch histories that have not been killed. -/
theorem pow_apply_univ_ofFinitePartialTransition
    (weight : ξ → ENNReal) (next : α → ξ → Option α) (n : ℕ) (a : α) :
    (ofFinitePartialTransition weight next ^ n) a univ =
      partialTransitionSurvivalWeight weight next n a := by
  induction n generalizing a with
  | zero =>
      change Kernel.id a univ = 1
      rw [Kernel.id_apply]
      simp
  | succ n ih =>
      rw [show n + 1 = 1 + n by omega,
        Kernel.pow_add_apply_eq_lintegral _ 1 n a MeasurableSet.univ]
      simp only [pow_one]
      rw [lintegral_ofFinitePartialTransition]
      rw [show 1 + n = n + 1 by omega,
        partialTransitionSurvivalWeight_succ]
      apply Finset.sum_congr rfl
      intro k _
      cases hnext : next a k with
      | none => simp
      | some b => simp [ih b]

end ProbabilityTheory.Kernel
