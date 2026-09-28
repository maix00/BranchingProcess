import Probability.Kernel.FiniteState
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Constructions.Pi

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

/-- Endpoint obtained by following a finite branch history, or `none` if one
of its partial transitions is killed. -/
def runPartialTransitions (next : α → ξ → Option α) :
    (n : ℕ) → α → (Fin n → ξ) → Option α
  | 0, a, _ => some a
  | n + 1, a, history =>
      (next a (history 0)).bind fun b =>
        runPartialTransitions next n b (Fin.tail history)

/-- Explicit finite sum of the weights of all surviving branch histories. -/
noncomputable def partialTransitionHistoryWeight
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (n : ℕ) (a : α) : ENNReal :=
  ∑ history : Fin n → ξ,
    (∏ k, weight (history k)) *
      if (runPartialTransitions next n a history).isSome then 1 else 0

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

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem partialTransitionHistoryWeight_succ
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (n : ℕ) (a : α) :
    partialTransitionHistoryWeight weight next (n + 1) a =
      ∑ k, weight k * (next a k).elim 0
        (partialTransitionHistoryWeight weight next n) := by
  rw [partialTransitionHistoryWeight]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ξ)).sum_comp]
  simp_rw [Fin.consEquiv_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  have htail (history : Fin n → ξ) :
      Fin.tail ((Fin.consEquiv (fun _ : Fin (n + 1) => ξ)) (k, history)) =
        history := by
    change Fin.tail (@Fin.cons n (fun _ => ξ) k history) = history
    exact Fin.tail_cons (α := fun _ => ξ) k history
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.prod_univ_succ,
    runPartialTransitions]
  cases next a k with
  | none => simp
  | some b =>
      simp only [Option.bind_some, Option.elim_some]
      simp_rw [Fin.cons_succ, htail, mul_assoc]
      rw [← Finset.mul_sum]
      rfl

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The recursive survival weight is the explicit sum over finite branch
histories. -/
theorem partialTransitionHistoryWeight_eq_survivalWeight
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (n : ℕ) (a : α) :
    partialTransitionHistoryWeight weight next n a =
      partialTransitionSurvivalWeight weight next n a := by
  induction n generalizing a with
  | zero => simp [partialTransitionHistoryWeight, runPartialTransitions]
  | succ n ih =>
      rw [partialTransitionHistoryWeight_succ,
        partialTransitionSurvivalWeight_succ]
      apply Finset.sum_congr rfl
      intro k _
      cases next a k <;> simp [ih]

/-- The finite set of branch histories that survive all `n` partial
transitions. -/
def survivingPartialTransitionHistories
    (next : α → ξ → Option α) (n : ℕ) (a : α) :
    Finset (Fin n → ξ) :=
  Finset.univ.filter fun history =>
    (runPartialTransitions next n a history).isSome

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Under a finite product law whose singleton masses are the branch
weights, the probability of survival is the explicit history weight. -/
theorem pi_apply_survivingPartialTransitionHistories
    [MeasurableSpace ξ] [MeasurableSingletonClass ξ]
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (hsingleton : ∀ k, ν {k} = weight k) (n : ℕ) (a : α) :
    (Measure.pi (fun _ : Fin n => ν))
        (survivingPartialTransitionHistories next n a : Set (Fin n → ξ)) =
      partialTransitionHistoryWeight weight next n a := by
  rw [← MeasureTheory.sum_measure_singleton]
  simp_rw [Measure.pi_singleton, hsingleton]
  simp only [partialTransitionHistoryWeight,
    survivingPartialTransitionHistories, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro history _
  by_cases h : (runPartialTransitions next n a history).isSome <;> simp [h]

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
