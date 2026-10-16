/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.FiniteState.PartialStep
public import Probability.Kernel.Step.Path
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Survival of finite partial steps

A finite partial step chooses one of finitely many weighted branches.
A branch returning `none` is killed.  This file identifies the total mass of
the iterated sub-Markov kernel with the recursively accumulated weight of all
surviving branch histories.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α ξ : Type*} [Countable α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [Fintype ξ]

/-- Total weight of the branch histories that survive for `n` transitions. -/
noncomputable def partialStepSurvivalWeight
    (weight : ξ → ENNReal) (next : α → ξ → Option α) : ℕ → α → ENNReal
  | 0, _ => 1
  | n + 1, a =>
      ∑ k, weight k * (next a k).elim 0
        (partialStepSurvivalWeight weight next n)

/-- Explicit finite sum of the weights of all surviving branch histories. -/
noncomputable def partialStepHistoryWeight
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (n : ℕ) (a : α) : ENNReal :=
  ∑ history : Fin n → ξ,
    (∏ k, weight (history k)) *
      if (runPartialSteps next n a history).isSome then 1 else 0

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
@[simp]
theorem partialStepSurvivalWeight_zero
    (weight : ξ → ENNReal) (next : α → ξ → Option α) (a : α) :
    partialStepSurvivalWeight weight next 0 a = 1 := rfl

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
@[simp]
theorem partialStepSurvivalWeight_succ
    (weight : ξ → ENNReal) (next : α → ξ → Option α) (n : ℕ) (a : α) :
    partialStepSurvivalWeight weight next (n + 1) a =
      ∑ k, weight k * (next a k).elim 0
        (partialStepSurvivalWeight weight next n) := rfl

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
theorem partialStepHistoryWeight_succ
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (n : ℕ) (a : α) :
    partialStepHistoryWeight weight next (n + 1) a =
      ∑ k, weight k * (next a k).elim 0
        (partialStepHistoryWeight weight next n) := by
  rw [partialStepHistoryWeight]
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
    runPartialSteps]
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
theorem partialStepHistoryWeight_eq_survivalWeight
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (n : ℕ) (a : α) :
    partialStepHistoryWeight weight next n a =
      partialStepSurvivalWeight weight next n a := by
  induction n generalizing a with
  | zero => simp [partialStepHistoryWeight, runPartialSteps]
  | succ n ih =>
      rw [partialStepHistoryWeight_succ,
        partialStepSurvivalWeight_succ]
      apply Finset.sum_congr rfl
      intro k _
      cases next a k <;> simp [ih]

/-- The finite set of branch histories that survive all `n` partial
transitions. -/
def survivingPartialStepHistories
    (next : α → ξ → Option α) (n : ℕ) (a : α) :
    Finset (Fin n → ξ) :=
  Finset.univ.filter fun history =>
    (runPartialSteps next n a history).isSome

omit [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Under a finite product law whose singleton masses are the branch
weights, the probability of survival is the explicit history weight. -/
theorem pi_apply_survivingPartialStepHistories
    [MeasurableSpace ξ] [MeasurableSingletonClass ξ]
    (ν : Measure ξ) [IsProbabilityMeasure ν]
    (weight : ξ → ENNReal) (next : α → ξ → Option α)
    (hsingleton : ∀ k, ν {k} = weight k) (n : ℕ) (a : α) :
    (Measure.pi (fun _ : Fin n => ν))
        (survivingPartialStepHistories next n a : Set (Fin n → ξ)) =
      partialStepHistoryWeight weight next n a := by
  rw [← MeasureTheory.sum_measure_singleton]
  simp_rw [Measure.pi_singleton, hsingleton]
  simp only [partialStepHistoryWeight,
    survivingPartialStepHistories, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro history _
  by_cases h : (runPartialSteps next n a history).isSome <;> simp [h]

/-- The mass remaining after `n` kernel transitions is exactly the total
weight of all branch histories that have not been killed. -/
theorem pow_apply_univ_ofFinitePartialStep
    (weight : ξ → ENNReal) (next : α → ξ → Option α) (n : ℕ) (a : α) :
    (ofFinitePartialStep weight next ^ n) a univ =
      partialStepSurvivalWeight weight next n a := by
  induction n generalizing a with
  | zero =>
      change Kernel.id a univ = 1
      rw [Kernel.id_apply]
      simp
  | succ n ih =>
      rw [show n + 1 = 1 + n by omega,
        Kernel.pow_add_apply_eq_lintegral _ 1 n a MeasurableSet.univ]
      simp only [pow_one]
      rw [lintegral_ofFinitePartialStep]
      rw [show 1 + n = n + 1 by omega,
        partialStepSurvivalWeight_succ]
      apply Finset.sum_congr rfl
      intro k _
      cases hnext : next a k with
      | none => simp
      | some b => simp [ih b]

end ProbabilityTheory.Kernel

end
