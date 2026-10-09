/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Boundary
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Measurability of finite-step corridor boundaries

The finite-step boundary and its traces are defined in the deterministic
Skorokhod layer. This file proves that their level indices and evaluations are
measurable, keeping measure-theoretic facts out of the topological definition.
-/

open MeasureTheory Set
open scoped Topology

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor.StepBoundary

private theorem card_filter_eq_sum {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.filter_insert]
    by_cases hp : p a
    · rw [ite_eq_left hp, Finset.card_insert_of_notMem]
      · rw [Finset.sum_insert ha, ih]
        simp [hp, Nat.add_comm]
      · intro h
        exact ha (Finset.mem_filter.mp h).1
    · rw [ite_eq_right hp, Finset.sum_insert ha, ih]
      simp [hp]

private theorem card_le_measurable (b : Skorokhod.PathClass.StepCorridor.StepBoundary) :
    Measurable (fun t : unitInterval => (b.knots.filter (fun s => s ≤ t)).card) := by
  have hsum : Measurable (fun t : unitInterval =>
      ∑ q ∈ b.knots, if q ≤ t then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro q hq
    exact Measurable.ite (measurableSet_Ici : MeasurableSet (Set.Ici q))
      measurable_const measurable_const
  have hEq : (fun t : unitInterval => (b.knots.filter (fun s => s ≤ t)).card) =
      fun t => ∑ q ∈ b.knots, if q ≤ t then (1 : ℕ) else 0 := by
    funext t
    exact card_filter_eq_sum b.knots (fun s => s ≤ t)
  rw [hEq]
  exact hsum

private theorem card_lt_measurable (b : Skorokhod.PathClass.StepCorridor.StepBoundary) :
    Measurable (fun t : unitInterval => (b.knots.filter (fun s => s < t)).card) := by
  have hsum : Measurable (fun t : unitInterval =>
      ∑ q ∈ b.knots, if q < t then (1 : ℕ) else 0) := by
    apply Finset.measurable_sum
    intro q hq
    exact Measurable.ite (measurableSet_Ioi : MeasurableSet (Set.Ioi q))
      measurable_const measurable_const
  have hEq : (fun t : unitInterval => (b.knots.filter (fun s => s < t)).card) =
      fun t => ∑ q ∈ b.knots, if q < t then (1 : ℕ) else 0 := by
    funext t
    exact card_filter_eq_sum b.knots (fun s => s < t)
  rw [hEq]
  exact hsum

/-- The right-continuous level index of a finite-step boundary is measurable.
This follows by expressing the number of knots already reached as a finite
sum of measurable indicators. -/
theorem levelIndex_measurable (b : Skorokhod.PathClass.StepCorridor.StepBoundary) :
    Measurable b.levelIndex := by
  have hbound (t : unitInterval) :
      (b.knots.filter (fun s => s ≤ t)).card < b.knots.card + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))
  let f : unitInterval → {n : ℕ // n < b.knots.card + 1} :=
    fun t => ⟨(b.knots.filter (fun s => s ≤ t)).card, hbound t⟩
  have hf : Measurable f := by
    unfold f
    exact (card_le_measurable b).subtype_mk
      (p := fun n : ℕ => n < b.knots.card + 1) (h := hbound)
  have hEq : b.levelIndex = Fin.equivSubtype.symm ∘ f := by
    funext t
    apply Fin.ext
    rfl
  rw [hEq]
  exact (measurable_of_finite Fin.equivSubtype.symm).comp hf

/-- The left-trace level index of a finite-step boundary is measurable. -/
theorem leftLevelIndex_measurable (b : Skorokhod.PathClass.StepCorridor.StepBoundary) :
    Measurable b.leftLevelIndex := by
  have hbound (t : unitInterval) :
      (b.knots.filter (fun s => s < t)).card < b.knots.card + 1 :=
    Nat.lt_succ_of_le (Finset.card_le_card (Finset.filter_subset _ _))
  let f : unitInterval → {n : ℕ // n < b.knots.card + 1} :=
    fun t => ⟨(b.knots.filter (fun s => s < t)).card, hbound t⟩
  have hf : Measurable f := by
    unfold f
    exact (card_lt_measurable b).subtype_mk
      (p := fun n : ℕ => n < b.knots.card + 1) (h := hbound)
  have hraw : Measurable (fun t : unitInterval => Fin.equivSubtype.symm (f t)) :=
    (measurable_of_finite Fin.equivSubtype.symm).comp hf
  have hset : MeasurableSet {t : unitInterval | t = ⊥} := measurableSet_singleton ⊥
  unfold Skorokhod.PathClass.StepCorridor.StepBoundary.leftLevelIndex
  exact Measurable.ite hset (levelIndex_measurable b) hraw

/-- Evaluation of a finite-step boundary is measurable. -/
theorem eval_measurable (b : Skorokhod.PathClass.StepCorridor.StepBoundary) :
    Measurable b.eval := by
  exact (measurable_of_finite b.levels).comp b.levelIndex_measurable

/-- The totalized left-trace function of a finite-step boundary is measurable. -/
theorem leftTrace_measurable (b : Skorokhod.PathClass.StepCorridor.StepBoundary) :
    Measurable b.leftTrace := by
  exact (measurable_of_finite b.levels).comp b.leftLevelIndex_measurable

end Skorokhod.PathClass.StepCorridor.StepBoundary
