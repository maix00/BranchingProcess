/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Window.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable windows for finite increment paths
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk

theorem measurableSet_inWindows {E : Type*} [MeasurableSpace E] {n : ℕ}
    (window : Fin (n + 1) → Set E)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    MeasurableSet {path : Fin (n + 1) → E | InWindows window path} := by
  rw [show {path : Fin (n + 1) → E | InWindows window path} =
      ⋂ k, {path | path k ∈ window k} by
    ext path
    simp [InWindows]]
  exact MeasurableSet.iInter fun k =>
    (hwindow k).preimage (measurable_pi_apply k)

theorem measurableSet_inClosedInterval
    (lower upper : ℝ) (n : ℕ) (initial : ℝ) :
    MeasurableSet {increment : ℕ → ℝ |
      InClosedInterval lower upper n initial increment} := by
  exact (measurableSet_inWindows
    (fun _ : Fin (n + 1) => Set.Icc lower upper)
    (fun _ => measurableSet_Icc)).preimage (history_measurable n initial)

theorem measurableSet_finiteInClosedInterval
    (lower upper initial : ℝ) (n : ℕ) :
    MeasurableSet {increment : Fin n → ℝ |
      FiniteInClosedInterval lower upper initial increment} := by
  rw [show {increment : Fin n → ℝ |
        FiniteInClosedInterval lower upper initial increment} =
      ⋂ k : Fin (n + 1), {increment | initial +
        ∑ j : Fin k, increment
          ⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩ ∈
            Set.Icc lower upper} by
    ext increment
    simp [FiniteInClosedInterval]]
  exact MeasurableSet.iInter fun k => measurableSet_Icc.preimage
    (measurable_const.add <| Finset.measurable_sum Finset.univ fun j _ =>
      measurable_pi_apply
        (⟨j, lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ k.isLt)⟩ : Fin n))

/-- Indicator of a finite path-window event. -/
noncomputable def windowTest {E : Type*} {n : ℕ}
    (window : Fin (n + 1) → Set E) :
    (Fin (n + 1) → E) → ENNReal :=
  {path | InWindows window path}.indicator fun _ => 1

theorem windowTest_measurable {E : Type*} [MeasurableSpace E] {n : ℕ}
    (window : Fin (n + 1) → Set E)
    (hwindow : ∀ k, MeasurableSet (window k)) :
    Measurable (windowTest window) :=
  measurable_const.indicator (measurableSet_inWindows window hwindow)

@[simp] theorem windowTest_eq_one_iff {E : Type*} {n : ℕ}
    (window : Fin (n + 1) → Set E) (path : Fin (n + 1) → E) :
    windowTest window path = 1 ↔ InWindows window path := by
  simp [windowTest]

@[simp] theorem windowTest_eq_zero_iff {E : Type*} {n : ℕ}
    (window : Fin (n + 1) → Set E) (path : Fin (n + 1) → E) :
    windowTest window path = 0 ↔ ¬InWindows window path := by
  simp [windowTest]

end ProbabilityTheory.RandomWalk
