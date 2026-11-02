/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Window.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable windows for finite increment paths

## Public declarations

- `ProbabilityTheory.RandomWalk.measurableSet_inWindows`: if each coordinate window is measurable, then
  `{path | ∀ k, path k ∈ window k}` is measurable.
- `ProbabilityTheory.RandomWalk.measurableSet_inClosedInterval` and
  `ProbabilityTheory.RandomWalk.measurableSet_finiteInClosedInterval`: the infinite increment-path event
  and the finite-vector event that every partial sum from `initial` belongs
  to $[lower, upper]$ are measurable.
-/

open MeasureTheory

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

end ProbabilityTheory.RandomWalk
