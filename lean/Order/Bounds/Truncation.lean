module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Truncation bounds for real-valued finite families

These deterministic estimates split a contribution on an event into a tail
above a cutoff and a bounded contribution proportional to the event.
-/

open scoped BigOperators

@[expose] public section

namespace Order.Bounds

/-- On an event, an absolute value is bounded by its part above a cutoff plus
the cutoff itself. -/
theorem abs_on_event_le_truncatedTail_add
    (x K : ℝ) (event : Prop) [Decidable event] (hK : 0 ≤ K) :
    (if event then |x| else 0) ≤
      (if K < |x| then |x| else 0) + K * (if event then 1 else 0) := by
  classical
  by_cases he : event
  · simp only [ite_eq_left he, mul_one]
    by_cases hx : K < |x|
    · simp only [ite_eq_left hx]
      linarith
    · simp only [ite_eq_right hx]
      simpa using (le_of_not_gt hx)
  · simp only [ite_eq_right he, mul_zero, add_zero]
    split_ifs <;> positivity

/-- The pointwise truncation estimate summed over a finite labelled family. -/
theorem sum_abs_on_event_le_truncatedTail_add
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) (event : ι → Prop)
    [DecidablePred event] (K : ℝ) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => (if K < |x i| then |x i| else 0) +
        K * (if event i then 1 else 0)) := by
  exact Finset.sum_le_sum fun i hi => abs_on_event_le_truncatedTail_add
    (x i) K (event i) hK

/-- The finite-family truncation estimate with the event contribution written
as the number of exceptional indices. -/
theorem sum_abs_on_event_le_truncatedTail_add_card
    {ι : Type*} (s : Finset ι) (x : ι → ℝ) (event : ι → Prop)
    [DecidablePred event] (K : ℝ) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => if K < |x i| then |x i| else 0) +
        K * (s.filter event).card := by
  calc
    s.sum (fun i => if event i then |x i| else 0) ≤
        s.sum (fun i => (if K < |x i| then |x i| else 0) +
          K * (if event i then 1 else 0)) :=
      sum_abs_on_event_le_truncatedTail_add s x event K hK
    _ = s.sum (fun i => if K < |x i| then |x i| else 0) +
          K * (s.filter event).card := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [← Finset.mul_sum]
      congr 1
      simp [Finset.sum_boole]

end Order.Bounds

end
