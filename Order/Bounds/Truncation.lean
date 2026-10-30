/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Order.Defs.LinearOrder

/-!
# Truncation bounds for finite families in ordered additive groups

For a linearly ordered additive group G with monotone addition, these estimates
split an event contribution into its tail above a cutoff and a bounded term.
For $x\in G$, write $\mathbf 1_E x$ for $x$ when $E$ holds and $0$ otherwise.
Thus, for $0\leq K$,
\[
  \mathbf 1_E|x|
  \leq \mathbf 1_{\{K<|x|\}}|x|+\mathbf 1_E K.
\]
In the finite-family estimate, the cardinality term
$|A|\,K$ denotes the natural multiple of $K$ by the finite cardinality $|A|$.

## Public declarations

- `abs_on_event_le_truncatedTail_add` states
  $\mathbf 1_E|x|\leq \mathbf 1_{\{K<|x|\}}|x|+\mathbf 1_E K$ for $0\leq K$.
- `sum_abs_on_event_le_truncatedTail_add` sums the pointwise estimate over a
  finite labelled family.
- `sum_abs_on_event_le_truncatedTail_add_card` writes the bounded part as the
  number of exceptional indices:
  $\sum_{i\in s}\mathbf 1_{E_i}|x_i|\leq
  \sum_{i\in s}\mathbf 1_{\{K<|x_i|\}}|x_i|+
  |\{i\in s:E_i\}|\,K$.
-/

open scoped BigOperators

@[expose] public section

namespace Order.Bounds

/-- On an event, an absolute value is bounded by its part above a cutoff plus
the cutoff itself. -/
theorem abs_on_event_le_truncatedTail_add
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (x K : G) (event : Prop) [Decidable event] (hK : 0 ≤ K) :
    (if event then |x| else 0) ≤
      (if K < |x| then |x| else 0) + (if event then K else 0) := by
  classical
  by_cases he : event
  · simp only [ite_eq_left he]
    by_cases hx : K < |x|
    · simp only [ite_eq_left hx]
      exact le_add_of_nonneg_right hK
    · simp only [ite_eq_right hx, zero_add]
      exact le_of_not_gt hx
  · simp only [ite_eq_right he]
    by_cases hx : K < |x|
    · simp only [ite_eq_left hx, add_zero]
      exact abs_nonneg _
    · simp only [ite_eq_right hx, add_zero]
      exact le_rfl

/-- The pointwise truncation estimate summed over a finite labelled family. -/
theorem sum_abs_on_event_le_truncatedTail_add
    {ι : Type*} {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (s : Finset ι) (x : ι → G) (event : ι → Prop)
    [DecidablePred event] (K : G) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => (if K < |x i| then |x i| else 0) +
        (if event i then K else 0)) := by
  exact Finset.sum_le_sum fun i hi => abs_on_event_le_truncatedTail_add
    (x i) K (event i) hK

/-- The finite-family truncation estimate with the event contribution written
as the number of exceptional indices. -/
theorem sum_abs_on_event_le_truncatedTail_add_card
    {ι : Type*} {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (s : Finset ι) (x : ι → G) (event : ι → Prop)
    [DecidablePred event] (K : G) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => if K < |x i| then |x i| else 0) +
        (s.filter event).card • K := by
  calc
    s.sum (fun i => if event i then |x i| else 0) ≤
        s.sum (fun i => (if K < |x i| then |x i| else 0) +
          (if event i then K else 0)) :=
      sum_abs_on_event_le_truncatedTail_add s x event K hK
    _ = s.sum (fun i => if K < |x i| then |x i| else 0) +
          (s.filter event).card • K := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp [Finset.sum_ite, Finset.sum_const]

end Order.Bounds

end
