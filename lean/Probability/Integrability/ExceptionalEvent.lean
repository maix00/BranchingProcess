module

public import Order.Bounds.Truncation
public import Probability.Independence.Integration

/-!
# Exceptional-event estimates

This compatibility module keeps the original probability-layer names for
deterministic truncation bounds. Independent-event integral identities are
owned by `Probability.Independence.Integration`.
-/

@[expose] public section

namespace ProbabilityTheory

/-- Compatibility name for `Order.Bounds.abs_on_event_le_truncatedTail_add`. -/
@[deprecated Order.Bounds.abs_on_event_le_truncatedTail_add (since := "2026-10-03")]
theorem bad_event_truncation (x K : ℝ) (event : Prop) [Decidable event] (hK : 0 ≤ K) :
    (if event then |x| else 0) ≤
      (if K < |x| then |x| else 0) + K * (if event then 1 else 0) :=
  Order.Bounds.abs_on_event_le_truncatedTail_add x K event hK

/-- Compatibility name for
`Order.Bounds.sum_abs_on_event_le_truncatedTail_add`. -/
@[deprecated Order.Bounds.sum_abs_on_event_le_truncatedTail_add (since := "2026-10-03")]
theorem bad_event_truncation_sum {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (event : ι → Prop) [DecidablePred event]
    (K : ℝ) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => (if K < |x i| then |x i| else 0) +
        K * (if event i then 1 else 0)) :=
  Order.Bounds.sum_abs_on_event_le_truncatedTail_add s x event K hK

/-- Compatibility name for
`Order.Bounds.sum_abs_on_event_le_truncatedTail_add_card`. -/
@[deprecated Order.Bounds.sum_abs_on_event_le_truncatedTail_add_card
  (since := "2026-10-03")]
theorem bad_event_truncation_sum_card {ι : Type*} (s : Finset ι)
    (x : ι → ℝ) (event : ι → Prop) [DecidablePred event]
    (K : ℝ) (hK : 0 ≤ K) :
    s.sum (fun i => if event i then |x i| else 0) ≤
      s.sum (fun i => if K < |x i| then |x i| else 0) +
        K * (s.filter event).card :=
  Order.Bounds.sum_abs_on_event_le_truncatedTail_add_card s x event K hK

end ProbabilityTheory

end
