module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Order.Bounds.Corridor

/-!
# Compatibility name for the deterministic one-jump corridor estimate

The order-theoretic result is owned by `Order.Bounds.Corridor`.
-/

@[expose] public section

namespace ProbabilityTheory

/-- Compatibility name for
`Order.Bounds.oneJump_staysInInterval_and_endsNear`. -/
@[deprecated Order.Bounds.oneJump_staysInInterval_and_endsNear
  (since := "2026-10-03")]
theorem oneJump_staysInInterval_and_endsNear
    {T : Type*} [LinearOrder T] [OrderTop T]
    (S : T → ℝ) (jumpTime : T) (jumpSize lower upper target ρ ε margin : ℝ)
    (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hsmall : ∀ t, |S t| ≤ ρ)
    (hjump : |jumpSize - target| < ρ) :
    (∀ t, lower + (margin - 2 * ρ) ≤
        S t + (if jumpTime ≤ t then jumpSize else 0) ∧
      S t + (if jumpTime ≤ t then jumpSize else 0) ≤
        upper - (margin - 2 * ρ)) ∧
      target - ε < S ⊤ + jumpSize ∧ S ⊤ + jumpSize < target + ε :=
  Order.Bounds.oneJump_staysInInterval_and_endsNear S jumpTime jumpSize
    lower upper target ρ ε margin hε hl0 hu0 hly huy hsmall hjump

end ProbabilityTheory

end
