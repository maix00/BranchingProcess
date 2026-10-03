module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith

/-!
# Deterministic one-jump corridor estimate

This estimate controls a path with one jump when its background path has a
uniform bound. It depends only on order and real arithmetic.
-/

@[expose] public section

namespace Order.Bounds

/-- A uniformly small background path plus one well-placed jump stays in a
shrunk interval and ends near the target. -/
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
      target - ε < S ⊤ + jumpSize ∧ S ⊤ + jumpSize < target + ε := by
  have hstay : ∀ t, lower + (margin - 2 * ρ) ≤
        S t + (if jumpTime ≤ t then jumpSize else 0) ∧
      S t + (if jumpTime ≤ t then jumpSize else 0) ≤
        upper - (margin - 2 * ρ) := by
    intro t
    have hs := abs_le.mp (hsmall t)
    have hw := abs_lt.mp hjump
    split_ifs <;> constructor <;> linarith
  have hs := abs_le.mp (hsmall ⊤)
  have hw := abs_lt.mp hjump
  refine ⟨hstay, ?_, ?_⟩ <;> linarith

end Order.Bounds

end
