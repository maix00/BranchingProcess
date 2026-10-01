module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.Linarith

/-!
# A corridor reached by one jump

This deterministic estimate is useful for finite-variation jump processes.
The small-jump path can have infinitely many jumps; only its total uniform
error enters the estimate.
-/

@[expose] public section

namespace ProbabilityTheory

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

end ProbabilityTheory

end
