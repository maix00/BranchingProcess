/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.Linarith

/-!
# Deterministic one-jump corridor estimate

This estimate controls a path with one jump when its background path has a
uniform bound. The time parameter needs only a decidable relation `≤` and a
greatest element; the estimate uses real arithmetic for path values.

## Public declarations

- `oneJump_staysInInterval_and_endsNear` states that a background path bounded
  by $\rho$, with a jump within $\rho$ of a target in a margin-$m$ interval,
  stays in the interval shrunk by $2\rho$ and ends within $\varepsilon$ of
  the target when $2\rho<\varepsilon$.
-/

@[expose] public section

namespace Order.Bounds

/-- A uniformly small background path plus one well-placed jump stays in a
shrunk interval and ends near the target. -/
theorem oneJump_staysInInterval_and_endsNear
    {T : Type*} [LE T] [DecidableLE T] [OrderTop T]
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
