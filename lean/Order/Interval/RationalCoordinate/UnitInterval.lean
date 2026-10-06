/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Interval.Set.Basic

/-!
# Rational coordinates in the unit interval

The rational subtype used for coordinates in `[0, 1]`. It is independent of
finite-grid constructions and can be shared by order and topology adapters.
-/

@[expose] public section

namespace RationalCoordinate

/-- Rational coordinates in the unit interval `[0, 1]`. -/
abbrev UnitInterval := Set.Icc (0 : ℚ) 1

end RationalCoordinate
