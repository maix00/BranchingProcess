/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval

/-!
# Linear continuous paths on the unit interval

## Public declarations

- `ContinuousMap.linearPath`: the continuous path $t\mapsto at$ on
  $[0,1]$ with slope $a$.
- `ContinuousMap.linearPath_apply`: its pointwise value is $at$.
-/

@[expose] public section

namespace ContinuousMap

/-- The continuous linear path with the given slope on the unit interval. -/
def linearPath (slope : ℝ) : C(unitInterval, ℝ) :=
  ⟨fun t => slope * (t : ℝ), continuous_const.mul continuous_subtype_val⟩

@[simp]
theorem linearPath_apply (slope : ℝ) (t : unitInterval) :
    linearPath slope t = slope * (t : ℝ) := rfl

end ContinuousMap

end
