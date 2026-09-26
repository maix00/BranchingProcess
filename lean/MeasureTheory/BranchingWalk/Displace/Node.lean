import MeasureTheory.BranchingWalk.Step.Measurability
import MeasureTheory.UlamHarris.Basic
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# The realized-child predicate

`childRealized i` is the set of branching steps in which the child slot `i` is
present: the `Set`-valued reading of `present` at slot `i`. The point-process
layer uses it to speak about one child of a step, and its measurability is
exactly `present_measurableSet`.

The displacement of an address and the realized-address predicate live in
`Displace/Basic.lean` and `Tree/Realization.lean`. Both are defined for an
arbitrary label type, so this file carries no second, `ℕ`-specialized copy of
them.
-/

open MeasureTheory

namespace MeasureTheory

namespace BranchingWalk

open MeasureTheory.UlamHarris



/-- Every child slot follows its presence flag; in particular slot zero may
be absent and the child point process may be empty. -/
def childRealized {X : Type*} (i : ℕ) : Set (NatStep X) :=
  {ξ | present ξ i}

theorem childRealized_measurable {X : Type*} [MeasurableSpace X] (i : ℕ) :
    MeasurableSet (childRealized (X := X) i) :=
  present_measurableSet i

end BranchingWalk

end MeasureTheory
