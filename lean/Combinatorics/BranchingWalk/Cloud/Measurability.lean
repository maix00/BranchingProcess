/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of time-indexed clouds

The measurable space on `CloudSet Time X` is induced by the coordinate map
`C ↦ C.points`.  Thus membership of every fixed time-space point in a cloud is
a measurable event.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

namespace CloudSet

variable {Time X : Type*}

/-- The coordinate σ-algebra on time-indexed clouds. -/
instance instMeasurableSpace : MeasurableSpace (CloudSet Time X) :=
  MeasurableSpace.comap (fun C : CloudSet Time X => C.points) inferInstance

theorem measurable_points :
    Measurable (fun C : CloudSet Time X => C.points) :=
  Measurable.of_comap_le le_rfl

@[simp] theorem measurableSet_points_mem (t : Time) (x : X) :
    MeasurableSet {C : CloudSet Time X | x ∈ C.points t} :=
  MeasurableSet.preimage (measurableSet_mem x)
    ((measurable_pi_apply t).comp measurable_points)

theorem measurable_vertexSet :
    Measurable (fun C : CloudSet Time X => C.vertexSet) := by
  rw [measurable_set_iff]
  intro p
  rcases p with ⟨t, x⟩
  change Measurable (fun C : CloudSet Time X => x ∈ C.points t)
  exact measurableSet_setOfPred.mp (measurableSet_points_mem (t := t) (x := x))

end CloudSet

end Branching

end Combinatorics

end
