import MeasureTheory.BranchingWalk.Cloud.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of time-indexed clouds

The measurable space on `Cloud Time X` is induced by the coordinate map
`C ↦ C.points`.  Thus membership of every fixed time-space point in a cloud is
a measurable event.
-/

namespace MeasureTheory

namespace BranchingWalk

namespace Cloud

variable {Time X : Type*}

/-- The coordinate σ-algebra on time-indexed clouds. -/
instance instMeasurableSpace : MeasurableSpace (Cloud Time X) :=
  MeasurableSpace.comap (fun C : Cloud Time X => C.points) inferInstance

theorem measurable_points :
    Measurable (fun C : Cloud Time X => C.points) :=
  Measurable.of_comap_le le_rfl

@[simp] theorem measurableSet_points_mem (t : Time) (x : X) :
    MeasurableSet {C : Cloud Time X | x ∈ C.points t} :=
  MeasurableSet.preimage (measurableSet_mem x)
    ((measurable_pi_apply t).comp measurable_points)

theorem measurable_vertexSet :
    Measurable (fun C : Cloud Time X => C.vertexSet) := by
  rw [measurable_set_iff]
  intro p
  rcases p with ⟨t, x⟩
  change Measurable (fun C : Cloud Time X => x ∈ C.points t)
  exact measurableSet_setOfPred.mp (measurableSet_points_mem (t := t) (x := x))

end Cloud

end BranchingWalk

end MeasureTheory
