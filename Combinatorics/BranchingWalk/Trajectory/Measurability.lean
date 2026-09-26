import Combinatorics.BranchingWalk.Trajectory.Basic
import Combinatorics.BranchingWalk.Cloud.Measurability
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of space-time trajectories

The σ-algebra on `Trajectory Time X` is induced by the pair of vertex and edge
images.  The projection back to the vertex cloud is measurable.
-/

namespace Combinatorics

namespace Branching

namespace Trajectory

variable {Time X : Type*}

/-- The coordinate σ-algebra on trajectories. -/
instance instMeasurableSpace : MeasurableSpace (Trajectory Time X) :=
  MeasurableSpace.comap
    (fun T : Trajectory Time X => (T.vertices, T.edges)) inferInstance

theorem measurable_vertices :
    Measurable (fun T : Trajectory Time X => T.vertices) :=
  measurable_fst.comp (Measurable.of_comap_le le_rfl)

theorem measurable_edges :
    Measurable (fun T : Trajectory Time X => T.edges) :=
  measurable_snd.comp (Measurable.of_comap_le le_rfl)

theorem measurable_toCloud :
    Measurable (fun T : Trajectory Time X => T.toCloud) := by
  have hpoints : Measurable
      (fun T : Trajectory Time X => (T.toCloud).points) := by
    rw [measurable_pi_iff]
    intro t
    have hslice : Measurable
        (fun S : Set (Time × X) => {x : X | (t, x) ∈ S}) := by
      rw [measurable_set_iff]
      intro x
      change Measurable (fun S : Set (Time × X) => (t, x) ∈ S)
      exact measurableSet_setOfPred.mp (measurableSet_mem (t, x))
    exact hslice.comp measurable_vertices
  exact (measurable_iff_comap_le).2 (by
    rw [Cloud.instMeasurableSpace, MeasurableSpace.comap_comp]
    exact hpoints.comap_le)

end Trajectory

end Branching

end Combinatorics
