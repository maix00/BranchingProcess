/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Trajectory.Basic
public import Combinatorics.BranchingWalk.Cloud.Measurability
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of space-time trajectories

## Public declarations

The trajectory σ-algebra is induced by its two coordinates, and both
coordinate maps are measurable:

\[
\mathcal{M}_{\operatorname{Trajectory}(Time,X)}
=\operatorname{comap}\!\left(T\mapsto(T.\operatorname{vertexCloud},T.\operatorname{edges}),
\mathcal{M}_{\operatorname{CloudSet}(Time,X)}\times
\mathcal{M}_{\operatorname{Set}(Time\times X)}\right).
\]
\[
T\mapsto T.\operatorname{vertexCloud}\text{ is measurable},
\qquad
T\mapsto T.\operatorname{edges}\text{ is measurable}.
\]

* `Combinatorics.Branching.Trajectory.instMeasurableSpace` equips
  `Trajectory Time X` with the σ-algebra induced by the pair of vertex and
  edge sets.
* `Combinatorics.Branching.Trajectory.measurable_vertexCloud` and
  `Combinatorics.Branching.Trajectory.measurable_edges` prove measurability of
  the two coordinate maps.
* `Combinatorics.Branching.Trajectory.measurable_vertexSet` proves that the
  space-time vertex set is measurable as a function of the trajectory.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

namespace Trajectory

variable {Time X : Type*}

/-- The coordinate σ-algebra on trajectories. -/
instance instMeasurableSpace : MeasurableSpace (Trajectory Time X) :=
  MeasurableSpace.comap
    (fun T : Trajectory Time X => (T.vertexCloud, T.edges)) inferInstance

theorem measurable_vertexCloud :
    Measurable (fun T : Trajectory Time X => T.vertexCloud) :=
  measurable_fst.comp (Measurable.of_comap_le le_rfl)

theorem measurable_edges :
    Measurable (fun T : Trajectory Time X => T.edges) :=
  measurable_snd.comp (Measurable.of_comap_le le_rfl)

theorem measurable_vertexSet :
    Measurable (fun T : Trajectory Time X => T.vertexCloud.vertexSet) :=
  CloudSet.measurable_vertexSet.comp measurable_vertexCloud

end Trajectory

end Branching

end Combinatorics
