/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Basic

/-!
# Space-time trajectories

A `Trajectory Time X` records the time-indexed cloud of vertex images and the
space-time set of edge images of a walk. Edges are stored as their point
images; segment identity is not part of this structure.

## Public declarations

* `Combinatorics.Branching.Trajectory Time X` stores a vertex cloud
  `CloudSet Time X` and an edge-image set in `Time × X`; the projections are
  `Trajectory.vertexCloud` and `Trajectory.edges`.
* `Combinatorics.Branching.Trajectory.carrier T` is the union of
  `T.vertexCloud.vertexSet` and `T.edges`.
* `Combinatorics.Branching.Trajectory.ext` proves equality from equality of
  the vertex clouds and edge-image sets.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

/-- The time-indexed vertex cloud and space-time edge image of a walk. -/
structure Trajectory (Time X : Type*) where
  vertexCloud : CloudSet Time X
  edges : Set (Time × X)

namespace Trajectory

variable {Time X : Type*}

/-- The union of the vertex and edge images. -/
def carrier (T : Trajectory Time X) : Set (Time × X) :=
  T.vertexCloud.vertexSet ∪ T.edges

@[ext] theorem ext {T S : Trajectory Time X}
    (hvertices : T.vertexCloud = S.vertexCloud)
    (hedges : T.edges = S.edges) : T = S := by
  cases T
  cases S
  cases hvertices
  cases hedges
  rfl

end Trajectory

end Branching

end Combinatorics
