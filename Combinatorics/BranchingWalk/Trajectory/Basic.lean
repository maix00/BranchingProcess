/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Basic

/-!
# Space-time trajectories

A `Trajectory Time X` records the vertex and edge images of a walk in
space-time.  Edges are stored as their point images; segment identity is not
part of this structure.

## Public declarations

* `Combinatorics.Branching.Trajectory Time X` stores sets of space-time
  vertices and edge images. `Combinatorics.Branching.Trajectory.vertices` and
  `Combinatorics.Branching.Trajectory.edges` are its defining projections.
* `Combinatorics.Branching.Trajectory.carrier T` is the union of those two
  sets; `Combinatorics.Branching.Trajectory.toCloud T` takes their
  time-indexed slices of the vertex set.
* `Combinatorics.Branching.Trajectory.mem_toCloud` states
  `x ∈ T.toCloud.points t ↔ (t, x) ∈ T.vertices`.
  `Combinatorics.Branching.Trajectory.ext` proves equality from equality of
  both the vertex and edge sets.
-/

@[expose] public section

namespace Combinatorics

namespace Branching

/-- The space-time vertex and edge images of a walk. -/
structure Trajectory (Time X : Type*) where
  vertices : Set (Time × X)
  edges : Set (Time × X)

namespace Trajectory

variable {Time X : Type*}

/-- The union of the vertex and edge images. -/
def carrier (T : Trajectory Time X) : Set (Time × X) :=
  T.vertices ∪ T.edges

/-- The time-indexed cloud of the trajectory vertices. -/
def toCloud (T : Trajectory Time X) : CloudSet Time X where
  points t := {x | (t, x) ∈ T.vertices}

@[simp] theorem mem_toCloud (T : Trajectory Time X) (t : Time) (x : X) :
    x ∈ (T.toCloud).points t ↔ (t, x) ∈ T.vertices :=
  Iff.rfl

@[ext] theorem ext {T S : Trajectory Time X}
    (hvertices : T.vertices = S.vertices)
    (hedges : T.edges = S.edges) : T = S := by
  cases T
  cases S
  simp only at hvertices hedges
  subst hvertices
  subst hedges
  rfl

end Trajectory

end Branching

end Combinatorics
