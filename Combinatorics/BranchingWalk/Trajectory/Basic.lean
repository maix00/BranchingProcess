module

public import Combinatorics.BranchingWalk.Cloud.Basic

/-!
# Space-time trajectories

A `Trajectory Time X` records the vertex and edge images of a walk in
space-time.  Edges are stored as their point images; segment identity is not
part of this structure.
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
