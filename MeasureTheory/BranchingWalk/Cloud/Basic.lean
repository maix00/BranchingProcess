import Mathlib.Data.Set.Basic

/-!
# Time-indexed particle clouds

A `Cloud Time X` is a family of spatial point sets indexed by time.  It is
only the geometric image of a branching walk; the branching-step data and its
initial positions generate it in `Cloud/Step.lean`.
-/

namespace MeasureTheory

namespace BranchingWalk

/-- A time-indexed cloud of points in `X`. -/
structure Cloud (Time X : Type*) where
  points : Time → Set X

namespace Cloud

variable {Time X : Type*}

instance : Membership (Time × X) (Cloud Time X) where
  mem C p := p.2 ∈ C.points p.1

/-- The space-time set of all points of a cloud. -/
def vertexSet (C : Cloud Time X) : Set (Time × X) :=
  {p | p ∈ C}

@[simp] theorem mem_vertexSet (C : Cloud Time X) (p : Time × X) :
    p ∈ C.vertexSet ↔ p ∈ C :=
  Iff.rfl

@[ext] theorem ext {C D : Cloud Time X}
    (h : ∀ t x, x ∈ C.points t ↔ x ∈ D.points t) : C = D := by
  cases C with
  | mk Cpoints =>
    cases D with
    | mk Dpoints =>
      congr
      funext t
      ext x
      exact h t x

end Cloud

end BranchingWalk

end MeasureTheory
