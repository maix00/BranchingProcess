import Combinatorics.BranchingWalk.Basic.Position

/-!
# Walks as one-branch branching walks

A walk is the child-slot singleton specialization of a branching walk.  The
only address in generation `n` is `lineNode n`, and an increment sequence
therefore determines the whole step field without an arbitrary slot choice.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris
open scoped BigOperators

/-- A walk is a branching walk whose child-slot type is a singleton. -/
abbrev Walk (Mark Position : Type*) := BranchingWalk PUnit Mark Position

namespace Walk

/-- The unique address in generation `n` of a one-branch tree. -/
def lineNode (n : ℕ) : TreeNode PUnit := List.replicate n PUnit.unit

@[simp] theorem lineNode_length (n : ℕ) : (lineNode n).length = n := by
  simp [lineNode]

@[simp] theorem lineNode_zero : lineNode 0 = [] := rfl

theorem lineNode_succ (n : ℕ) :
    lineNode (n + 1) = lineNode n ++ [PUnit.unit] := by
  simpa [lineNode] using List.replicate_add n 1 PUnit.unit

/-- Every singleton-labelled address is the canonical address of its length. -/
theorem eq_lineNode_length (u : TreeNode PUnit) : u = lineNode u.length := by
  induction u with
  | nil => rfl
  | cons i u ih =>
      cases i
      simp only [List.length_cons, lineNode, List.replicate_succ]
      exact congrArg (List.cons PUnit.unit) ih

variable {Mark Position : Type*}

/-- The everywhere-present singleton step carrying `x`. -/
def singletonStep (x : Mark) : Step PUnit Mark := fun _ => some x

@[simp] theorem singletonStep_apply (x : Mark) (i : PUnit) :
    singletonStep x i = some x := rfl

/-- The one-branch step field encoded by a sequence of increments. -/
def stepFieldOfIncrements (increment : ℕ → Mark) : StepField PUnit Mark :=
  fun u => singletonStep (increment u.length)

@[simp] theorem stepFieldOfIncrements_apply
    (increment : ℕ → Mark) (u : TreeNode PUnit) (i : PUnit) :
    stepFieldOfIncrements increment u i = some (increment u.length) := rfl

@[simp] theorem surviveAlong_stepFieldOfIncrements
    (increment : ℕ → Mark) (v p : TreeNode PUnit) :
    surviveAlong (stepFieldOfIncrements increment) v p := by
  induction p generalizing v with
  | nil => exact surviveAlong_nil _ _
  | cons i p ih =>
      exact ⟨by simp [survive], ih (v ++ [i])⟩

/-- Build a walk from its initial position and increment sequence. -/
def ofIncrements (initial : Position) (increment : ℕ → Mark) :
    Walk Mark Position where
  step _ := stepFieldOfIncrements increment
  initial _ := initial
  parentClosed _ := isParentClosed_of_surviveAlong_prefix _

@[simp] theorem ofIncrements_step
    (initial : Position) (increment : ℕ → Mark) (u : TreeNode PUnit)
    (i : PUnit) :
    (ofIncrements initial increment).step PUnit.unit u i =
      some (increment u.length) := rfl

@[simp] theorem ofIncrements_initial
    (initial : Position) (increment : ℕ → Mark) :
    (ofIncrements initial increment).initial PUnit.unit = initial := rfl

/-- Reading the unique edge in each generation recovers the increment
sequence.  This is total on arbitrary walks by retaining possible absence. -/
def increments (walk : Walk Mark Position) : ℕ → Option Mark :=
  fun n => walk.step PUnit.unit (lineNode n) PUnit.unit

@[simp] theorem increments_ofIncrements
    (initial : Position) (increment : ℕ → Mark) :
    increments (ofIncrements initial increment) = some ∘ increment := by
  funext n
  simp [increments]

/-- The displacement along the unique `n`-edge path is the sum of the first
`n` mapped increments. -/
theorem displaceWith_lineNode [AddCommMonoid Position]
    (d : Mark → Position) (increment : ℕ → Mark) (n : ℕ) :
    displaceWith d (stepFieldOfIncrements increment) [] (lineNode n) =
      ∑ k ∈ Finset.range n, d (increment k) := by
  induction n with
  | zero => simp [lineNode]
  | succ n ih =>
      rw [lineNode_succ, show n + 1 = Nat.succ n by omega]
      rw [show lineNode n ++ [PUnit.unit] =
          lineNode n ++ [PUnit.unit] by rfl]
      change displace ((stepFieldOfIncrements increment).map d) []
          (lineNode n ++ [PUnit.unit]) = _
      rw [displace_append]
      change displaceWith d (stepFieldOfIncrements increment) [] (lineNode n) +
          displaceWith d (stepFieldOfIncrements increment) (lineNode n)
            [PUnit.unit] = _
      rw [ih]
      change (∑ k ∈ Finset.range n, d (increment k)) +
          (d (increment (lineNode n).length) + 0) = _
      simp [Finset.sum_range_succ]

/-- The unique generation-`n` position of a walk constructed from increments
is its initial position plus the first `n` mapped increments. -/
theorem position_lineNode [AddCommMonoid Position]
    (d : Mark → Position) (initial : Position)
    (increment : ℕ → Mark) (n : ℕ) :
    (ofIncrements initial increment).position d PUnit.unit (lineNode n) =
      initial + ∑ k ∈ Finset.range n, d (increment k) := by
  change initial + displaceWith d (stepFieldOfIncrements increment) []
      (lineNode n) = _
  rw [displaceWith_lineNode]

end Walk

end Combinatorics.Branching
