module

public import Combinatorics.BranchingWalk.Basic.Displace
public import Combinatorics.BranchingWalk.Basic.Map
public import Combinatorics.BranchingWalk.StepField
public import Combinatorics.BranchingWalk.Step.Potential

/-!
# Separating child marks from accumulated positions

A step field carries marks in `X`. A map `d : X → Y` interprets each present
mark as an increment in an additive position space `Y`. Thus `X` itself need
not have any algebraic structure. The existing same-space displacement is the
special case `Y = X`, `d = id`.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- Accumulate mapped edge marks along a path. -/
def displaceWith {α X Y : Type*} [AddCommMonoid Y]
    (d : X → Y) (β : StepField α X) (v p : TreeNode α) : Y :=
  displace (β.map d) v p

@[simp] theorem displaceWith_nil {α X Y : Type*} [AddCommMonoid Y]
    (d : X → Y) (β : StepField α X) (v : TreeNode α) :
    displaceWith d β v [] = 0 := rfl

theorem displaceWith_cons {α X Y : Type*} [AddCommMonoid Y]
    (d : X → Y) (β : StepField α X) (v : TreeNode α)
    (i : α) (p : TreeNode α) :
    displaceWith d β v (i :: p) =
      value' ((β v).map d) i + displaceWith d β (v ++ [i]) p := rfl

/-- Partial mapped displacement; an absent edge makes the result absent. -/
def displaceWith? {α X Y : Type*} [AddCommMonoid Y]
    (d : X → Y) (β : StepField α X) (v p : TreeNode α) : Option Y :=
  displace? (β.map d) v p

theorem displaceWith?_eq_some_iff {α X Y : Type*} [AddCommMonoid Y]
    (d : X → Y) (β : StepField α X) (v p : TreeNode α) :
    displaceWith? d β v p = some (displaceWith d β v p) ↔
      surviveAlong β v p := by
  simp [displaceWith?, displaceWith, displace?_eq_some_iff,
    surviveAlong_map_iff]

theorem displaceWith?_eq_none_iff {α X Y : Type*} [AddCommMonoid Y]
    (d : X → Y) (β : StepField α X) (v p : TreeNode α) :
    displaceWith? d β v p = none ↔ ¬ surviveAlong β v p := by
  simp [displaceWith?, displace?_eq_none_iff, surviveAlong_map_iff]

@[simp] theorem displaceWith_id {α X : Type*} [AddCommMonoid X]
    (β : StepField α X) (v p : TreeNode α) :
    displaceWith id β v p = displace β v p := by
  simp [displaceWith]

/-- An additive projection commutes with zero-defaulted slot reading. -/
theorem AdditivePotential.map_value'
    {ι X : Type*} [MeasurableSpace X] [AddCommMonoid X]
    (φ : AdditivePotential X) (ξ : Step ι X) (i : ι) :
    value' (ξ.map φ) i = φ (value' ξ i) := by
  cases h : ξ i <;>
    simp [Step.map, value', h]

/-- An additive potential may be applied before or after accumulating a path. -/
theorem AdditivePotential.map_displace
    {α X : Type*} [MeasurableSpace X] [AddCommMonoid X]
    (φ : AdditivePotential X) (β : StepField α X)
    (v p : TreeNode α) :
    φ (displace β v p) = displaceWith φ β v p := by
  induction p generalizing v with
  | nil => simp [displaceWith]
  | cons i p ih =>
      rw [displace_cons, φ.map_add, displaceWith_cons,
        AdditivePotential.map_value', ih]

/-- Projecting mapped marks after path accumulation agrees with projecting
each raw mark first. This is the compatibility theorem for a mark space that
need not itself carry an addition. -/
theorem AdditivePotential.map_displaceWith
    {α Mark Position : Type*} [MeasurableSpace Position]
    [AddCommMonoid Position]
    (φ : AdditivePotential Position) (d : Mark → Position)
    (β : StepField α Mark) (v p : TreeNode α) :
    φ (displaceWith d β v p) =
      displaceWith (φ ∘ d) β v p := by
  calc
    φ (displaceWith d β v p) =
        displaceWith φ (β.map d) v p :=
      φ.map_displace (β.map d) v p
    _ = displaceWith (φ ∘ d) β v p := by
      change displace ((β.map d).map (fun x => φ x)) v p =
        displace (β.map (fun x => φ (d x))) v p
      rw [StepField.map_map]
      rfl

end Combinatorics.Branching

end
