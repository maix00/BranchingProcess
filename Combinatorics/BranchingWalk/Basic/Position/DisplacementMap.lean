/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Position.Displace
public import Combinatorics.BranchingWalk.Basic.Map
public import Combinatorics.BranchingWalk.Step.Map
public import Combinatorics.BranchingWalk.StepField
public import Combinatorics.BranchingWalk.Step.Potential

/-!
# Separating child marks from accumulated positions

A step field carries marks in `X`. A map `d : X → Y` interprets each present
mark as an increment in an additive position space `Y`. Thus `X` itself need
not have any algebraic structure. The existing same-space displacement is the
special case `Y = X`, `d = id`.

The public API defines `displaceWith d β v p` by mapping marks before applying
`displace`, with the corresponding nil and cons equations. Its partial form
`displaceWith?` is `some (displaceWith d β v p)` exactly when
`surviveAlong β v p`, and is `none` exactly when that path is absent.
`displaceWith_id` recovers the same-space definition. For an additive
potential `φ`, `AdditivePotential.map_displace` and
`AdditivePotential.map_displaceWith` state
`φ (displace β v p) = displaceWith φ β v p` and
`φ (displaceWith d β v p) = displaceWith (φ ∘ d) β v p`.

The public declarations are `Combinatorics.Branching.displaceWith`,
`Combinatorics.Branching.displaceWith_nil`,
`Combinatorics.Branching.displaceWith_cons`,
`Combinatorics.Branching.displaceWith?`,
`Combinatorics.Branching.displaceWith?_eq_some_iff`,
`Combinatorics.Branching.displaceWith?_eq_none_iff`,
`Combinatorics.Branching.displaceWith_id`,
`Combinatorics.Branching.AdditivePotential.map_displace`, and
`Combinatorics.Branching.AdditivePotential.map_displaceWith`. Their defining
relations include
`displaceWith d β v (i :: p) = value' ((β v).map d) i +
displaceWith d β (v ++ [i]) p`, the equivalences between the partial result
and `surviveAlong β v p`, and the two potential identities stated above.
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
        Step.value'_map φ.toAddMonoidHom φ.map_zero, ih]

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
