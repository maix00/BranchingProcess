/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Basic.Position.Basic
public import Combinatorics.BranchingWalk.Cloud.Basic

/-!
# Finite populations as particle clouds

This constructs a particle cloud from a finite labelled population in a
root-indexed branching walk.  The construction is independent of the rule used
to choose that population.
-/

@[expose] public section

namespace Combinatorics.Branching.Selection.Coupling

open Combinatorics.UlamHarris

variable {Root α Mark Position : Type*}

/-- A finite labelled population presented as a constant-time cloud with the
position function of a root-indexed branching walk. -/
def populationCloud [AddCommMonoid Position]
    (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (population : Finset (RootIndexed.TreeNode Root α)) :
    Cloud Unit Root α Position where
  particles _ := ↑population
  position := β.position d

@[simp] theorem populationCloud_particles [AddCommMonoid Position]
    (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (population : Finset (RootIndexed.TreeNode Root α)) (t : Unit) :
    (populationCloud d β population).particles t = ↑population :=
  rfl

@[simp] theorem populationCloud_position [AddCommMonoid Position]
    (d : Mark → Position)
    (β : RootIndexed.BranchingWalk Root α Mark Position)
    (population : Finset (RootIndexed.TreeNode Root α))
    (p : RootIndexed.TreeNode Root α) :
    (populationCloud d β population).position p.1 p.2 =
      β.position d p.1 p.2 :=
  rfl

end Combinatorics.Branching.Selection.Coupling

end
