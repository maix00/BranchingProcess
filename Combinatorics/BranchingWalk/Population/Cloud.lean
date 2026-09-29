module

public import Combinatorics.BranchingWalk.Population.Basic
public import Combinatorics.BranchingWalk.Cloud.Basic

/-!
# Spatial clouds of branching populations

A branching `Population` contains the genealogical slices and their successor
law.  Supplying a position map turns those slices into a natural-number
indexed `Cloud`.  The general `Cloud Time ...` remains a configuration view
used by slice comparison; this file identifies its discrete branching
specialization without introducing another structure.
-/

@[expose] public section

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

namespace Population

/-- Add positions to a deterministic branching population. -/
def cloud {Root α Mark Position : Type*}
    {stepField : Root → StepField α Mark}
    (P : Population stepField)
    (position : Root → TreeNode α → Position) :
    Cloud ℕ Root α Position where
  particles := P.particles
  position := position

@[simp] theorem cloud_particles {Root α Mark Position : Type*}
    {stepField : Root → StepField α Mark}
    (P : Population stepField)
    (position : Root → TreeNode α → Position) (n : ℕ) :
    (P.cloud position).particles n = P n :=
  rfl

@[simp] theorem cloud_position {Root α Mark Position : Type*}
    {stepField : Root → StepField α Mark}
    (P : Population stepField)
    (position : Root → TreeNode α → Position) (r : Root) (u : TreeNode α) :
    (P.cloud position).position r u = position r u :=
  rfl

end Population

end Combinatorics.Branching
