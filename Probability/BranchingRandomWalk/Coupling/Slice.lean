/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Coupling.Basic
public import Combinatorics.BranchingWalk.Cloud.Order.SliceDominatingMap

/-!
# Slice domination carried by a coupling

This file connects the measure-level notion of coupling to a pathwise
order-dominating map between cloud slices.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics Combinatorics.Branching

variable {X Y Time Root α Position Value : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Preorder Value]

/-- Almost every paired realization of the coupling admits an
order-dominating map between the indicated cloud slices. -/
def Coupling.SliceDominates {μ : Measure X} {ν : Measure Y}
    (κ : ProbabilityTheory.Coupling μ ν)
    (φ : Position → Value)
    (source : X → Cloud Time Root α Position)
    (target : Y → Cloud Time Root α Position)
    (t : Time) : Prop :=
  κ.AESatisfies fun x y =>
    Nonempty (Cloud.SliceDominatingMap φ (source x) (target y) t)

end ProbabilityTheory.BranchingRandomWalk
