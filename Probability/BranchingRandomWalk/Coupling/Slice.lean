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

## Public declarations

* `Coupling.SliceDominates κ φ objectsToMatchCloud availablePartnersCloud t` means that for
  `κ`-almost every paired sample `(x,y)`, there is a
  `Cloud.SliceDominatingMap φ (objectsToMatchCloud x) (availablePartnersCloud y) t`.
  Precisely,
  \[
  \kappa\text{-a.e. }(x,y),\qquad
  \operatorname{Nonempty}\bigl(\operatorname{SliceDominatingMap}
  (\varphi,\operatorname{objectsToMatchCloud}(x),\operatorname{availablePartnersCloud}(y),t)\bigr).
  \]
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
    (objectsToMatchCloud : X → Cloud Time Root α Position)
    (availablePartnersCloud : Y → Cloud Time Root α Position)
    (t : Time) : Prop :=
  κ.AESatisfies fun x y =>
    Nonempty (Cloud.SliceDominatingMap φ (objectsToMatchCloud x) (availablePartnersCloud y) t)

end ProbabilityTheory.BranchingRandomWalk
