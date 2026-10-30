/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Core
public import Probability.BranchingRandomWalk.Coupling.Rank.Block.Basic

/-!
# Recursive rank-matching primitives

Source and fallback projections and the fresh-coordinate map for one
generation. These construction interfaces are shared by the measurability
and product-law layers.

## Public declarations

* `RootIndexed.StepField.left` and `RootIndexed.StepField.right` are the
  projections `f(inl r, u)` and `f(inr r, u)` from a two-copy field.
* `RootIndexed.rankInstalledBlockChoice` forms the generation-`n` coordinate
  map by applying `rankBlockChoice` to source and target candidates evaluated
  on the preceding installed field `F_n`.
The one-use expansion of a recursive successor as a coordinate gluing is
internal proof support under `Lemmas/RecursiveStep.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- The source (left) copy of a joint product field. -/
def RootIndexed.StepField.left
    {Root α X : Type*}
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  field.reindex Sum.inl

/-- The fallback (right) copy of a joint product field. -/
def RootIndexed.StepField.right
    {Root α X : Type*}
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  field.reindex Sum.inr

/-- The complete fresh-coordinate map used at one recursive matching stage. -/
noncomputable def RootIndexed.rankInstalledBlockChoice
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) :
    RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Generation Root α n × TreeNode α →
        (Root ⊕ Root) × TreeNode α :=
  let prior := RootIndexed.rankInstalledField sourceValue targetValue source target
    RootIndexed.StepField.left RootIndexed.StepField.right n
  RootIndexed.rankBlockChoice n
    (sourceValue n) (fun field => targetValue n field (prior field))
    (source n) (fun field => target n field (prior field))


end ProbabilityTheory.BranchingRandomWalk.Coupling
