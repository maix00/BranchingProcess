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

The selected-BRW and fallback projections, together with the fresh-coordinate
map for one generation. These construction interfaces are shared by the
measurability and product-law layers.

## Public declarations

The two copies are coordinate restrictions, and the fresh block choice at
stage `n` uses ranks evaluated on the preceding installed field `F_n`:

\[\begin{aligned}
\operatorname{left}(F)(r,u)&=F(\operatorname{inl}(r),u),\\
\operatorname{right}(F)(r,u)&=F(\operatorname{inr}(r),u),\\
\operatorname{rankInstalledBlockChoice}_n(F)
&=\operatorname{rankBlockChoice}_n
  (\operatorname{selectedBRWPopulationOrderKey}_n(F),
   \operatorname{nSelectedBRWPopulationOrderKey}_n(F,F_n),
   \operatorname{selectedBRWPopulation}_n(F),\operatorname{nSelectedBRWPopulation}_n(F,F_n)).
\end{aligned}\]

* `RootIndexed.StepField.left` and `RootIndexed.StepField.right` are the
  projections `f(inl r, u)` and `f(inr r, u)` from a two-copy field.
* `RootIndexed.rankInstalledBlockChoice` forms the generation-`n` coordinate
  map by applying `rankBlockChoice` to the selected-BRW and n-selected-BRW
  populations evaluated on the preceding installed field `F_n`.
The one-use expansion of a recursive successor as a coordinate gluing is
internal proof support under `Lemmas/RecursiveStep.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- The selected-BRW (left) copy of a joint product field. -/
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
    (selectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (nSelectedBRWPopulationOrderKey : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (selectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (nSelectedBRWPopulation : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (n : ℕ) :
    RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Generation Root α n × TreeNode α →
        (Root ⊕ Root) × TreeNode α :=
  let prior := RootIndexed.rankInstalledField selectedBRWPopulationOrderKey nSelectedBRWPopulationOrderKey selectedBRWPopulation nSelectedBRWPopulation
    RootIndexed.StepField.left RootIndexed.StepField.right n
  RootIndexed.rankBlockChoice n
    (selectedBRWPopulationOrderKey n) (fun field => nSelectedBRWPopulationOrderKey n field (prior field))
    (selectedBRWPopulation n) (fun field => nSelectedBRWPopulation n field (prior field))


end ProbabilityTheory.BranchingRandomWalk.Coupling
