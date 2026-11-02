/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Coupling.Rank.Field
public import Probability.BranchingRandomWalk.Coupling.Field.Law
public import Probability.BranchingRandomWalk.Coupling.Field.Adaptive
public import Probability.BranchingRandomWalk.Step.Field.Update

/-!
# One-generation rank choice

This layer builds the guarded equal-rank inverse and the injective choice of a
source root for each target generation address.

## Public declarations

The rank choice uses the source coordinate of the same rank when one exists,
and the corresponding fallback coordinate otherwise; it is injective and
preserves generation depth:

\[
\operatorname{rankChoice}_n(q)
=\operatorname{pasteCoordinate}(\operatorname{rankPreimage}_n,q),
\qquad
\operatorname{Injective}(\operatorname{rankChoice}_n),\quad
(\operatorname{rankChoice}_n(q)).2.\operatorname{length}=n.
\]

* `RootIndexed.rankPreimage` assigns to every target tree node its guarded
  source node of the same dynamic rank, when such a node exists.
* `RootIndexed.rankPreimage_range_countable` proves countability of the
  actual range of the complete random inverse function from countable actual
  ranges of the source and target populations.
* `RootIndexed.measurableSet_rankPreimage_eq` proves that every inverse-map
  fibre belongs to the generation-`n` domain flow.
* `RootIndexed.rankChoice` extends the inverse match to generation-`n`
  addresses by using the target copy when a source match is absent.
* `RootIndexed.rankChoice_depth` states that every selected root has address
  length `n` when every source particle does.
* `RootIndexed.rankChoice_injective` states that the selected map on
  generation-`n` addresses is injective for each field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- The sample-dependent guarded inverse rank map. -/
noncomputable def RootIndexed.rankPreimage
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.TreeNode Root α → Option (RootIndexed.TreeNode Root α) :=
  preimageByRank (sourceValue field) (targetValue field)
    (source field) (target field)

/-- Countability of the complete random inverse match follows solely from
the actual ranges of its random finite supports. -/
theorem RootIndexed.rankPreimage_range_countable
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hsourceRange : (Set.range source).Countable)
    (htargetRange : (Set.range target).Countable) :
    (Set.range (RootIndexed.rankPreimage sourceValue targetValue
      source target)).Countable := by
  exact preimageByRank_function_range_countable sourceValue targetValue
    source target hsourceRange htargetRange

/-- Every fibre of the complete random inverse match belongs to the current
generation domain flow.  The ambient root and slot types remain arbitrary. -/
theorem RootIndexed.measurableSet_rankPreimage_eq
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hsourceFiber : ∀ s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | source field = s})
    (hsourceRange : (Set.range source).Countable)
    (htargetFiber : ∀ s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | target field = s})
    (htargetRange : (Set.range target).Countable)
    (hsourceKey : ∀ p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (sourceValue field) q <
        valueKey (sourceValue field) p)
    (htargetKey : ∀ p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (targetValue field) q <
        valueKey (targetValue field) p)
    (f : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α)) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankPreimage sourceValue targetValue source target
        field = f} := by
  let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α X) :=
    RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n
  exact measurableSet_preimageByRank_function_eq sourceValue targetValue
    source target hsourceFiber hsourceRange htargetFiber htargetRange
    hsourceKey htargetKey f

/-- At every target node of generation `n`, choose the source node of equal
rank when it exists and otherwise choose the same node in the fallback copy. -/
noncomputable def RootIndexed.rankChoice
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (q : RootIndexed.Generation Root α n) :
    (Root ⊕ Root) × TreeNode α :=
  RootIndexed.StepField.pasteCoordinate
    (RootIndexed.rankPreimage sourceValue targetValue source target field) q.1

/-- Every chosen root lies in generation `n` when the source population does. -/
theorem RootIndexed.rankChoice_depth
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ field p, p ∈ source field → p.2.length = n)
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (q : RootIndexed.Generation Root α n) :
    (RootIndexed.rankChoice n sourceValue targetValue source target field q).2.length = n := by
  unfold RootIndexed.rankChoice
    RootIndexed.rankPreimage RootIndexed.StepField.pasteCoordinate
  cases hpre : preimageByRank (sourceValue field) (targetValue field)
      (source field) (target field) q.1 with
  | none => exact q.2
  | some p =>
      exact hsourceDepth field p
        (preimageByRank_eq_some_iff.mp hpre).2.1

/-- The chosen family is injective for every sample. -/
theorem RootIndexed.rankChoice_injective
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    Function.Injective
      (RootIndexed.rankChoice n sourceValue targetValue source target field) := by
  intro q₁ q₂ hq
  apply Subtype.ext
  apply RootIndexed.StepField.pasteCoordinate_injective
    (preimageByRank (sourceValue field) (targetValue field)
      (source field) (target field))
    (fun r₁ r₂ p => preimageByRank_leftUnique
      (sourceValue field) (targetValue field)
      (source field) (target field))
  exact hq

end ProbabilityTheory.BranchingRandomWalk.Coupling
