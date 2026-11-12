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

This layer builds the guarded equal-rank inverse and chooses an object at the
same rank for each partner generation address.

## Public declarations

The rank choice uses the object coordinate of the same rank when one exists,
and the partner coordinate as fallback otherwise. The resulting map is
injective and preserves generation depth:

\[
\operatorname{rankChoice}_n(q)
=\operatorname{pasteCoordinate}(\operatorname{rankPreimage}_n,q),
\qquad
\operatorname{Injective}(\operatorname{rankChoice}_n),\quad
(\operatorname{rankChoice}_n(q)).2.\operatorname{length}=n.
\]

* `RootIndexed.rankPreimage` assigns to every partner tree node its guarded
  object node of the same dynamic rank, when such a node exists.
* `RootIndexed.rankPreimage_range_countable` proves countability of the
  actual range of the complete random inverse function from countable actual
  ranges of both finite populations.
* `RootIndexed.measurableSet_rankPreimage_eq` proves that every inverse-map
  fibre belongs to the generation-`n` domain flow.
* `RootIndexed.rankChoice` extends the inverse match to generation-`n`
  addresses by using the partner copy when an object match is absent.
* `RootIndexed.rankChoice_depth` states that every chosen root has address
  length `n` when every object to match does.
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
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.TreeNode Root α → Option (RootIndexed.TreeNode Root α) :=
  objectAtPartnerRankBy (objectOrderKey field) (partnerOrderKey field)
    (objectsToMatch field) (availablePartners field)

/-- Countability of the complete random inverse match follows solely from
the actual ranges of its random finite supports. -/
theorem RootIndexed.rankPreimage_range_countable
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersRange : (Set.range availablePartners).Countable) :
    (Set.range (RootIndexed.rankPreimage objectOrderKey partnerOrderKey
      objectsToMatch availablePartners)).Countable := by
  exact preimageByRank_function_range_countable objectOrderKey partnerOrderKey
    objectsToMatch availablePartners hobjectsToMatchRange havailablePartnersRange

/-- Every fibre of the complete random inverse match belongs to the current
generation domain flow.  The ambient root and slot types remain arbitrary. -/
theorem RootIndexed.measurableSet_rankPreimage_eq
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hobjectsToMatchFiber : ∀ s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | objectsToMatch field = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | availablePartners field = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (objectOrderKey field) q <
        valueKey (objectOrderKey field) p)
    (hpartnerOrderKeyMeasurable : ∀ p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (partnerOrderKey field) q <
        valueKey (partnerOrderKey field) p)
    (f : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α)) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankPreimage objectOrderKey partnerOrderKey objectsToMatch availablePartners
        field = f} := by
  let _ : MeasurableSpace (RootIndexed.StepField (Root ⊕ Root) α X) :=
    RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n
  exact measurableSet_preimageByRank_function_eq objectOrderKey partnerOrderKey
    objectsToMatch availablePartners hobjectsToMatchFiber hobjectsToMatchRange havailablePartnersFiber havailablePartnersRange
    hobjectOrderKeyMeasurable hpartnerOrderKeyMeasurable f

/-- At every partner node of generation `n`, choose the object node of equal
rank when it exists and otherwise choose the same node in the fallback copy. -/
noncomputable def RootIndexed.rankChoice
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (q : RootIndexed.Generation Root α n) :
    (Root ⊕ Root) × TreeNode α :=
  RootIndexed.StepField.pasteCoordinate
    (RootIndexed.rankPreimage objectOrderKey partnerOrderKey objectsToMatch availablePartners field) q.1

/-- Every chosen root lies in generation `n` when each object to match does. -/
theorem RootIndexed.rankChoice_depth
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hobjectsToMatchDepth : ∀ field p, p ∈ objectsToMatch field → p.2.length = n)
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (q : RootIndexed.Generation Root α n) :
    (RootIndexed.rankChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners field q).2.length = n := by
  unfold RootIndexed.rankChoice
    RootIndexed.rankPreimage RootIndexed.StepField.pasteCoordinate
  cases hpre : objectAtPartnerRankBy (objectOrderKey field) (partnerOrderKey field)
      (objectsToMatch field) (availablePartners field) q.1 with
  | none => exact q.2
  | some p =>
      exact hobjectsToMatchDepth field p
        (objectAtPartnerRankBy_eq_some_iff.mp hpre).2.1

/-- The chosen family is injective for every sample. -/
theorem RootIndexed.rankChoice_injective
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    Function.Injective
      (RootIndexed.rankChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners field) := by
  intro q₁ q₂ hq
  apply Subtype.ext
  apply RootIndexed.StepField.pasteCoordinate_injective
    (objectAtPartnerRankBy (objectOrderKey field) (partnerOrderKey field)
      (objectsToMatch field) (availablePartners field))
    (fun r₁ r₂ p => objectAtPartnerRankBy_leftUnique
      (objectOrderKey field) (partnerOrderKey field)
      (objectsToMatch field) (availablePartners field))
  exact hq

end ProbabilityTheory.BranchingRandomWalk.Coupling
