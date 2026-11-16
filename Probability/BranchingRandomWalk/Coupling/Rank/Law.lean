/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Coupling.Rank.Field
public import Probability.BranchingRandomWalk.Coupling.Field.Law

/-!
# Product law of a fixed rank matching

For fixed object and partner populations, install the object coordinate of
each rank into the partner coordinate of the same rank. The object and
fallback fields are the two summands of one product field. The installed
partner field is again a complete i.i.d. field.

This is a fixed-cell theorem.  Random, past-measurable populations are handled
later by partitioning over their actual range.

## Public declarations

For fixed finite object and partner populations, equal-rank installation is a
paste along the guarded rank preimage and preserves the product law:

\[\begin{aligned}
\operatorname{rankInstalledStepField}
&=\operatorname{paste}(\operatorname{objectAtPartnerRankBy}),\\
\operatorname{rankInstalledStepField}_{\#}
\operatorname{stepFieldLaw}_{R\oplus R}^{\mu}
&=\operatorname{stepFieldLaw}_{R}^{\mu}.
\end{aligned}\]

- `ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.rankInstalledStepField_eq_paste`:
  identifies fixed equal-rank installation with
  `StepField.paste (objectAtPartnerRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners)`.
- `ProbabilityTheory.BranchingRandomWalk.Coupling.RootIndexed.stepFieldLaw_rankInstalledStepField`:
  for independent product fields on two root copies, mapping the combined
  field through a fixed equal-rank installation gives the product law on one
  root set.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- Fixed equal-rank installation is the generic paste operation associated
with the guarded inverse matching. -/
theorem RootIndexed.rankInstalledStepField_eq_paste
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.rankInstalledStepField
        (fun _ => objectOrderKey) (fun _ => partnerOrderKey)
        (fun _ => objectsToMatch) (fun _ => availablePartners)
        (fun sample r u => sample (Sum.inl r) u)
        (fun sample r u => sample (Sum.inr r) u) field =
      RootIndexed.StepField.paste
        (objectAtPartnerRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners) field := by
  funext r u
  simp only [RootIndexed.rankInstalledStepField, valueAtMatchedRank,
    Coupling.valueAtObjectPreimage, RootIndexed.StepField.paste,
    RootIndexed.StepField.reindexCoordinates_apply]
  cases h : objectAtPartnerRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners (r, u) <;>
    simp [RootIndexed.StepField.pasteCoordinate, h]

/-- Installing a fixed equal-rank matching between two independent copies
preserves the root-indexed product law.  Roots and offspring slots may be
arbitrary types. -/
theorem RootIndexed.stepFieldLaw_rankInstalledStepField
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (objectOrderKey partnerOrderKey : RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : Finset (RootIndexed.TreeNode Root α)) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (fun field => RootIndexed.rankInstalledStepField
          (fun _ => objectOrderKey) (fun _ => partnerOrderKey)
          (fun _ => objectsToMatch) (fun _ => availablePartners)
          (fun sample r u => sample (Sum.inl r) u)
          (fun sample r u => sample (Sum.inr r) u) field) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  rw [show (fun field => RootIndexed.rankInstalledStepField
      (fun _ => objectOrderKey) (fun _ => partnerOrderKey)
      (fun _ => objectsToMatch) (fun _ => availablePartners)
      (fun sample r u => sample (Sum.inl r) u)
      (fun sample r u => sample (Sum.inr r) u) field) =
      RootIndexed.StepField.paste
        (objectAtPartnerRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners) by
    funext field
    exact RootIndexed.rankInstalledStepField_eq_paste
      objectOrderKey partnerOrderKey objectsToMatch availablePartners field]
  exact RootIndexed.stepFieldLaw_paste μ
    (objectAtPartnerRankBy objectOrderKey partnerOrderKey objectsToMatch availablePartners)
    (fun q₁ q₂ p => objectAtPartnerRankBy_leftUnique
      objectOrderKey partnerOrderKey objectsToMatch availablePartners)

end ProbabilityTheory.BranchingRandomWalk.Coupling

end
