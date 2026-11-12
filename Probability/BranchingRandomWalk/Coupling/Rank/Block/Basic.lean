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

public import Probability.BranchingRandomWalk.Coupling.Rank.Choice
public import Combinatorics.UlamHarris.Generation

/-!
# Rank block-coordinate choice

This layer extends a one-generation rank choice to the complete step-only block
map and proves its range, measurability, freshness, and injectivity. The one-use
gluing identity is internal proof support under `Lemmas/Glue.lean`.

## Public declarations

The block map applies the equal-rank choice at the root and leaves every
strict descendant in the fallback copy; it is injective and does not map a
coordinate to a depth below `n`:

\[
\operatorname{rankBlockChoice}_n(F)((r,u),v)=
\begin{cases}
\operatorname{rankChoice}_n(F)((r,u)),&v=[],\\
(\operatorname{inr}(r),u\mathbin{++}i::w),&v=i::w,
\end{cases}
\qquad
\operatorname{Injective}(\operatorname{rankBlockChoice}_n(F)),
\quad |u|=n\Longrightarrow
\left|\operatorname{rankBlockChoice}_n(F)((r,u),v).2\right|\ge n.
\]

* `RootIndexed.rankBlockChoice` maps the root coordinate of each generation
  block by equal rank and keeps strict descendants in the partner copy.
* `RootIndexed.rankBlockChoice_range_countable` transfers countability of the
  actual inverse-map range to the complete block-map range.
* `RootIndexed.rankBlockChoice_range_countable_of_supports` derives that
  countability from countable actual ranges of the random finite populations.
* `RootIndexed.measurableSet_rankBlockChoice_eq_of_supports` proves that each
  block-map fibre belongs to the generation-`n` domain flow under measurable
  support fibres and measurable rank comparisons.
* `RootIndexed.rankBlockChoice_future` states that every output coordinate
  has address length at least `n`.
* `RootIndexed.rankBlockChoice_injective` states that the complete
  step-only block-coordinate map is injective.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling


open Combinatorics.UlamHarris Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection

/-- Coordinate map for a step-only installation. At the root of each
generation block it reads the equal-rank object coordinate when matched; all
strict descendant coordinates remain in the fallback copy. -/
noncomputable def RootIndexed.rankBlockChoice
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (qv : RootIndexed.Generation Root α n × TreeNode α) :
    (Root ⊕ Root) × TreeNode α :=
  match qv.2 with
  | [] => RootIndexed.rankChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners
      field qv.1
  | i :: v => (Sum.inr qv.1.1.1, qv.1.1.2 ++ i :: v)

/-- Extend a guarded inverse map to the complete step-only block map. -/
private def RootIndexed.blockChoiceOfPreimage
    {Root α : Type*} (n : ℕ)
    (preimage : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α)) :
    RootIndexed.Generation Root α n × TreeNode α →
      (Root ⊕ Root) × TreeNode α
  | (q, []) => RootIndexed.StepField.pasteCoordinate preimage q.1
  | (q, i :: v) => (Sum.inr q.1.1, q.1.2 ++ i :: v)

private theorem RootIndexed.rankBlockChoice_eq_blockChoiceOfPreimage
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.rankBlockChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners field =
      RootIndexed.blockChoiceOfPreimage n
        (RootIndexed.rankPreimage objectOrderKey partnerOrderKey objectsToMatch availablePartners
          field) := by
  funext qv
  rcases qv with ⟨q, v⟩
  cases v <;> rfl

/-- Countability of the random block map follows from countability of the
actual range of the finite-support inverse matching. -/
theorem RootIndexed.rankBlockChoice_range_countable
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hcount : (Set.range (RootIndexed.rankPreimage
      objectOrderKey partnerOrderKey objectsToMatch availablePartners)).Countable) :
    (Set.range (RootIndexed.rankBlockChoice n objectOrderKey partnerOrderKey
      objectsToMatch availablePartners)).Countable := by
  apply (hcount.image (RootIndexed.blockChoiceOfPreimage n)).mono
  rintro f ⟨field, rfl⟩
  exact ⟨RootIndexed.rankPreimage objectOrderKey partnerOrderKey objectsToMatch availablePartners field,
    Set.mem_range_self field,
    (RootIndexed.rankBlockChoice_eq_blockChoiceOfPreimage n objectOrderKey
      partnerOrderKey objectsToMatch availablePartners field).symm⟩

/-- The random block map is countably ranged whenever its two random finite
populations are.  Ambient roots and offspring slots need not be countable. -/
theorem RootIndexed.rankBlockChoice_range_countable_of_supports
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersRange : (Set.range availablePartners).Countable) :
    (Set.range (RootIndexed.rankBlockChoice n objectOrderKey partnerOrderKey
      objectsToMatch availablePartners)).Countable := by
  apply RootIndexed.rankBlockChoice_range_countable n objectOrderKey partnerOrderKey
    objectsToMatch availablePartners
  exact RootIndexed.rankPreimage_range_countable objectOrderKey partnerOrderKey
    objectsToMatch availablePartners hobjectsToMatchRange havailablePartnersRange

/-- Fibre measurability of the random block map follows from fibre
measurability and countable actual range of the inverse matching. -/
private theorem RootIndexed.measurableSet_rankBlockChoice_eq
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (objectOrderKey partnerOrderKey :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hcount : (Set.range (RootIndexed.rankPreimage
      objectOrderKey partnerOrderKey objectsToMatch availablePartners)).Countable)
    (hfiber : ∀ f, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankPreimage objectOrderKey partnerOrderKey objectsToMatch availablePartners
        field = f})
    (g : RootIndexed.Generation Root α n × TreeNode α →
      (Root ⊕ Root) × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankBlockChoice n objectOrderKey partnerOrderKey
        objectsToMatch availablePartners field = g} := by
  let S := Set.range (RootIndexed.rankPreimage
    objectOrderKey partnerOrderKey objectsToMatch availablePartners)
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  have hset : {field | RootIndexed.rankBlockChoice n objectOrderKey partnerOrderKey
      objectsToMatch availablePartners field = g} =
      ⋃ f : {f : S // RootIndexed.blockChoiceOfPreimage n f.1 = g},
        {field | RootIndexed.rankPreimage objectOrderKey partnerOrderKey
          objectsToMatch availablePartners field = f.1.1} := by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      let f := RootIndexed.rankPreimage objectOrderKey partnerOrderKey objectsToMatch availablePartners
        field
      have hfg : RootIndexed.blockChoiceOfPreimage n f = g := by
        rw [← RootIndexed.rankBlockChoice_eq_blockChoiceOfPreimage n
          objectOrderKey partnerOrderKey objectsToMatch availablePartners field]
        exact h
      exact ⟨⟨⟨f, Set.mem_range_self field⟩, hfg⟩, rfl⟩
    · rintro ⟨f, hf⟩
      rw [RootIndexed.rankBlockChoice_eq_blockChoiceOfPreimage n objectOrderKey
        partnerOrderKey objectsToMatch availablePartners field, hf]
      exact f.2
  rw [hset]
  exact MeasurableSet.iUnion fun f => hfiber f.1.1

/-- The block-map fibres belong to the current generation domain flow when
the support fibres and rank comparisons do. -/
theorem RootIndexed.measurableSet_rankBlockChoice_eq_of_supports
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
    (g : RootIndexed.Generation Root α n × TreeNode α →
      (Root ⊕ Root) × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankBlockChoice n objectOrderKey partnerOrderKey
        objectsToMatch availablePartners field = g} := by
  apply RootIndexed.measurableSet_rankBlockChoice_eq n objectOrderKey partnerOrderKey
    objectsToMatch availablePartners
  · exact RootIndexed.rankPreimage_range_countable objectOrderKey partnerOrderKey
      objectsToMatch availablePartners hobjectsToMatchRange havailablePartnersRange
  · exact RootIndexed.measurableSet_rankPreimage_eq n objectOrderKey partnerOrderKey
      objectsToMatch availablePartners hobjectsToMatchFiber hobjectsToMatchRange havailablePartnersFiber havailablePartnersRange
      hobjectOrderKeyMeasurable hpartnerOrderKeyMeasurable

/-- Every block coordinate is fresh at generation `n` or later. -/
theorem RootIndexed.rankBlockChoice_future
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
    (qv : RootIndexed.Generation Root α n × TreeNode α) :
    n ≤ (RootIndexed.rankBlockChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners
      field qv).2.length := by
  rcases qv with ⟨q, v⟩
  cases v with
  | nil =>
      exact le_of_eq (RootIndexed.rankChoice_depth n objectOrderKey partnerOrderKey
        objectsToMatch availablePartners hobjectsToMatchDepth field q).symm
  | cons i v =>
      simp [RootIndexed.rankBlockChoice, q.2]

/-- The complete step-only block coordinate map is injective. -/
theorem RootIndexed.rankBlockChoice_injective
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
      (RootIndexed.rankBlockChoice n objectOrderKey partnerOrderKey objectsToMatch availablePartners
        field) := by
  rintro ⟨q₁, v₁⟩ ⟨q₂, v₂⟩ h
  cases v₁ with
  | nil =>
      cases v₂ with
      | nil =>
          have hq : q₁ = q₂ :=
            RootIndexed.rankChoice_injective n objectOrderKey partnerOrderKey
              objectsToMatch availablePartners field h
          subst q₂
          rfl
      | cons j w =>
          unfold RootIndexed.rankBlockChoice at h
          unfold RootIndexed.rankChoice
            RootIndexed.rankPreimage RootIndexed.StepField.pasteCoordinate at h
          cases hp : objectAtPartnerRankBy (objectOrderKey field) (partnerOrderKey field)
              (objectsToMatch field) (availablePartners field) q₁.1 with
          | some p => simp [hp] at h
          | none =>
              simp only [hp] at h
              have hlen := congrArg (fun z => z.2.length) h
              simp [q₁.2, q₂.2] at hlen
  | cons i v =>
      cases v₂ with
      | nil =>
          unfold RootIndexed.rankBlockChoice at h
          unfold RootIndexed.rankChoice
            RootIndexed.rankPreimage RootIndexed.StepField.pasteCoordinate at h
          cases hp : objectAtPartnerRankBy (objectOrderKey field) (partnerOrderKey field)
              (objectsToMatch field) (availablePartners field) q₂.1 with
          | some p => simp [hp] at h
          | none =>
              simp only [hp] at h
              have hlen := congrArg (fun z => z.2.length) h
              simp [q₁.2, q₂.2] at hlen
      | cons j w =>
          have hbranch := Combinatorics.UlamHarris.RootIndexed.appendAddresses_injective
            (RootIndexed.generationRoots (Root := Root) (α := α) n)
            (RootIndexed.generationRoots_depth n)
            (RootIndexed.generationRoots_injective n)
          exact hbranch (by simpa [RootIndexed.rankBlockChoice,
            RootIndexed.generationRoots] using h)


end ProbabilityTheory.BranchingRandomWalk.Coupling
