import Probability.BranchingRandomWalk.Coupling.Rank.Field
import Probability.BranchingRandomWalk.Coupling.Field.Law
import Probability.BranchingRandomWalk.Coupling.Field.Adaptive
import Probability.BranchingRandomWalk.Step.GenerationUpdate

import Probability.BranchingRandomWalk.Coupling.Rank.Choice

/-!
# Rank block-coordinate choice

This layer extends a one-generation rank choice to the complete step-only block
map and proves its range, measurability, freshness, injectivity, and gluing
properties.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- Coordinate map for a step-only installation.  At the root of each
generation block it reads the equal-rank source coordinate when matched; all
strict descendant coordinates remain in the fallback copy. -/
noncomputable def RootIndexed.rankBlockChoice
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X)
    (qv : RootIndexed.Generation Root α n × TreeNode α) :
    (Root ⊕ Root) × TreeNode α :=
  match qv.2 with
  | [] => RootIndexed.rankChoice n sourceValue targetValue source target
      field qv.1
  | i :: v => (Sum.inr qv.1.1.1, qv.1.1.2 ++ i :: v)

/-- Extend a guarded inverse map to the complete step-only block map. -/
def RootIndexed.blockChoiceOfPreimage
    {Root α : Type*} (n : ℕ)
    (preimage : RootIndexed.TreeNode Root α →
      Option (RootIndexed.TreeNode Root α)) :
    RootIndexed.Generation Root α n × TreeNode α →
      (Root ⊕ Root) × TreeNode α
  | (q, []) => RootIndexed.choiceOfPreimage n preimage q
  | (q, i :: v) => (Sum.inr q.1.1, q.1.2 ++ i :: v)

theorem RootIndexed.rankBlockChoice_eq_blockChoiceOfPreimage
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.rankBlockChoice n sourceValue targetValue source target field =
      RootIndexed.blockChoiceOfPreimage n
        (RootIndexed.rankPreimage sourceValue targetValue source target
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
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hcount : (Set.range (RootIndexed.rankPreimage
      sourceValue targetValue source target)).Countable) :
    (Set.range (RootIndexed.rankBlockChoice n sourceValue targetValue
      source target)).Countable := by
  apply (hcount.image (RootIndexed.blockChoiceOfPreimage n)).mono
  rintro f ⟨field, rfl⟩
  exact ⟨RootIndexed.rankPreimage sourceValue targetValue source target field,
    Set.mem_range_self field,
    (RootIndexed.rankBlockChoice_eq_blockChoiceOfPreimage n sourceValue
      targetValue source target field).symm⟩

/-- The random block map is countably ranged whenever its two random finite
populations are.  Ambient roots and offspring slots need not be countable. -/
theorem RootIndexed.rankBlockChoice_range_countable_of_supports
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hsourceRange : (Set.range source).Countable)
    (htargetRange : (Set.range target).Countable) :
    (Set.range (RootIndexed.rankBlockChoice n sourceValue targetValue
      source target)).Countable := by
  apply RootIndexed.rankBlockChoice_range_countable n sourceValue targetValue
    source target
  exact RootIndexed.rankPreimage_range_countable sourceValue targetValue
    source target hsourceRange htargetRange

/-- Fibre measurability of the random block map follows from fibre
measurability and countable actual range of the inverse matching. -/
theorem RootIndexed.measurableSet_rankBlockChoice_eq
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hcount : (Set.range (RootIndexed.rankPreimage
      sourceValue targetValue source target)).Countable)
    (hfiber : ∀ f, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankPreimage sourceValue targetValue source target
        field = f})
    (g : RootIndexed.Generation Root α n × TreeNode α →
      (Root ⊕ Root) × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankBlockChoice n sourceValue targetValue
        source target field = g} := by
  let S := Set.range (RootIndexed.rankPreimage
    sourceValue targetValue source target)
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  have hset : {field | RootIndexed.rankBlockChoice n sourceValue targetValue
      source target field = g} =
      ⋃ f : {f : S // RootIndexed.blockChoiceOfPreimage n f.1 = g},
        {field | RootIndexed.rankPreimage sourceValue targetValue
          source target field = f.1.1} := by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      let f := RootIndexed.rankPreimage sourceValue targetValue source target
        field
      have hfg : RootIndexed.blockChoiceOfPreimage n f = g := by
        rw [← RootIndexed.rankBlockChoice_eq_blockChoiceOfPreimage n
          sourceValue targetValue source target field]
        exact h
      exact ⟨⟨⟨f, Set.mem_range_self field⟩, hfg⟩, rfl⟩
    · rintro ⟨f, hf⟩
      rw [RootIndexed.rankBlockChoice_eq_blockChoiceOfPreimage n sourceValue
        targetValue source target field, hf]
      exact f.2
  rw [hset]
  exact MeasurableSet.iUnion fun f => hfiber f.1.1

/-- The block-map fibres belong to the current generation domain flow when
the support fibres and rank comparisons do. -/
theorem RootIndexed.measurableSet_rankBlockChoice_eq_of_supports
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
    (g : RootIndexed.Generation Root α n × TreeNode α →
      (Root ⊕ Root) × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankBlockChoice n sourceValue targetValue
        source target field = g} := by
  apply RootIndexed.measurableSet_rankBlockChoice_eq n sourceValue targetValue
    source target
  · exact RootIndexed.rankPreimage_range_countable sourceValue targetValue
      source target hsourceRange htargetRange
  · exact RootIndexed.measurableSet_rankPreimage_eq n sourceValue targetValue
      source target hsourceFiber hsourceRange htargetFiber htargetRange
      hsourceKey htargetKey

/-- Every block coordinate is fresh at generation `n` or later. -/
theorem RootIndexed.rankBlockChoice_future
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
    (qv : RootIndexed.Generation Root α n × TreeNode α) :
    n ≤ (RootIndexed.rankBlockChoice n sourceValue targetValue source target
      field qv).2.length := by
  rcases qv with ⟨q, v⟩
  cases v with
  | nil =>
      exact le_of_eq (RootIndexed.rankChoice_depth n sourceValue targetValue
        source target hsourceDepth field q).symm
  | cons i v =>
      simp [RootIndexed.rankBlockChoice, q.2]

/-- The complete step-only block coordinate map is injective. -/
theorem RootIndexed.rankBlockChoice_injective
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
      (RootIndexed.rankBlockChoice n sourceValue targetValue source target
        field) := by
  rintro ⟨q₁, v₁⟩ ⟨q₂, v₂⟩ h
  cases v₁ with
  | nil =>
      cases v₂ with
      | nil =>
          have hq : q₁ = q₂ :=
            RootIndexed.rankChoice_injective n sourceValue targetValue
              source target field h
          subst q₂
          rfl
      | cons j w =>
          unfold RootIndexed.rankBlockChoice at h
          unfold RootIndexed.rankChoice RootIndexed.choiceOfPreimage
            RootIndexed.rankPreimage RootIndexed.StepField.pasteCoordinate at h
          cases hp : preimageByRank (sourceValue field) (targetValue field)
              (source field) (target field) q₁.1 with
          | some p => simp [hp] at h
          | none =>
              simp only [hp] at h
              have hlen := congrArg (fun z => z.2.length) h
              simp [q₁.2, q₂.2] at hlen
  | cons i v =>
      cases v₂ with
      | nil =>
          unfold RootIndexed.rankBlockChoice at h
          unfold RootIndexed.rankChoice RootIndexed.choiceOfPreimage
            RootIndexed.rankPreimage RootIndexed.StepField.pasteCoordinate at h
          cases hp : preimageByRank (sourceValue field) (targetValue field)
              (source field) (target field) q₂.1 with
          | some p => simp [hp] at h
          | none =>
              simp only [hp] at h
              have hlen := congrArg (fun z => z.2.length) h
              simp [q₁.2, q₂.2] at hlen
      | cons j w =>
          have hbranch := RootIndexed.branchingAddresses_injective
            (RootIndexed.generationRoots (Root := Root) (α := α) n)
            (RootIndexed.generationRoots_depth n)
            (RootIndexed.generationRoots_injective n)
          exact hbranch (by simpa [RootIndexed.rankBlockChoice,
            RootIndexed.generationRoots] using h)

/-- The block-coordinate construction is exactly the step-only
`updateGeneration` installation when the prior field still equals the
fallback copy at generation `n` and later. -/
theorem RootIndexed.glue_rankBlockChoice_eq_updateGeneration
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (base : RootIndexed.StepField (Root ⊕ Root) α X)
    (prior : RootIndexed.StepField Root α X)
    (hprior : ∀ r u, n ≤ u.length → prior r u = base (Sum.inr r) u) :
    RootIndexed.StepField.glue n (prior.past n)
        (RootIndexed.selectedCoordinateField
          (RootIndexed.rankBlockChoice n sourceValue targetValue source target)
          base) =
      Combinatorics.Branching.RootIndexed.StepField.updateGeneration n
        (RootIndexed.rankInstalledStepField
          (fun _ => sourceValue base) (fun _ => targetValue base)
          (fun _ => source base) (fun _ => target base)
          (fun sample r u => sample (Sum.inl r) u)
          (fun _ => prior) base)
        prior := by
  funext r u
  by_cases hlt : u.length < n
  · simp [RootIndexed.StepField.glue, hlt,
      Combinatorics.Branching.RootIndexed.StepField.updateGeneration_apply,
      Nat.ne_of_lt hlt, RootIndexed.StepField.past]
  · have hle : n ≤ u.length := Nat.le_of_not_gt hlt
    by_cases heq : u.length = n
    · have htake : u.take n = u := by simp [heq]
      have hdrop : u.drop n = [] := by simp [heq]
      simp only [RootIndexed.StepField.glue,
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration_apply,
        heq, ↓reduceIte, RootIndexed.selectedCoordinateField,
        RootIndexed.StepField.reindexCoordinates_apply, htake, hdrop,
        RootIndexed.rankBlockChoice]
      unfold RootIndexed.rankChoice RootIndexed.choiceOfPreimage
        RootIndexed.rankPreimage RootIndexed.StepField.pasteCoordinate
      unfold RootIndexed.rankInstalledStepField valueAtMatchedRank
        Coupling.valueAtPreimage
      cases hpre : preimageByRank (sourceValue base) (targetValue base)
          (source base) (target base) (r, u) with
      | some p => simp [hpre]
      | none => simp [hpre, hprior r u hle]
    · have hgt : n < u.length := lt_of_le_of_ne hle (Ne.symm heq)
      have hdrop : u.drop n ≠ [] := by
        intro hnil
        have := congrArg List.length (List.take_append_drop n u)
        simp [hnil, List.length_take, Nat.min_eq_left hle] at this
        omega
      simp only [RootIndexed.StepField.glue, hlt, dite_false,
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration_apply,
        heq, ↓reduceIte, RootIndexed.selectedCoordinateField,
        RootIndexed.StepField.reindexCoordinates_apply]
      cases hv : u.drop n with
      | nil => exact (hdrop hv).elim
      | cons i v =>
          simp only [RootIndexed.rankBlockChoice]
          have huv : u.take n ++ i :: v = u := by
            rw [← hv]
            exact List.take_append_drop n u
          rw [huv]
          exact (hprior r u hle).symm

end ProbabilityTheory.BranchingRandomWalk.Coupling
