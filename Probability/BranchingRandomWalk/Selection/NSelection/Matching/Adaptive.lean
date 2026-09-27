import Probability.BranchingRandomWalk.Selection.NSelection.Matching.Law
import Probability.BranchingRandomWalk.Selection.Coupling.Field.Adaptive
import Probability.BranchingRandomWalk.Step.GenerationUpdate

/-!
# Predictable equal-rank matching

This file instantiates predictable descendant-field pasting with the guarded
equal-rank inverse.  The selected source and target populations and their
ranking values may depend on the past of the joint source/fallback field.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

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
    (preimageByRank (sourceValue field) (targetValue field)
      (source field) (target field)) q.1

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
  unfold RootIndexed.rankChoice RootIndexed.StepField.pasteCoordinate
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
          unfold RootIndexed.rankChoice RootIndexed.StepField.pasteCoordinate at h
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
          unfold RootIndexed.rankChoice RootIndexed.StepField.pasteCoordinate at h
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
        (RootIndexed.matchedStepField
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
      unfold RootIndexed.rankChoice RootIndexed.StepField.pasteCoordinate
      unfold RootIndexed.matchedStepField valueAtMatchedRank
        Selection.Coupling.valueAtPreimage
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

/-- A past-measurable equal-rank matching of generation-`n` populations
preserves the complete target product law.  Countability is localized to the
actual range of the random chosen family. -/
theorem RootIndexed.stepFieldLaw_spliceByRank
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (sourceValue targetValue :
      RootIndexed.StepField (Root ⊕ Root) α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ field p, p ∈ source field → p.2.length = n)
    (hcount : (Set.range
      (RootIndexed.rankChoice n sourceValue targetValue source target)).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field |
        RootIndexed.rankChoice n sourceValue targetValue source target field =
          roots}) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.StepField.splice n
          (RootIndexed.rankChoice n sourceValue targetValue source target)) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  exact RootIndexed.stepFieldLaw_splice μ n
    (RootIndexed.rankChoice n sourceValue targetValue source target)
    hcount hfiber
    (RootIndexed.rankChoice_depth n sourceValue targetValue source target
      hsourceDepth)
    (RootIndexed.rankChoice_injective n sourceValue targetValue source target)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
