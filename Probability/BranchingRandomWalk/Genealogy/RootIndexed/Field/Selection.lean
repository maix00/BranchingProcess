/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Selection.NSelection.ByValue
public import MeasureTheory.Selection.NSelection.FromSet
public import MeasureTheory.Selection.NSelection.Totalized
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Measurability
public import Combinatorics.BranchingWalk.Basic.Position.Basic

/-!
# Adapted spatial selection in a pre-sampled forest

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.measurable_selectFirstNBy`:
  in a pre-sampled forest, the first `N` particles by observed position at
  generation `n` form a measurable finite set when the candidate fibres are
  measurable with countable actual range.
- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.measurable_selectFirstNFromSet`:
  the intrinsic first-`N` segment of a measurable, possibly infinite
  generation candidate set is measurable when it exists pointwise and the
  labels are countable.
- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.measurable_selectFirstNFromSetTotalized`:
  the totalized selector using an empty-set fallback outside the
  lower-finite domain is generation-measurable for countable labels.

Marks, additive positions, and ordered observations remain separate.
Selection in the opposite spatial direction applies `OrderDual` only to the
observation type.
-/

open MeasureTheory Combinatorics.UlamHarris
open Combinatorics.Selection.NSelection

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.Branching
noncomputable section

variable {Root α Mark Position Value : Type*}

/-- Selecting the first `N` observed positions from a concrete random finite
candidate set is generation-measurable when its fibres are measurable and its
actual range is countable. Neither the root type nor the child-slot type is
required to be countable. -/
theorem measurable_selectFirstNBy
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) (n : ℕ)
    (candidates : RootIndexed.StepField Root α Mark →
      Finset (RootIndexed.TreeNode Root α))
    (hcandidateFiber : ∀ s,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark) n]
        {ω | candidates ω = s})
    (hcandidateRange : (Set.range candidates).Countable) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (fun ω => Combinatorics.Selection.NSelection.selectFirstNBy N
        (observedPositionAtGeneration initial d φ n ω) (candidates ω)) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark) n
  apply Combinatorics.Selection.NSelection.measurable_selectFirstNBy N
    (observedPositionAtGeneration initial d φ n) candidates
    hcandidateFiber hcandidateRange
  intro p q
  apply Combinatorics.Selection.NSelection.measurable_valueKey_lt
  intro r
  exact hφ.comp
    (ProbabilityTheory.BranchingRandomWalk.RootIndexed.positionAtGeneration_measurable
      initial d hd n r.1 r.2)

/-- The intrinsic first-`N` segment of a possibly infinite generation
candidate population is measurable when it exists pointwise. The candidates
remain set-valued; only the selected population is finite. -/
theorem measurable_selectFirstNFromSet
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) (n : ℕ)
    (candidates : RootIndexed.StepField Root α Mark →
      Set (RootIndexed.TreeNode Root α))
    (hadmits : ∀ ω,
      Combinatorics.Selection.NSelection.AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ n ω) (candidates ω))
    (hcandidates : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n] candidates) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (fun ω =>
        Combinatorics.Selection.NSelection.selectFirstNFromSet N
          (observedPositionAtGeneration initial d φ n ω)
          (candidates ω) (hadmits ω)) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark) n
  apply Combinatorics.Selection.NSelection.measurable_selectFirstNFromSet N
    (observedPositionAtGeneration initial d φ n) candidates hadmits hcandidates
  intro p q
  apply Combinatorics.Selection.NSelection.measurable_valueKey_lt
  intro r
  exact hφ.comp
    (ProbabilityTheory.BranchingRandomWalk.RootIndexed.positionAtGeneration_measurable
      initial d hd n r.1 r.2)

/-- Totalized first-N selection by observed generation position is measurable
without requiring every raw field to admit an initial segment.  The selector
uses its empty-set fallback outside the lower-finite domain. -/
theorem measurable_selectFirstNFromSetTotalized
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    [MeasurableSpace Value] [TopologicalSpace Value]
    [OpensMeasurableSpace Value] [LinearOrder Value]
    [SecondCountableTopology Value] [OrderClosedTopology Value]
    [MeasurableEq Value]
    (N : ℕ) (initial : Root → Position)
    (d : Mark → Position) (hd : Measurable d)
    (φ : Position → Value) (hφ : Measurable φ) (n : ℕ)
    (candidates : RootIndexed.StepField Root α Mark →
      Set (RootIndexed.TreeNode Root α))
    (hcandidates : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n] candidates) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (fun ω => Combinatorics.Selection.NSelection.selectFirstNFromSetTotalized N
        (observedPositionAtGeneration initial d φ n) candidates ω) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark) n
  apply Combinatorics.Selection.NSelection.measurable_selectFirstNFromSetTotalized
    N (observedPositionAtGeneration initial d φ n) candidates hcandidates
  intro p q
  apply Combinatorics.Selection.NSelection.measurable_valueKey_lt
  intro r
  exact hφ.comp
    (ProbabilityTheory.BranchingRandomWalk.RootIndexed.positionAtGeneration_measurable
      initial d hd n r.1 r.2)

end

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
