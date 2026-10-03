module

public import Probability.BranchingRandomWalk.Selection.NSelection.ByValue
public import Probability.BranchingRandomWalk.Selection.NSelection.Infinite
public import Probability.BranchingRandomWalk.Selection.NSelection.Totalized
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability
public import Combinatorics.BranchingWalk.Basic.Position

/-!
# Adapted spatial selection in a pre-sampled forest

This file instantiates dynamic measurable selection with positions in an
arbitrary root-indexed pre-sampled branching walk. Marks, additive positions,
and ordered observations remain separate. Selection in the opposite spatial
direction applies `OrderDual` only to the observation type.
-/

open MeasureTheory Combinatorics.UlamHarris

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.RootIndexed

open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.Selection

noncomputable section

variable {Root α Mark Position Value : Type*}

/-- The observed position of a labelled particle at generation `n`. Labels
at another depth receive additive zero; actual generation candidate sets
contain only labels of depth `n`. -/
def observedPositionAtGeneration
    [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position)
    (φ : Position → Value) (n : ℕ)
    (ω : RootIndexed.StepField Root α Mark)
    (p : RootIndexed.TreeNode Root α) : Value :=
  φ (ProbabilityTheory.BranchingRandomWalk.RootIndexed.positionAtGeneration
    initial d n p.1 p.2 ω)

theorem observedPositionAtGeneration_eq
    [AddCommMonoid Position]
    (initial : Root → Position) (d : Mark → Position)
    (φ : Position → Value) (n : ℕ)
    (ω : RootIndexed.StepField Root α Mark)
    (p : RootIndexed.TreeNode Root α) (hp : p.2.length = n) :
    observedPositionAtGeneration initial d φ n ω p =
      φ ((Combinatorics.Branching.RootIndexed.BranchingWalk.ofStepField
        initial ω).position d p.1 p.2) := by
  simp [observedPositionAtGeneration, RootIndexed.positionAtGeneration, hp,
    RootIndexed.position, RootIndexed.displace,
    Combinatorics.Branching.RootIndexed.BranchingWalk.position]

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
      (fun ω => Combinatorics.Branching.Selection.NSelection.selectFirstNBy N
        (observedPositionAtGeneration initial d φ n ω) (candidates ω)) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark) n
  apply Selection.NSelection.measurable_selectFirstNBy N
    (observedPositionAtGeneration initial d φ n) candidates
    hcandidateFiber hcandidateRange
  intro p q
  apply Selection.NSelection.measurable_valueKey_lt
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
      Combinatorics.Branching.Selection.NSelection.AdmitsFirstNBy N
        (observedPositionAtGeneration initial d φ n ω) (candidates ω))
    (hcandidates : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n] candidates) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n]
      (fun ω =>
        Combinatorics.Branching.Selection.NSelection.selectFirstNFromSet N
          (observedPositionAtGeneration initial d φ n ω)
          (candidates ω) (hadmits ω)) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark) n
  apply Selection.NSelection.measurable_selectFirstNFromSet N
    (observedPositionAtGeneration initial d φ n) candidates hadmits hcandidates
  intro p q
  apply Selection.NSelection.measurable_valueKey_lt
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
      (fun ω => Selection.NSelection.selectFirstNFromSetTotalized N
        (observedPositionAtGeneration initial d φ n) candidates ω) := by
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark) n
  apply Selection.NSelection.measurable_selectFirstNFromSetTotalized
    N (observedPositionAtGeneration initial d φ n) candidates hcandidates
  intro p q
  apply Selection.NSelection.measurable_valueKey_lt
  intro r
  exact hφ.comp
    (ProbabilityTheory.BranchingRandomWalk.RootIndexed.positionAtGeneration_measurable
      initial d hd n r.1 r.2)

/-- Dynamic leftmost selection is causal for the generation domain flow of an
arbitrary root-indexed pre-sampled forest. Countability is needed only by the
finite-set measurable encoding used by this concrete capacity selector. -/
noncomputable def leftmostBy
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
    (φ : Position → Value) (hφ : Measurable φ) :
    CausalFiniteNSelection ℕ
      (RootIndexed.StepField Root α Mark)
      (RootIndexed.TreeNode Root α) N
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark)) :=
  CausalFiniteNSelection.leftmostByOfMeasurableValue N
    (observedPositionAtGeneration initial d φ)
    (fun n p => hφ.comp
      (ProbabilityTheory.BranchingRandomWalk.RootIndexed.positionAtGeneration_measurable
        initial d hd n p.1 p.2))

@[simp] theorem leftmostBy_select
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
    (φ : Position → Value) (hφ : Measurable φ)
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
    (s : Finset (RootIndexed.TreeNode Root α)) :
    (leftmostBy N initial d hd φ hφ).select n ω s =
      Combinatorics.Branching.Selection.NSelection.selectFirstNBy N
        (observedPositionAtGeneration initial d φ n ω) s :=
  rfl

/-- The opposite spatial selection uses the same position process and changes
only its ordered observation to `OrderDual Value`. -/
noncomputable def rightmostBy
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
    (φ : Position → Value) (hφ : Measurable φ) :
    CausalFiniteNSelection ℕ
      (RootIndexed.StepField Root α Mark)
      (RootIndexed.TreeNode Root α) N
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := Mark)) :=
  leftmostBy N initial d hd
    (fun x => OrderDual.toDual (φ x)) hφ

@[simp] theorem rightmostBy_select
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
    (φ : Position → Value) (hφ : Measurable φ)
    (n : ℕ) (ω : RootIndexed.StepField Root α Mark)
    (s : Finset (RootIndexed.TreeNode Root α)) :
    (rightmostBy N initial d hd φ hφ).select n ω s =
      Combinatorics.Branching.Selection.NSelection.selectFirstNBy N
        (fun p => OrderDual.toDual
          (observedPositionAtGeneration initial d φ n ω p)) s :=
  rfl

end

end ProbabilityTheory.BranchingRandomWalk.RootIndexed
