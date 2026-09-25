import ThesisSpeed.Probability.Branching.Step
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory
open Classical

namespace ThesisSpeed

noncomputable def branchingStepAtomMeasure (ξ : NatRealBranchingStep) (i : ℕ) :
    Measure ℝ := by
  exact match ξ i with
  | some x => Measure.dirac x
  | none => 0

noncomputable def branchingStepPointMeasure (ξ : NatRealBranchingStep) :
    Measure ℝ := Measure.sum (branchingStepAtomMeasure ξ)

theorem branchingStepAtomMeasure_apply (ξ : NatRealBranchingStep) (i : ℕ)
    (s : Set ℝ) (hs : MeasurableSet s) :
    branchingStepAtomMeasure ξ i s =
      match ξ i with
      | some x => if x ∈ s then 1 else 0
      | none => 0 := by
  cases h : ξ i with
  | none => simp [branchingStepAtomMeasure, h]
  | some x =>
      by_cases hx : x ∈ s <;>
        simp [branchingStepAtomMeasure, h, Measure.dirac_apply' _ hs, hx]

theorem branchingStepAtomMeasure_univ (ξ : NatRealBranchingStep) (i : ℕ) :
    branchingStepAtomMeasure ξ i Set.univ =
      if branchingStepChildPresent ξ i then 1 else 0 := by
  cases h : ξ i <;>
    simp [branchingStepAtomMeasure, branchingStepChildPresent,
      branchingStepPresent, h]

theorem branchingStepPointMeasure_apply (ξ : NatRealBranchingStep)
    (s : Set ℝ) (hs : MeasurableSet s) :
    branchingStepPointMeasure ξ s =
      ∑' i : ℕ, match ξ i with
        | some x => if x ∈ s then 1 else 0
        | none => 0 := by
  rw [branchingStepPointMeasure, Measure.sum_apply _ hs]
  exact tsum_congr (fun i => branchingStepAtomMeasure_apply ξ i s hs)

end ThesisSpeed
