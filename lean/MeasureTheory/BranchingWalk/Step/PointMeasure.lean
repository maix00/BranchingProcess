import MeasureTheory.BranchingWalk.Step.Basic
import MeasureTheory.Measure.DiracSum

/-!
# Dirac sums of a branching step

An absent slot contributes nothing and a present slot contributes the Dirac
mass at its mark, so a step induces a counting measure on mark space. This is
the `Step` instance of `MeasureTheory.Measure.optionDiracSum`; it is
deterministic and carries no probability measure, filtration, or sample space.

The real-line vocabulary and the measurability of the induced measure under a
probability law belong to the branching random walk and live in
`Probability/BranchingRandomWalk/PointProcess/`.
-/

open MeasureTheory
open Classical
open scoped ENNReal

namespace MeasureTheory

namespace BranchingWalk

/-- The Dirac mass of a present slot, and zero for an absent slot. -/
noncomputable def stepAtomMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) : Measure X :=
  (ξ i).elim 0 Measure.dirac

/-- The point measure obtained by summing the atoms of a branching step. It is
the Dirac sum over the present slots. -/
noncomputable def stepPointMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) : Measure X :=
  Measure.sum (stepAtomMeasure ξ)

theorem stepPointMeasure_eq_optionDiracSum {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) :
    stepPointMeasure ξ = Measure.optionDiracSum ξ :=
  rfl

theorem stepAtomMeasure_apply {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) (s : Set X) (hs : MeasurableSet s) :
    stepAtomMeasure ξ i s =
      match ξ i with
      | some x => if x ∈ s then 1 else 0
      | none => 0 := by
  cases h : ξ i <;>
    simp [stepAtomMeasure, h, Measure.dirac_apply' _ hs, Set.indicator_apply]

theorem stepAtomMeasure_univ {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) :
    stepAtomMeasure ξ i Set.univ =
      if present ξ i then 1 else 0 := by
  cases h : ξ i <;>
    simp [stepAtomMeasure, present, h]

theorem stepPointMeasure_apply {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (s : Set X) (hs : MeasurableSet s) :
    stepPointMeasure ξ s =
      ∑' i : ι, match ξ i with
        | some x => if x ∈ s then 1 else 0
        | none => 0 := by
  rw [stepPointMeasure, Measure.sum_apply _ hs]
  exact tsum_congr (fun i => stepAtomMeasure_apply ξ i s hs)

end BranchingWalk

end MeasureTheory
