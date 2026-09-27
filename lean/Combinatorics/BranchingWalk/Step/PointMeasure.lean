import Combinatorics.BranchingWalk.Step.Basic
import Combinatorics.BranchingWalk.Step.Measurability
import Mathlib.MeasureTheory.Measure.GiryMonad
import MeasureTheory.Measure.DiracSum

/-!
# Dirac sums of a branching step

An absent slot contributes nothing and a survive slot contributes the Dirac
mass at its mark, so a step induces a counting measure on mark space. This is
the `Step` instance of `MeasureTheory.Measure.iOptionDiracSum`; it is
deterministic and carries no probability measure, filtration, or sample space.

Measurability of this observation under a random step lives in
`Probability/BranchingRandomWalk/Step/`.
-/

open MeasureTheory
open Classical
open scoped ENNReal

namespace Combinatorics

namespace Branching

/-- The Dirac mass of a survive slot, and zero for an absent slot. -/
noncomputable def stepAtomMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) : Measure X :=
  (ξ i).elim 0 Measure.dirac

/-- The point measure obtained by summing the atoms of a branching step. It is
the Dirac sum over the survive slots. -/
noncomputable def stepPointMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) : Measure X :=
  Measure.sum (stepAtomMeasure ξ)

theorem stepPointMeasure_eq_iOptionDiracSum {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) :
    stepPointMeasure ξ = Measure.iOptionDiracSum ξ :=
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
      if survive ξ i then 1 else 0 := by
  cases h : ξ i <;>
    simp [stepAtomMeasure, survive, h]

theorem stepPointMeasure_apply {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (s : Set X) (hs : MeasurableSet s) :
    stepPointMeasure ξ s =
      ∑' i : ι, match ξ i with
        | some x => if x ∈ s then 1 else 0
        | none => 0 := by
  rw [stepPointMeasure, Measure.sum_apply _ hs]
  exact tsum_congr (fun i => stepAtomMeasure_apply ξ i s hs)

/-- The Dirac mass of a slot is a measurable function of the step: it is the Dirac mass at the slot's value
where the slot is survive, and the zero measure where it is not. -/
theorem stepAtomMeasure_measurable {ι X : Type*} [MeasurableSpace X] [Zero X] (i : ι) :
    Measurable (fun ξ : Step ι X => stepAtomMeasure ξ i) := by
  classical
  have hfun : (fun ξ : Step ι X => stepAtomMeasure ξ i) =
      fun ξ => if survive ξ i then Measure.dirac (value' ξ i) else 0 := by
    funext ξ
    cases h : ξ i with
    | none => simp [stepAtomMeasure, h, survive]
    | some x => simp [stepAtomMeasure, h, survive, value']
  rw [hfun]
  exact (Measure.measurable_dirac.comp (value'_measurable i)).ite
    (survive_measurableSet i) measurable_const

/-- The point measure of a step is a measurable function of the step. -/
theorem stepPointMeasure_measurable {ι X : Type*} [Countable ι] [MeasurableSpace X] [Zero X] :
    Measurable (fun ξ : Step ι X => stepPointMeasure ξ) := by
  have hfun : (fun ξ : Step ι X => stepPointMeasure ξ) =
      fun ξ => Measure.sum (stepAtomMeasure ξ) := rfl
  rw [hfun]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable (fun ξ : Step ι X => (Measure.sum (stepAtomMeasure ξ)) s)
  simp_rw [Measure.sum_apply _ hs]
  exact Measurable.tsum (fun i => (Measure.measurable_coe hs).comp (stepAtomMeasure_measurable i))

end Branching

end Combinatorics
