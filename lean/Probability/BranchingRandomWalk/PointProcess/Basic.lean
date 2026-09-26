import MeasureTheory.BranchingWalk.Step.Basic
import Probability.PointProcess.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Branching-step point processes

A branching step is a field `ι → Option X`: `some x` is a present child with
mark `x`, and `none` is an absent slot. Summing Dirac masses over the present
slots gives a counting measure on `X`. The structure
`StepPointProcess Ω ι X` records a point process together with a
measurable branching-step realization of its samplewise measure.

This is the abstract layer corresponding to the `Option X` slot encoding. The
thesis works with `ι = ℕ`, `X = ℝ`, and the additional left-half-line
finiteness condition; that specialization is `RealStepPointProcess`.
-/

open MeasureTheory
open Classical
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.BranchingWalk MeasureTheory

open MeasureTheory.BranchingWalk MeasureTheory


/-- The Dirac mass of a present slot, and zero for an absent slot. -/
noncomputable def stepAtomMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) : Measure X :=
  match ξ i with
  | some x => Measure.dirac x
  | none => 0

/-- The point measure obtained by summing the atoms of a branching step. -/
noncomputable def stepPointMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) : Measure X :=
  Measure.sum (stepAtomMeasure ξ)

theorem stepAtomMeasure_apply {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) (s : Set X) (hs : MeasurableSet s) :
    stepAtomMeasure ξ i s =
      match ξ i with
      | some x => if x ∈ s then 1 else 0
      | none => 0 := by
  cases h : ξ i with
  | none => simp [stepAtomMeasure, h]
  | some x =>
      by_cases hx : x ∈ s <;>
        simp [stepAtomMeasure, h, Measure.dirac_apply' _ hs, hx]

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

/-- A point process represented by a measurable branching step. The point
measure is exactly the Dirac sum of the present slots. -/
structure StepPointProcess (Ω ι X : Type*) [MeasurableSpace Ω]
    [MeasurableSpace X] (𝒜 : Set (Set X)) extends PointProcess Ω X 𝒜 where
  toStep : Ω → Step ι X
  measurable_toStep : Measurable toStep
  measure_eq : ∀ ω, toMeasure ω = stepPointMeasure (toStep ω)

instance {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (𝒜 : Set (Set X)) :
    CoeFun (StepPointProcess Ω ι X 𝒜) (fun _ => Ω → Measure X) :=
  ⟨fun Ξ => Ξ.toMeasure⟩

/-- The thesis specialization `ι = ℕ`, `X = ℝ`, with finiteness on the left
rays. The family is an explicit parameter of the underlying structure; this
abbreviation just records the paper's choice. Swapping `leftRayFamily` for
`rightRayFamily` gives the mirror-image theory with no other change, which is
why the finiteness condition itself carries no left-right asymmetry. -/
abbrev RealStepPointProcess (Ω : Type*) [MeasurableSpace Ω] :=
  StepPointProcess Ω ℕ ℝ (leftRayFamily ℝ)

/-- The zero branching-step point process, with every slot absent. -/
noncomputable def emptyStepPointProcess (Ω ι X : Type*)
    [MeasurableSpace Ω] [MeasurableSpace X] (𝒜 : Set (Set X)) :
    StepPointProcess Ω ι X 𝒜 where
  toPointProcess := emptyPointProcess Ω X 𝒜
  toStep := fun _ _ => none
  measurable_toStep :=
    measurable_pi_iff.mpr (fun _ => measurable_const)
  measure_eq := by
    intro ω
    symm
    simp [emptyPointProcess, stepPointMeasure, stepAtomMeasure]

/-- The empty branching-step point process with the thesis's `ℝ`
specialization. -/
noncomputable def emptyRealStepPointProcess (Ω : Type*)
    [MeasurableSpace Ω] : RealStepPointProcess Ω :=
  emptyStepPointProcess Ω ℕ ℝ (leftRayFamily ℝ)

end ProbabilityTheory.BranchingRandomWalk
