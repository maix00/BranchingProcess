import ThesisSpeed.Probability.Branching.Step
import ThesisSpeed.Probability.PointProcess.RandomMeasure.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Branching-step point processes

A branching step is a field `ι → Option X`: `some x` is a present child with
mark `x`, and `none` is an absent slot. Summing Dirac masses over the present
slots gives a counting measure on `X`. The structure
`BranchingStepPointProcess Ω ι X` records a point process together with a
measurable branching-step realization of its samplewise measure.

This is the abstract layer corresponding to the `Option X` slot encoding. The
thesis works with `ι = ℕ`, `X = ℝ`, and the additional left-half-line
finiteness condition; that specialization is `RealBranchingStepPointProcess`.
-/

open MeasureTheory
open Classical
open scoped ENNReal

namespace ThesisSpeed

/-- The Dirac mass of a present slot, and zero for an absent slot. -/
noncomputable def branchingStepAtomMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : BranchingStep ι X) (i : ι) : Measure X :=
  match ξ i with
  | some x => Measure.dirac x
  | none => 0

/-- The point measure obtained by summing the atoms of a branching step. -/
noncomputable def branchingStepPointMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : BranchingStep ι X) : Measure X :=
  Measure.sum (branchingStepAtomMeasure ξ)

theorem branchingStepAtomMeasure_apply {ι X : Type*} [MeasurableSpace X]
    (ξ : BranchingStep ι X) (i : ι) (s : Set X) (hs : MeasurableSet s) :
    branchingStepAtomMeasure ξ i s =
      match ξ i with
      | some x => if x ∈ s then 1 else 0
      | none => 0 := by
  cases h : ξ i with
  | none => simp [branchingStepAtomMeasure, h]
  | some x =>
      by_cases hx : x ∈ s <;>
        simp [branchingStepAtomMeasure, h, Measure.dirac_apply' _ hs, hx]

theorem branchingStepAtomMeasure_univ {ι X : Type*} [MeasurableSpace X]
    (ξ : BranchingStep ι X) (i : ι) :
    branchingStepAtomMeasure ξ i Set.univ =
      if branchingStepPresent ξ i then 1 else 0 := by
  cases h : ξ i <;>
    simp [branchingStepAtomMeasure, branchingStepPresent, h]

theorem branchingStepPointMeasure_apply {ι X : Type*} [MeasurableSpace X]
    (ξ : BranchingStep ι X) (s : Set X) (hs : MeasurableSet s) :
    branchingStepPointMeasure ξ s =
      ∑' i : ι, match ξ i with
        | some x => if x ∈ s then 1 else 0
        | none => 0 := by
  rw [branchingStepPointMeasure, Measure.sum_apply _ hs]
  exact tsum_congr (fun i => branchingStepAtomMeasure_apply ξ i s hs)

/-- A point process represented by a measurable branching step. The point
measure is exactly the Dirac sum of the present slots. -/
structure BranchingStepPointProcess (Ω ι X : Type*) [MeasurableSpace Ω]
    [MeasurableSpace X] (𝒜 : Set (Set X)) extends PointProcess Ω X 𝒜 where
  toBranchingStep : Ω → BranchingStep ι X
  measurable_toBranchingStep : Measurable toBranchingStep
  measure_eq : ∀ ω, toMeasure ω = branchingStepPointMeasure (toBranchingStep ω)

instance {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (𝒜 : Set (Set X)) :
    CoeFun (BranchingStepPointProcess Ω ι X 𝒜) (fun _ => Ω → Measure X) :=
  ⟨fun Ξ => Ξ.toMeasure⟩

/-- The thesis specialization `ι = ℕ`, `X = ℝ`, with finiteness on the left
rays. The family is an explicit parameter of the underlying structure; this
abbreviation just records the paper's choice. Swapping `leftRayFamily` for
`rightRayFamily` gives the mirror-image theory with no other change, which is
why the finiteness condition itself carries no left-right asymmetry. -/
abbrev RealBranchingStepPointProcess (Ω : Type*) [MeasurableSpace Ω] :=
  BranchingStepPointProcess Ω ℕ ℝ (leftRayFamily ℝ)

/-- The zero branching-step point process, with every slot absent. -/
noncomputable def emptyBranchingStepPointProcess (Ω ι X : Type*)
    [MeasurableSpace Ω] [MeasurableSpace X] (𝒜 : Set (Set X)) :
    BranchingStepPointProcess Ω ι X 𝒜 where
  toPointProcess := emptyPointProcess Ω X 𝒜
  toBranchingStep := fun _ _ => none
  measurable_toBranchingStep :=
    measurable_pi_iff.mpr (fun _ => measurable_const)
  measure_eq := by
    intro ω
    symm
    simp [emptyPointProcess, branchingStepPointMeasure, branchingStepAtomMeasure]

/-- The empty branching-step point process with the thesis's `ℝ`
specialization. -/
noncomputable def emptyRealBranchingStepPointProcess (Ω : Type*)
    [MeasurableSpace Ω] : RealBranchingStepPointProcess Ω :=
  emptyBranchingStepPointProcess Ω ℕ ℝ (leftRayFamily ℝ)

end ThesisSpeed
