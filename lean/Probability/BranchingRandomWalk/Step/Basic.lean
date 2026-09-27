import Combinatorics.BranchingWalk.Step.PointMeasure
import Combinatorics.BranchingWalk.Step.Monotone
import Combinatorics.BranchingWalk.Step.Measurability

/-!
# Random branching steps

The primitive probabilistic input is a measurable random variable
`Ξ : Ω → Step ι X`. Everything attached to one reproduction event is first
defined deterministically on `Step ι X`; its measurability then follows by
composition with `Ξ`.

There is deliberately no inverse construction from a random counting measure
to ranked slots in this layer.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- A random branching step: a measurable `Step`-valued map on an abstract sample space. -/
structure Step (Ω ι X : Type*) [MeasurableSpace Ω]
    [MeasurableSpace X] where
  toStep : Ω → Combinatorics.Branching.Step ι X
  measurable_toStep : Measurable toStep

instance {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] :
    CoeFun (Step Ω ι X)
      (fun _ => Ω → Combinatorics.Branching.Step ι X) :=
  ⟨Step.toStep⟩

/-- The step law is the pushforward law of `Ξ`. -/
noncomputable def Step.law
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Step Ω ι X) (P : Measure Ω) :
    Measure (Combinatorics.Branching.Step ι X) :=
  P.map Ξ

instance {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Step Ω ι X) (P : Measure Ω)
    [IsProbabilityMeasure P] : IsProbabilityMeasure (Ξ.law P) := by
  unfold Step.law
  infer_instance

/-- The random point measure is a deterministic observation of `Ξ`. -/
noncomputable def Step.pointMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Step Ω ι X) : Ω → Measure X :=
  fun ω => stepPointMeasure (Ξ ω)

theorem Step.pointMeasure_measurable
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (Ξ : Step Ω ι X) :
    Measurable Ξ.pointMeasure :=
  stepPointMeasure_measurable.comp Ξ.measurable_toStep

/-- The point-measure law is obtained by mapping the step law through the
deterministic Dirac-sum function. -/
theorem Step.map_pointMeasure_law
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι] [Zero X] (Ξ : Step Ω ι X) (P : Measure Ω) :
    (Ξ.law P).map stepPointMeasure = P.map Ξ.pointMeasure := by
  unfold Step.law Step.pointMeasure
  rw [Measure.map_map stepPointMeasure_measurable Ξ.measurable_toStep]
  rfl

theorem Step.law_apply
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Step Ω ι X) (P : Measure Ω)
    (s : Set (Combinatorics.Branching.Step ι X))
    (hs : MeasurableSet s) :
    Ξ.law P s = P (Ξ ⁻¹' s) := by
  exact Measure.map_apply Ξ.measurable_toStep hs

end ProbabilityTheory.BranchingRandomWalk
