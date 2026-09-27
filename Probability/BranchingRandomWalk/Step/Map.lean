import Combinatorics.BranchingWalk.Step.Map
import Probability.BranchingRandomWalk.Step.Basic

/-!
# Mapping random branching-step marks

A measurable map of marks acts on a random `Step` by composing the random
variable with the deterministic `Combinatorics.Branching.Step.map`. Forgetting
marks is the constant-map instance used for the Galton--Watson genealogy.
-/

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory

 theorem measurable_stepMap
    {ι X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) :
    Measurable (fun ξ : Combinatorics.Branching.Step ι X => ξ.map f) := by
  rw [measurable_pi_iff]
  intro i
  exact (measurable_option_map hf).comp (measurable_pi_apply i)

/-- Map the marks of a random step by a measurable function. -/
def Step.map {Ω ι X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    (Ξ : Step Ω ι X) (f : X → Y) (hf : Measurable f) : Step Ω ι Y where
  toStep ω := (Ξ ω).map f
  measurable_toStep := (measurable_stepMap f hf).comp Ξ.measurable_toStep

@[simp] theorem Step.map_apply {Ω ι X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    (Ξ : Step Ω ι X) (f : X → Y) (hf : Measurable f) (ω : Ω) :
    Ξ.map f hf ω = (Ξ ω).map f := rfl

/-- Mapping marks before taking the law agrees with pushing the step law
forward through the deterministic mark map. -/
theorem Step.map_law
    {Ω ι X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y]
    (Ξ : Step Ω ι X) (P : Measure Ω) (f : X → Y) (hf : Measurable f) :
    (Ξ.map f hf).law P = (Ξ.law P).map (Combinatorics.Branching.Step.map f) := by
  unfold Step.law Step.map
  rw [Measure.map_map (measurable_stepMap f hf) Ξ.measurable_toStep]
  rfl

/-- Forget the spatial marks of a random step. This retains exactly its random
child-slot configuration. -/
def Step.forgetMarks {Ω ι X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] (Ξ : Step Ω ι X) : Step Ω ι PUnit.{1} :=
  Ξ.map (fun _ => PUnit.unit.{1}) measurable_const

@[simp] theorem Step.survive_forgetMarks_iff
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Step Ω ι X) (ω : Ω) (i : ι) :
    survive (Ξ.forgetMarks ω) i ↔ survive (Ξ ω) i := by
  exact survive_map_iff _ _ _

/-- The unmarked reproduction law underlying a random marked step. -/
noncomputable def Step.unmarkedLaw
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Step Ω ι X) (P : Measure Ω) :
    Measure (Combinatorics.Branching.Step ι PUnit.{1}) :=
  Ξ.forgetMarks.law P

instance Step.unmarkedLaw.isProbabilityMeasure
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Step Ω ι X) (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (Ξ.unmarkedLaw P) := by
  unfold Step.unmarkedLaw
  infer_instance

/-- The unmarked reproduction law is the deterministic forgetful image of the
marked step law. -/
theorem Step.unmarkedLaw_eq_map
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Ξ : Step Ω ι X) (P : Measure Ω) :
    Ξ.unmarkedLaw P =
      (Ξ.law P).map Combinatorics.Branching.Step.forgetMark := by
  exact Ξ.map_law P (fun _ => PUnit.unit.{1}) measurable_const

end ProbabilityTheory.BranchingRandomWalk
